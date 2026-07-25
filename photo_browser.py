#!/usr/bin/env python3
"""
Photo & Video Browser — a simple, non-destructive media organizer.

Scans one or more folders recursively, reads each photo's or video's
"date taken" (EXIF / video metadata, falling back to the file's modified
date), and serves a local web UI where you can browse your library filtered
by All / Year / Month / Week / Day, sorted newest- or oldest-first.

Your files are only ever read — except the Delete button, which (with your
confirmation) removes a file, sending it to the Recycle Bin when possible.

Usage:
    python photo_browser.py "C:/path/to/media"
    python photo_browser.py "C:/photos" "D:/videos" --port 8000
    python photo_browser.py "C:/photos" --debug      # list every folder scanned

Requires: Pillow            ->  pip install Pillow
Optional: pillow-heif       ->  pip install pillow-heif   (view iPhone/HEIC photos)
Optional: send2trash        ->  pip install send2trash    (delete to Recycle Bin)
Optional: ffmpeg on PATH    ->  enables real video thumbnails (still frames).
"""

import argparse
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import traceback
import webbrowser
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

try:
    from PIL import Image, ExifTags, ImageOps
except ImportError:
    sys.exit("Pillow is required. Install it with:  pip install Pillow")

APP_VERSION = "1.2"

# Optional: lets Pillow read iPhone/HEIC photos so they display + thumbnail.
try:
    import pillow_heif
    pillow_heif.register_heif_opener()
    HEIF_OK = True
    HEIF_ERR = None
except Exception as _e:
    HEIF_OK = False
    HEIF_ERR = repr(_e)

# Optional: decodes camera RAW files (Sony .ARW, Canon .CR2/CR3, Nikon .NEF, etc.)
try:
    import rawpy
    RAW_OK = True
    RAW_ERR = None
except Exception as _e:
    RAW_OK = False
    RAW_ERR = repr(_e)

# Optional: sends deleted files to the OS Recycle Bin/Trash (recoverable).
try:
    from send2trash import send2trash as _send2trash
except Exception:
    _send2trash = None

# Browser-native raster images (shown as-is if small enough):
WEB_IMG = {".jpg", ".jpeg", ".jpe", ".jfif", ".png", ".gif", ".webp", ".bmp", ".avif", ".ico"}
# Other still images Pillow can usually convert to a viewable preview:
OTHER_IMG = {".tif", ".tiff", ".heic", ".heif"}
# Camera RAW formats (indexed so they're counted; shown with a placeholder
# unless Pillow can decode them):
RAW_EXTS = {".dng", ".cr2", ".cr3", ".nef", ".nrw", ".arw", ".sr2", ".srf",
            ".raf", ".orf", ".rw2", ".pef", ".srw", ".x3f", ".raw", ".kdc",
            ".dcr", ".mrw", ".3fr", ".mef", ".iiq", ".rwl", ".erf", ".mos"}
IMAGE_EXTS = WEB_IMG | OTHER_IMG | RAW_EXTS

VIDEO_EXTS = {".mp4", ".mov", ".m4v", ".avi", ".mkv", ".webm", ".3gp", ".mts",
              ".m2ts", ".wmv", ".flv", ".mpg", ".mpeg", ".m2v", ".ts", ".mod"}
WEB_PLAYABLE = {".mp4", ".m4v", ".mov", ".webm", ".3gp"}

THUMB_SIZE = (400, 400)
PREVIEW_MAX = 2560
PREVIEW_QUALITY = 90

_DATETIME_ORIGINAL = 36867
_DATETIME = 306

THUMB_DIR = os.path.join(tempfile.gettempdir(), "photo_browser_thumbs")
os.makedirs(THUMB_DIR, exist_ok=True)

FFMPEG = shutil.which("ffmpeg")

PHOTOS = []
ID_TO_PATH = {}
SCAN = {"done": True, "seen": 0}   # "done" flips to False while a scan is running
_PLACEHOLDER_CACHE = None


# ---------------------------------------------------------------- date reading

def read_image_date(path):
    try:
        with Image.open(path) as img:
            exif = img.getexif()
            if exif:
                for tag in (_DATETIME_ORIGINAL, _DATETIME):
                    val = exif.get(tag)
                    if val:
                        try:
                            return datetime.strptime(str(val).strip(), "%Y:%m:%d %H:%M:%S")
                        except ValueError:
                            pass
                try:
                    sub = exif.get_ifd(0x8769)
                    for tag in (_DATETIME_ORIGINAL, _DATETIME):
                        val = sub.get(tag)
                        if val:
                            try:
                                return datetime.strptime(str(val).strip(), "%Y:%m:%d %H:%M:%S")
                            except ValueError:
                                pass
                except Exception:
                    pass
    except Exception:
        pass
    return None


def _read_atom_creation(f, end):
    """Walk MP4/MOV atoms to find moov->mvhd creation_time. Returns datetime or None."""
    while f.tell() + 8 <= end:
        pos = f.tell()
        hdr = f.read(8)
        if len(hdr) < 8:
            break
        size = int.from_bytes(hdr[0:4], "big")
        typ = hdr[4:8]
        header = 8
        if size == 1:
            ext = f.read(8)
            if len(ext) < 8:
                break
            size = int.from_bytes(ext, "big")
            header = 16
        elif size == 0:
            size = end - pos
        if size < header:
            break
        body_start = pos + header
        body_end = pos + size
        if typ == b"moov":
            f.seek(body_start)
            res = _read_atom_creation(f, min(body_end, end))
            if res:
                return res
        elif typ == b"mvhd":
            f.seek(body_start)
            ver = f.read(4)
            if len(ver) < 4:
                return None
            if ver[0] == 1:
                raw = f.read(8)
                secs = int.from_bytes(raw, "big") if len(raw) == 8 else 0
            else:
                raw = f.read(4)
                secs = int.from_bytes(raw, "big") if len(raw) == 4 else 0
            if secs:
                try:
                    dt = datetime(1904, 1, 1) + timedelta(seconds=secs)
                    if 1970 <= dt.year <= 2100:
                        return dt
                except (OverflowError, OSError):
                    return None
            return None
        f.seek(body_end)
    return None


def read_video_date(path):
    try:
        size = os.path.getsize(path)
        with open(path, "rb") as f:
            return _read_atom_creation(f, size)
    except Exception:
        return None


def read_taken_date(path, kind):
    dt = read_image_date(path) if kind == "image" else read_video_date(path)
    if dt is None:
        try:
            dt = datetime.fromtimestamp(os.path.getmtime(path))
        except Exception:
            dt = datetime.fromtimestamp(0)
    return dt


# ---------------------------------------------------------------- scanning

def scan(folders, debug=False):
    print("Scanning for photos and videos...")
    count = 0
    skipped = {}
    err_dirs = []
    folders_seen = 0
    seen_dirs = set()    # canonical dirs already walked (prevents symlink loops/dupes)
    seen_files = set()   # canonical files already indexed (prevents dupes)

    def _onerr(err):
        err_dirs.append(getattr(err, "filename", "?"))

    for root_folder in folders:
        for dirpath, _dirs, files in os.walk(root_folder, onerror=_onerr, followlinks=True):
            real_dir = os.path.realpath(dirpath)
            if real_dir in seen_dirs:
                _dirs[:] = []   # don't descend again (breaks symlink cycles)
                continue
            seen_dirs.add(real_dir)
            folders_seen += 1
            if debug:
                print(f"  [{len(files):>5} files]  {dirpath}")
            for fname in files:
                ext = os.path.splitext(fname)[1].lower()
                if ext in IMAGE_EXTS:
                    kind = "image"
                elif ext in VIDEO_EXTS:
                    kind = "video"
                else:
                    skipped[ext] = skipped.get(ext, 0) + 1
                    continue
                full = os.path.join(dirpath, fname)
                real_file = os.path.realpath(full)
                if real_file in seen_files:
                    continue
                seen_files.add(real_file)
                dt = read_taken_date(full, kind)
                pid = hashlib.md5(full.encode("utf-8", "surrogatepass")).hexdigest()
                PHOTOS.append({
                    "id": pid,
                    "name": fname,
                    "ts": dt.timestamp(),
                    "iso": dt.strftime("%Y-%m-%d %H:%M"),
                    "kind": kind,
                    "playable": ext in WEB_PLAYABLE,
                    "web": ext in WEB_IMG,
                    "raw": ext in RAW_EXTS,
                })
                ID_TO_PATH[pid] = full
                count += 1
                SCAN["seen"] = count
                if count % 200 == 0:
                    print(f"  ...{count:,} items", end="\r")

    PHOTOS.sort(key=lambda p: p["ts"])
    SCAN["seen"] = count
    imgs = sum(1 for p in PHOTOS if p["kind"] == "image")
    vids = count - imgs
    print(f"\nFound {imgs:,} photos and {vids:,} videos in {folders_seen:,} folder(s).")

    if err_dirs:
        print(f"!  {len(err_dirs)} folder(s) couldn't be opened (permissions, or cloud-only "
              f"files not downloaded). They were skipped:")
        for d in err_dirs[:6]:
            print(f"     - {d}")
        if len(err_dirs) > 6:
            print(f"     ...and {len(err_dirs) - 6} more")

    if skipped:
        total_sk = sum(skipped.values())
        top = sorted(skipped.items(), key=lambda kv: -kv[1])[:12]
        shown = ", ".join(f"{(k or '(no extension)')} x{v:,}" for k, v in top)
        print(f"Ignored {total_sk:,} non-photo/video file(s) by type: {shown}")
        print("   (If a photo/video type you use is listed here, tell me and I'll add it.)")

    heic = sum(1 for p in PHOTOS
               if os.path.splitext(p["name"])[1].lower() in (".heic", ".heif"))
    if heic and not HEIF_OK:
        print(f"i  {heic:,} HEIC/HEIF photos found. To view them, install pillow-heif:  "
              f"pip install pillow-heif")
    raws = sum(1 for p in PHOTOS if os.path.splitext(p["name"])[1].lower() in RAW_EXTS)
    if raws:
        print(f"i  {raws:,} camera RAW files — showing their embedded previews (built in, no add-on needed).")
    if vids and not FFMPEG:
        print("i  ffmpeg not found — videos play, but show a placeholder thumbnail.")


# ---------------------------------------------------------------- thumbnails

def placeholder_thumb(kind="image"):
    global _PLACEHOLDER_CACHE
    if _PLACEHOLDER_CACHE is not None:
        return _PLACEHOLDER_CACHE
    img = Image.new("RGB", (400, 400), (24, 26, 33))
    try:
        from PIL import ImageDraw
        d = ImageDraw.Draw(img)
        d.polygon([(168, 150), (168, 250), (258, 200)], fill=(120, 130, 150))
    except Exception:
        pass
    buf = io.BytesIO()
    img.save(buf, format="JPEG", quality=80)
    _PLACEHOLDER_CACHE = buf.getvalue()
    return _PLACEHOLDER_CACHE


def _cache_path(pid, mtime, suffix):
    return os.path.join(THUMB_DIR, f"{pid}_{mtime}{suffix}.jpg")


def _largest_embedded_jpeg(path):
    """Find the largest embedded JPEG inside a RAW file (pure Python, no deps).
    Camera RAWs (Sony .ARW, etc.) carry a full-size JPEG preview — we extract it."""
    import mmap
    try:
        with open(path, "rb") as f:
            mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
            try:
                cands = []
                start = 0
                while True:
                    i = mm.find(b"\xff\xd8\xff", start)
                    if i < 0:
                        break
                    j = mm.find(b"\xff\xd9", i + 3)
                    if j < 0:
                        break
                    cands.append((j + 2 - i, i, j + 2))
                    start = j + 2
                    if len(cands) > 96:
                        break
                cands.sort(reverse=True)  # largest first
                for _ln, i, end in cands[:6]:
                    seg = mm[i:end]
                    try:
                        im = Image.open(io.BytesIO(seg))
                        im.load()
                        return seg
                    except Exception:
                        continue
            finally:
                mm.close()
    except Exception:
        return None
    return None


def raw_jpeg_bytes(path, max_dim, quality):
    """Return a JPEG for a RAW file. Uses the embedded preview (no dependencies);
    falls back to rawpy only if that fails and rawpy happens to be available."""
    im = None
    seg = _largest_embedded_jpeg(path)
    if seg is not None:
        try:
            im = Image.open(io.BytesIO(seg))
            im.draft("RGB", (max_dim, max_dim))
        except Exception:
            im = None
    if im is None and RAW_OK:
        try:
            with rawpy.imread(path) as raw:
                im = Image.fromarray(raw.postprocess(use_camera_wb=True, half_size=True))
        except Exception:
            im = None
    if im is None:
        return None
    im = ImageOps.exif_transpose(im).convert("RGB")
    if max(im.size) > max_dim:
        im.thumbnail((max_dim, max_dim))
    buf = io.BytesIO()
    im.save(buf, format="JPEG", quality=quality)
    return buf.getvalue()


def make_image_thumb(path, pid):
    try:
        mtime = int(os.path.getmtime(path))
    except OSError:
        mtime = 0
    cache_file = _cache_path(pid, mtime, "")
    if os.path.exists(cache_file):
        with open(cache_file, "rb") as f:
            return f.read()
    ext = os.path.splitext(path)[1].lower()
    try:
        if ext in RAW_EXTS:
            data = raw_jpeg_bytes(path, max(THUMB_SIZE), 82)
            if not data:
                return None
        else:
            with Image.open(path) as img:
                img.draft("RGB", THUMB_SIZE)          # fast JPEG downscale-on-decode
                img = ImageOps.exif_transpose(img)    # honor camera rotation
                img = img.convert("RGB")
                img.thumbnail(THUMB_SIZE)
                buf = io.BytesIO()
                img.save(buf, format="JPEG", quality=82)
                data = buf.getvalue()
        with open(cache_file, "wb") as f:
            f.write(data)
        return data
    except Exception:
        return None


def make_preview(path, pid):
    """A browser-friendly, downscaled JPEG for the full-screen viewer.
    Handles huge originals (fast) and non-web formats like HEIC (converted)."""
    try:
        mtime = int(os.path.getmtime(path))
    except OSError:
        mtime = 0
    cache_file = _cache_path(pid, mtime, "_pv")
    if os.path.exists(cache_file):
        with open(cache_file, "rb") as f:
            return f.read()
    ext = os.path.splitext(path)[1].lower()
    try:
        if ext in RAW_EXTS:
            data = raw_jpeg_bytes(path, PREVIEW_MAX, PREVIEW_QUALITY)
            if not data:
                return None
        else:
            with Image.open(path) as img:
                img.draft("RGB", (PREVIEW_MAX, PREVIEW_MAX))
                img = ImageOps.exif_transpose(img)
                img = img.convert("RGB")
                if max(img.size) > PREVIEW_MAX:
                    img.thumbnail((PREVIEW_MAX, PREVIEW_MAX))
                buf = io.BytesIO()
                img.save(buf, format="JPEG", quality=PREVIEW_QUALITY)
                data = buf.getvalue()
        with open(cache_file, "wb") as f:
            f.write(data)
        return data
    except Exception:
        return None


def make_video_thumb(path, pid):
    if not FFMPEG:
        return placeholder_thumb()
    try:
        mtime = int(os.path.getmtime(path))
    except OSError:
        mtime = 0
    cache_file = _cache_path(pid, mtime, "_v")
    if os.path.exists(cache_file):
        with open(cache_file, "rb") as f:
            return f.read()
    try:
        subprocess.run(
            [FFMPEG, "-y", "-loglevel", "error", "-ss", "1", "-i", path,
             "-frames:v", "1", "-vf", "scale=400:-2", cache_file],
            timeout=30, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        if os.path.exists(cache_file) and os.path.getsize(cache_file) > 0:
            with open(cache_file, "rb") as f:
                return f.read()
    except Exception:
        pass
    return placeholder_thumb()


_PREWARM_STARTED = False


def prewarm_thumbnails():
    """Generate thumbnails in the background so scrolling is instant.
    Newest photos first (that's what you see on launch)."""
    global _PREWARM_STARTED
    if _PREWARM_STARTED:
        return
    _PREWARM_STARTED = True

    def worker():
        from concurrent.futures import ThreadPoolExecutor
        items = list(reversed(PHOTOS))  # newest first

        def gen(p):
            fp = ID_TO_PATH.get(p["id"])
            if not fp:
                return
            try:
                if p["kind"] == "video":
                    make_video_thumb(fp, p["id"])
                else:
                    make_image_thumb(fp, p["id"])
            except Exception:
                pass

        workers = max(2, min(8, (os.cpu_count() or 4)))
        try:
            with ThreadPoolExecutor(max_workers=workers) as ex:
                list(ex.map(gen, items))
        except Exception:
            pass

    t = threading.Thread(target=worker, daemon=True)
    t.start()


# ---------------------------------------------------------------- HTML

INDEX_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Photos</title>
<style>
  :root{
    --bg:#0b0d12; --bg2:#0f1218; --surface:#151922; --surface2:#1b202b;
    --line:#242a36; --text:#eef1f6; --muted:#8b93a3; --muted2:#666e7e;
    --accent:#7c5cff; --accent2:#4f8cff; --shadow:0 8px 30px rgba(0,0,0,.45);
    --hdr-h:66px;
  }
  *{box-sizing:border-box;}
  html,body{height:100%;}
  body{margin:0;background:
        radial-gradient(1200px 600px at 80% -10%, rgba(124,92,255,.10), transparent 60%),
        radial-gradient(900px 500px at -10% 0%, rgba(79,140,255,.08), transparent 55%),
        var(--bg);
       color:var(--text);
       font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;
       -webkit-font-smoothing:antialiased;}
  ::-webkit-scrollbar{width:11px;height:11px;}
  ::-webkit-scrollbar-thumb{background:#2b3140;border-radius:8px;border:2px solid transparent;background-clip:content-box;}
  ::-webkit-scrollbar-thumb:hover{background:#3a4152;background-clip:content-box;}

  header{position:sticky;top:0;z-index:20;height:var(--hdr-h);
         display:flex;align-items:center;gap:18px;padding:0 22px;
         background:rgba(11,13,18,.72);backdrop-filter:blur(18px) saturate(160%);
         border-bottom:1px solid var(--line);}
  .brand{display:flex;align-items:baseline;gap:12px;min-width:0;}
  .brand h1{font-size:19px;margin:0;font-weight:700;letter-spacing:-.3px;
            background:linear-gradient(90deg,#fff,#c7cbd6);-webkit-background-clip:text;
            background-clip:text;-webkit-text-fill-color:transparent;}
  .brand .sub{font-size:12.5px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;}
  .spacer{flex:1;}
  .segment{display:flex;gap:2px;padding:4px;background:var(--surface);
           border:1px solid var(--line);border-radius:12px;}
  .seg{appearance:none;border:0;background:transparent;color:var(--muted);
       font-size:13px;font-weight:600;padding:7px 14px;border-radius:9px;cursor:pointer;
       transition:.18s;white-space:nowrap;}
  .seg:hover{color:var(--text);}
  .seg.active{color:#fff;background:linear-gradient(135deg,var(--accent),var(--accent2));
              box-shadow:0 4px 14px rgba(124,92,255,.35);}
  .sortbtn{display:flex;align-items:center;gap:8px;cursor:pointer;
           background:var(--surface);border:1px solid var(--line);border-radius:11px;
           color:var(--text);font-size:13px;font-weight:600;padding:9px 14px;transition:.18s;}
  .sortbtn:hover{border-color:#333b4b;background:var(--surface2);}
  .sortbtn svg{width:15px;height:15px;fill:none;stroke:currentColor;stroke-width:2;
               stroke-linecap:round;stroke-linejoin:round;transition:transform .25s;}
  .sortbtn.oldest svg{transform:rotate(180deg);}

  .layout{display:flex;height:calc(100vh - var(--hdr-h));}
  aside{width:210px;min-width:210px;overflow-y:auto;padding:14px 10px;
        border-right:1px solid var(--line);background:var(--bg2);}
  .rail-title{font-size:11px;letter-spacing:.14em;text-transform:uppercase;
              color:var(--muted2);font-weight:700;padding:6px 12px 10px;}
  .rail-item{display:flex;justify-content:space-between;align-items:center;gap:8px;
             padding:9px 12px;border-radius:10px;cursor:pointer;font-size:13.5px;
             color:var(--muted);transition:.14s;}
  .rail-item:hover{background:var(--surface);color:var(--text);}
  .rail-item.active{background:linear-gradient(135deg,rgba(124,92,255,.22),rgba(79,140,255,.14));
                    color:#fff;font-weight:600;}
  .rail-item .c{font-size:11.5px;color:var(--muted2);font-variant-numeric:tabular-nums;}
  .rail-item.active .c{color:#c8ccff;}

  main{flex:1;overflow-y:auto;padding:0 22px 60px;scroll-behavior:smooth;}
  .section{scroll-margin-top:80px;}
  .shead{position:sticky;top:0;z-index:8;display:flex;align-items:baseline;gap:12px;
         padding:22px 4px 12px;background:linear-gradient(180deg,var(--bg) 55%,transparent);}
  .shead .big{font-size:19px;font-weight:700;letter-spacing:-.3px;}
  .shead .small{font-size:12.5px;color:var(--muted);}

  .grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(168px,1fr));gap:12px;}
  .cell{position:relative;aspect-ratio:1/1;border-radius:14px;overflow:hidden;
        cursor:pointer;background:var(--surface);
        box-shadow:0 1px 2px rgba(0,0,0,.4);transition:transform .18s, box-shadow .18s;}
  .cell:hover{transform:translateY(-3px);box-shadow:var(--shadow);}
  .cell img{width:100%;height:100%;object-fit:cover;display:block;transition:transform .35s ease;}
  .cell:hover img{transform:scale(1.06);}
  .cell::after{content:"";position:absolute;inset:0;border-radius:14px;
               box-shadow:inset 0 0 0 1px rgba(255,255,255,.05);pointer-events:none;}
  .cap{position:absolute;left:0;right:0;bottom:0;padding:16px 10px 7px;font-size:11px;
       color:#f2f4f8;background:linear-gradient(transparent,rgba(0,0,0,.72));
       opacity:0;transition:.18s;font-variant-numeric:tabular-nums;}
  .cell:hover .cap{opacity:1;}
  .badge{position:absolute;top:8px;right:8px;height:26px;padding:0 8px;border-radius:20px;
         background:rgba(10,12,16,.62);backdrop-filter:blur(6px);display:flex;align-items:center;
         gap:5px;color:#fff;font-size:11px;font-weight:600;}
  .badge svg{width:11px;height:11px;fill:#fff;}
  .empty{color:var(--muted);padding:60px;text-align:center;}

  /* selection */
  .sortbtn.active{background:linear-gradient(135deg,var(--accent),var(--accent2));color:#fff;border-color:transparent;}
  .check{position:absolute;top:8px;left:8px;width:24px;height:24px;border-radius:50%;
         border:2px solid rgba(255,255,255,.85);background:rgba(10,12,16,.35);display:none;
         align-items:center;justify-content:center;z-index:3;}
  body.selectmode .check{display:flex;}
  body.selectmode .cell{cursor:pointer;}
  body.selectmode .cell:hover{transform:none;}
  .cell.sel .check{background:var(--accent);border-color:#fff;}
  .cell.sel .check::after{content:"";width:6px;height:11px;border:solid #fff;border-width:0 2px 2px 0;
         transform:rotate(45deg);margin-top:-2px;}
  .cell.sel{outline:3px solid var(--accent);outline-offset:-3px;}
  .cell.sel img{transform:scale(.92);}

  #selbar{position:fixed;left:50%;bottom:22px;transform:translateX(-50%);z-index:40;display:none;
          align-items:center;gap:16px;padding:10px 12px 10px 20px;border-radius:16px;
          background:rgba(21,25,34,.96);backdrop-filter:blur(12px);border:1px solid var(--line);
          box-shadow:var(--shadow);}
  #selbar #selcount{font-size:13.5px;font-weight:600;}
  .sb-actions{display:flex;gap:8px;}
  .sb-btn{border:1px solid var(--line);background:var(--surface2);color:var(--text);
          font-size:13px;font-weight:600;padding:8px 14px;border-radius:10px;cursor:pointer;transition:.15s;}
  .sb-btn:hover{background:#232a37;}
  .sb-btn.danger{background:linear-gradient(135deg,#ff5c6c,#ff7a45);border-color:transparent;color:#fff;}
  .sb-btn.danger:hover{filter:brightness(1.08);}

  #ctx{position:fixed;z-index:70;display:none;min-width:160px;padding:6px;border-radius:12px;
       background:rgba(24,28,38,.98);backdrop-filter:blur(12px);border:1px solid var(--line);
       box-shadow:var(--shadow);}
  #ctx .ci{padding:9px 12px;border-radius:8px;font-size:13.5px;cursor:pointer;color:var(--text);}
  #ctx .ci:hover{background:var(--surface2);}
  #ctx .ci.danger{color:#ff6b78;}
  #ctx .ci.danger:hover{background:rgba(255,86,86,.16);}

  /* lightbox */
  #lb{position:fixed;inset:0;z-index:60;display:none;align-items:center;justify-content:center;
      background:rgba(6,7,10,.86);backdrop-filter:blur(10px);}
  #lb.open{display:flex;animation:fade .18s ease;}
  @keyframes fade{from{opacity:0}to{opacity:1}}
  #lbcontent{position:relative;max-width:94vw;max-height:86vh;min-width:120px;min-height:120px;
             display:flex;align-items:center;justify-content:center;}
  #lbcontent img,#lbcontent video{max-width:94vw;max-height:86vh;border-radius:12px;
       box-shadow:0 20px 70px rgba(0,0,0,.6);display:block;}
  .spinner{width:44px;height:44px;border-radius:50%;border:3px solid rgba(255,255,255,.18);
           border-top-color:#fff;animation:spin .8s linear infinite;}
  @keyframes spin{to{transform:rotate(360deg)}}
  .lberr{color:#cfd3da;text-align:center;padding:30px;font-size:14px;}
  .lbbar{position:fixed;top:0;left:0;right:0;height:64px;display:flex;align-items:center;
         justify-content:space-between;padding:0 20px;z-index:2;
         background:linear-gradient(180deg,rgba(0,0,0,.55),transparent);}
  .lbbar .info{font-size:13.5px;color:#e7eaf0;}
  .lbbar .info b{font-weight:600;} .lbbar .info span{color:#9aa1ad;margin-left:8px;}
  .iconbtn{width:40px;height:40px;border-radius:50%;border:0;cursor:pointer;
           background:rgba(255,255,255,.10);color:#fff;display:flex;align-items:center;
           justify-content:center;transition:.15s;}
  .iconbtn:hover{background:rgba(255,255,255,.20);}
  .iconbtn.danger:hover{background:rgba(255,86,86,.28);}
  .iconbtn svg{width:20px;height:20px;fill:none;stroke:#fff;stroke-width:2.2;stroke-linecap:round;stroke-linejoin:round;}
  .lbactions{display:flex;gap:10px;}
  .lbnav{position:fixed;top:50%;transform:translateY(-50%);z-index:2;}
  .lbnav.prev{left:18px;} .lbnav.next{right:18px;}
  @media (max-width:640px){ aside{display:none;} }
</style>
</head>
<body>
<header>
  <div class="brand"><h1>Photos</h1><span class="sub" id="sub">Loading…</span></div>
  <div class="spacer"></div>
  <div class="segment" id="tabs">
    <button class="seg active" data-g="all">All</button>
    <button class="seg" data-g="year">Year</button>
    <button class="seg" data-g="month">Month</button>
    <button class="seg" data-g="week">Week</button>
    <button class="seg" data-g="day">Day</button>
  </div>
  <button class="sortbtn" id="sortbtn" title="Toggle sort order">
    <svg viewBox="0 0 24 24"><path d="M12 4v16M12 4l-5 5M12 4l5 5"/></svg>
    <span id="sortlabel">Newest</span>
  </button>
  <button class="sortbtn" id="selectbtn" title="Select multiple to delete">
    <svg viewBox="0 0 24 24"><path d="M9 11l3 3 8-8M20 12v6a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2h9"/></svg>
    <span>Select</span>
  </button>
  <button class="sortbtn" id="pickbtn" style="display:none" title="Choose a different folder">
    <svg viewBox="0 0 24 24"><path d="M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"/></svg>
    <span>Folder</span>
  </button>
</header>

<div class="layout">
  <aside id="rail"></aside>
  <main id="main"><div class="empty">Loading your library…</div></main>
</div>

<div id="lb">
  <div class="lbbar">
    <div class="info" id="lbinfo"></div>
    <div class="lbactions">
      <button class="iconbtn danger" onclick="del()" title="Delete (Del)"><svg viewBox="0 0 24 24"><path d="M4 7h16M9 7V4h6v3M10 11v6M14 11v6M6 7l1 13h10l1-13"/></svg></button>
      <button class="iconbtn" onclick="closeLb()" title="Close (Esc)"><svg viewBox="0 0 24 24"><path d="M6 6l12 12M18 6L6 18"/></svg></button>
    </div>
  </div>
  <button class="iconbtn lbnav prev" onclick="step(-1)"><svg viewBox="0 0 24 24"><path d="M15 6l-6 6 6 6"/></svg></button>
  <div id="lbcontent"></div>
  <button class="iconbtn lbnav next" onclick="step(1)"><svg viewBox="0 0 24 24"><path d="M9 6l6 6-6 6"/></svg></button>
</div>

<div id="ctx">
  <div class="ci" onclick="ctxOpen()">Open</div>
  <div class="ci" onclick="ctxSelect()">Select</div>
  <div class="ci danger" onclick="ctxDelete()">Delete</div>
</div>

<div id="selbar">
  <span id="selcount">0 selected</span>
  <div class="sb-actions">
    <button class="sb-btn" onclick="selectAllVisible()">Select all shown</button>
    <button class="sb-btn" onclick="clearSelection()">Clear</button>
    <button class="sb-btn danger" onclick="deleteSelected()">Delete</button>
    <button class="sb-btn" onclick="setSelectMode(false)">Done</button>
  </div>
</div>

<script>
let PHOTOS=[];
let CAN_RECYCLE=false;
let rawSupport=false;
let appVersion="";
let selectMode=false;
const selected=new Set();
const state={g:"all",sort:"newest",period:null};
let viewList=[];
let lbIndex=0;
let monthObserver=null;
const pad=n=>String(n).padStart(2,'0');
const main=document.getElementById('main');
const PLAY='<svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>';

function keyFor(d,g){
  const y=d.getFullYear();
  if(g==="year")  return {key:String(y),label:String(y),small:""};
  if(g==="month") return {key:`${y}-${pad(d.getMonth()+1)}`,
                          label:d.toLocaleDateString(undefined,{month:'long'}),small:String(y)};
  if(g==="week"){
    const day=(d.getDay()+6)%7;
    const mon=new Date(d);mon.setDate(d.getDate()-day);mon.setHours(0,0,0,0);
    const sun=new Date(mon);sun.setDate(mon.getDate()+6);
    return {key:`${mon.getFullYear()}-${pad(mon.getMonth()+1)}-${pad(mon.getDate())}`,
            label:`${mon.toLocaleDateString(undefined,{month:'short',day:'numeric'})} – ${sun.toLocaleDateString(undefined,{month:'short',day:'numeric'})}`,
            small:String(sun.getFullYear())};
  }
  return {key:`${y}-${pad(d.getMonth()+1)}-${pad(d.getDate())}`,
          label:d.toLocaleDateString(undefined,{weekday:'long',month:'long',day:'numeric',year:'numeric'}),
          small:String(y)};
}

function groupBy(g){
  const map=new Map();
  for(const p of PHOTOS){
    const d=new Date(p.ts*1000);
    const {key,label,small}=keyFor(d,g);
    if(!map.has(key)) map.set(key,{key,label,small,items:[]});
    map.get(key).items.push(p);
  }
  const dir=state.sort==="newest"?-1:1;
  const groups=[...map.values()].sort((a,b)=>a.key<b.key?-dir:(a.key>b.key?dir:0));
  for(const grp of groups) grp.items.sort((x,y)=>(x.ts-y.ts)*dir);
  return groups;
}

function cellHTML(p){
  const badge=p.kind==="video"?`<div class="badge">${PLAY}</div>`:"";
  return `<div class="cell" data-idx="__IDX__" data-id="${p.id}"><img loading="lazy" src="/thumb?id=${p.id}" alt="">${badge}<div class="cap">${p.iso}</div><div class="check"></div></div>`;
}
function gridHTML(items,offset){
  let h='<div class="grid">';
  items.forEach((p,i)=>{ h+=cellHTML(p).replace('__IDX__',offset+i); });
  return h+'</div>';
}

function render(){ (state.g==="all"||state.g==="day") ? renderTimeline() : renderPeriods(); }

function renderTimeline(){
  const groups=groupBy("day");
  if(!groups.length){ main.innerHTML='<div class="empty">No photos or videos found.</div>'; return; }
  viewList=[]; let html="", lastMonth=null; const railMonths=[];
  for(const g of groups){
    const offset=viewList.length; viewList.push(...g.items);
    const mk=g.key.slice(0,7); let anchor="";
    if(mk!==lastMonth){
      lastMonth=mk;
      const d=new Date(g.items[0].ts*1000);
      const mlabel=d.toLocaleDateString(undefined,{month:'long',year:'numeric'});
      railMonths.push({mk,mlabel});
      anchor=`<div class="manchor" data-mk="${mk}" id="m-${mk}"></div>`;
    }
    html+=`${anchor}<section class="section">
      <div class="shead"><span class="big">${g.label}</span><span class="small">${g.items.length} item${g.items.length!==1?'s':''}</span></div>
      ${gridHTML(g.items,offset)}</section>`;
  }
  main.innerHTML=html; main.scrollTop=0; bindCells();
  const rail=document.getElementById('rail');
  rail.innerHTML=`<div class="rail-title">Jump to</div>`+railMonths.map(m=>
    `<div class="rail-item" data-mk="${m.mk}"><span>${m.mlabel}</span></div>`).join('');
  rail.querySelectorAll('.rail-item').forEach(el=>{
    el.onclick=()=>{ const t=document.getElementById('m-'+el.dataset.mk); if(t) t.scrollIntoView({behavior:'smooth',block:'start'}); };
  });
  observeMonths();
}
function observeMonths(){
  if(monthObserver) monthObserver.disconnect();
  monthObserver=new IntersectionObserver(entries=>{
    entries.forEach(e=>{ if(e.isIntersecting) setRailActive(e.target.dataset.mk); });
  },{root:main,rootMargin:"-8% 0px -88% 0px",threshold:0});
  document.querySelectorAll('.manchor').forEach(a=>monthObserver.observe(a));
}
function setRailActive(mk){
  document.querySelectorAll('#rail .rail-item').forEach(el=>el.classList.toggle('active',el.dataset.mk===mk));
}

function renderPeriods(){
  if(monthObserver) monthObserver.disconnect();
  const groups=groupBy(state.g);
  if(!groups.length){ main.innerHTML='<div class="empty">Nothing found.</div>'; return; }
  if(!state.period||!groups.find(g=>g.key===state.period)) state.period=groups[0].key;
  const rail=document.getElementById('rail');
  const title={year:"Years",month:"Months",week:"Weeks"}[state.g]||"Periods";
  rail.innerHTML=`<div class="rail-title">${title}</div>`+groups.map(g=>
    `<div class="rail-item ${g.key===state.period?'active':''}" data-k="${g.key}">
       <span>${g.label}${g.small?` <span style="color:var(--muted2)">${g.small}</span>`:''}</span>
       <span class="c">${g.items.length}</span></div>`).join('');
  rail.querySelectorAll('.rail-item').forEach(el=>{ el.onclick=()=>{ state.period=el.dataset.k; renderPeriods(); }; });
  const sel=groups.find(g=>g.key===state.period);
  viewList=sel.items.slice();
  main.innerHTML=`<section class="section">
    <div class="shead"><span class="big">${sel.label}</span>
      <span class="small">${sel.small?sel.small+' · ':''}${sel.items.length} item${sel.items.length!==1?'s':''}</span></div>
    ${gridHTML(sel.items,0)}</section>`;
  main.scrollTop=0; bindCells();
}
function bindCells(){
  main.querySelectorAll('.cell').forEach(c=>{
    c.onclick=()=>{ if(selectMode) toggleSelect(c.dataset.id,c); else openLb(parseInt(c.dataset.idx,10)); };
    c.oncontextmenu=(e)=>{ e.preventDefault(); showCtx(e.clientX,e.clientY,parseInt(c.dataset.idx,10),c.dataset.id); };
  });
  applySelectionClasses();
}

// ---- multi-select ----
function setSelectMode(on){
  selectMode=on;
  if(!on) selected.clear();
  document.getElementById('selectbtn').classList.toggle('active',on);
  applySelectionClasses();
}
function toggleSelect(id,el){
  if(selected.has(id)){ selected.delete(id); el&&el.classList.remove('sel'); }
  else { selected.add(id); el&&el.classList.add('sel'); }
  updateSelBar();
}
function applySelectionClasses(){
  document.body.classList.toggle('selectmode',selectMode);
  main.querySelectorAll('.cell').forEach(c=>c.classList.toggle('sel',selected.has(c.dataset.id)));
  updateSelBar();
}
function updateSelBar(){
  const bar=document.getElementById('selbar');
  if(selectMode && selected.size>0){ bar.style.display='flex'; document.getElementById('selcount').textContent=`${selected.size} selected`; }
  else bar.style.display='none';
}
function clearSelection(){ selected.clear(); applySelectionClasses(); }
function selectAllVisible(){ viewList.forEach(p=>selected.add(p.id)); applySelectionClasses(); }
async function deleteSelected(){
  if(!selected.size) return;
  const ids=[...selected];
  const msg=CAN_RECYCLE
    ? `Move ${ids.length} item${ids.length!==1?'s':''} to the Recycle Bin?`
    : `Permanently delete ${ids.length} item${ids.length!==1?'s':''}?\nThis cannot be undone.`;
  if(!window.confirm(msg)) return;
  let j;
  try{ const r=await fetch('/delete_many?ids='+encodeURIComponent(ids.join(',')),{method:'POST'}); j=await r.json(); }
  catch(e){ alert('Delete failed: '+e); return; }
  if(!j||!j.ok){ alert('Delete failed.'); return; }
  const gone=new Set(ids);
  PHOTOS=PHOTOS.filter(p=>!gone.has(p.id));
  selected.clear();
  refreshSub();
  const sc=main.scrollTop; render(); main.scrollTop=sc;
  updateSelBar();
}

// ---- right-click context menu ----
function showCtx(x,y,idx,id){
  const m=document.getElementById('ctx');
  m.dataset.idx=idx; m.dataset.id=id;
  m.style.display='block';
  m.style.left=Math.min(x,window.innerWidth-m.offsetWidth-8)+'px';
  m.style.top=Math.min(y,window.innerHeight-m.offsetHeight-8)+'px';
}
function hideCtx(){ document.getElementById('ctx').style.display='none'; }
function ctxOpen(){ const i=parseInt(document.getElementById('ctx').dataset.idx,10); hideCtx(); openLb(i); }
function ctxSelect(){ const id=document.getElementById('ctx').dataset.id; hideCtx(); setSelectMode(true); selected.add(id); applySelectionClasses(); }
function ctxDelete(){ const id=document.getElementById('ctx').dataset.id; hideCtx(); delById(id); }
document.addEventListener('click',hideCtx);
document.addEventListener('scroll',hideCtx,true);

async function delById(id){
  const p=PHOTOS.find(x=>x.id===id); if(!p) return;
  const msg=CAN_RECYCLE
    ? `Move this ${p.kind} to the Recycle Bin?\n\n${p.name}`
    : `Permanently delete this ${p.kind}?\n\n${p.name}\n\nThis cannot be undone.`;
  if(!window.confirm(msg)) return;
  let j;
  try{ const r=await fetch('/delete?id='+encodeURIComponent(id),{method:'POST'}); j=await r.json(); }
  catch(e){ alert('Delete failed: '+e); return; }
  if(!j||!j.ok){ alert('Delete failed: '+((j&&j.error)||'unknown')); return; }
  PHOTOS=PHOTOS.filter(x=>x.id!==id); selected.delete(id);
  refreshSub();
  const sc=main.scrollTop; render(); main.scrollTop=sc;
}

// lightbox — images load a downscaled preview (fast, and converts HEIC etc.)
function openLb(i){
  lbIndex=i; const p=viewList[i]; const box=document.getElementById('lbcontent');
  if(p.kind==="video"){
    box.innerHTML=p.playable
      ? `<video src="/full?id=${p.id}" controls autoplay playsinline></video>`
      : `<div class="lberr"><div style="font-size:46px">🎬</div><p><b>${p.name}</b></p>
           <p style="color:#9aa1ad">This video format can't play in the browser.<br>Open it from your folder.</p></div>`;
  } else {
    box.innerHTML=`<div class="spinner"></div>`;
    const show=(image)=>{ if(viewList[lbIndex]===p){ box.innerHTML=''; box.appendChild(image); } };
    // 1) show a fast preview immediately
    const fast=new Image();
    fast.onload=()=>{
      show(fast);
      // 2) then sharpen to the full-resolution original (for browser-native formats)
      if(p.web){ const full=new Image(); full.onload=()=>show(full); full.src=`/full?id=${p.id}`; }
    };
    fast.onerror=()=>{ if(viewList[lbIndex]!==p) return;
      let hint="If it's an iPhone HEIC file, install pillow-heif (see README).";
      if(p.raw) hint="This RAW file has no usable embedded preview to display.";
      box.innerHTML=`<div class="lberr">Couldn't display <b>${p.name}</b>.<br><span style="color:#9aa1ad">${hint}</span></div>`; };
    fast.src=`/preview?id=${p.id}`;
  }
  document.getElementById('lbinfo').innerHTML=`<b>${p.name}</b><span>${p.iso}${p.kind==='video'?' · Video':''}</span>`;
  document.getElementById('lb').classList.add('open');
}
function closeLb(){ document.getElementById('lbcontent').innerHTML=""; document.getElementById('lb').classList.remove('open'); }
function step(d){ if(!viewList.length) return; lbIndex=(lbIndex+d+viewList.length)%viewList.length; openLb(lbIndex); }

async function del(){
  const p=viewList[lbIndex]; if(!p) return;
  const what=p.kind==="video"?"video":"photo";
  const msg=CAN_RECYCLE
    ? `Move this ${what} to the Recycle Bin?\n\n${p.name}\n\nYou can restore it from the Recycle Bin if needed.`
    : `Permanently delete this ${what}?\n\n${p.name}\n\nThis cannot be undone.`;
  if(!window.confirm(msg)) return;
  let j;
  try{ const r=await fetch('/delete?id='+encodeURIComponent(p.id),{method:'POST'}); j=await r.json(); }
  catch(e){ alert('Delete failed: '+e); return; }
  if(!j||!j.ok){ alert('Delete failed: '+((j&&j.error)||'unknown error')); return; }
  const neighbor=(viewList[lbIndex+1]||viewList[lbIndex-1]||{}).id;
  PHOTOS=PHOTOS.filter(x=>x.id!==p.id);
  refreshSub();
  const sc=main.scrollTop; render(); main.scrollTop=sc;
  if(neighbor){ const ni=viewList.findIndex(x=>x.id===neighbor); if(ni>=0){ openLb(ni); return; } }
  closeLb();
}

function refreshSub(){
  const imgs=PHOTOS.filter(p=>p.kind==='image').length;
  const vids=PHOTOS.length-imgs;
  let rng='';
  if(PHOTOS.length){
    const ts=PHOTOS.map(p=>p.ts);
    const f=t=>new Date(t*1000).toLocaleDateString(undefined,{month:'short',year:'numeric'});
    rng=` · ${f(Math.min(...ts))} – ${f(Math.max(...ts))}`;
  }
  const scan = scanning ? ` · scanning… (${(scanSeen||PHOTOS.length).toLocaleString()} found)` : '';
  const ver = appVersion ? ` · v${appVersion}` : '';
  document.getElementById('sub').textContent=`${imgs.toLocaleString()} photos · ${vids.toLocaleString()} videos${rng}${scan}${ver}`;
}

document.addEventListener('keydown',e=>{
  if(!document.getElementById('lb').classList.contains('open')) return;
  if(e.key==="Escape") closeLb();
  else if(e.key==="ArrowLeft") step(-1);
  else if(e.key==="ArrowRight") step(1);
  else if(e.key==="Delete"||e.key==="Backspace"){ e.preventDefault(); del(); }
});
document.getElementById('lb').addEventListener('click',e=>{ if(e.target.id==='lb') closeLb(); });

document.getElementById('tabs').addEventListener('click',e=>{
  const t=e.target.closest('.seg'); if(!t) return;
  document.querySelectorAll('.seg').forEach(x=>x.classList.remove('active'));
  t.classList.add('active'); state.g=t.dataset.g; state.period=null; render();
});
const sortBtn=document.getElementById('sortbtn');
sortBtn.addEventListener('click',()=>{
  state.sort=state.sort==="newest"?"oldest":"newest";
  sortBtn.classList.toggle('oldest',state.sort==="oldest");
  document.getElementById('sortlabel').textContent=state.sort==="newest"?"Newest":"Oldest";
  render();
});
document.getElementById('selectbtn').addEventListener('click',()=>setSelectMode(!selectMode));
document.addEventListener('keydown',e=>{
  if(document.getElementById('lb').classList.contains('open')) return;
  if(e.key==="Escape"){
    if(document.getElementById('ctx').style.display==='block') hideCtx();
    else if(selectMode) setSelectMode(false);
  }
});

// "Change folder" — only shown when running as the native app (pywebview present)
const pickBtn=document.getElementById('pickbtn');
function enablePick(){
  if(window.pywebview&&window.pywebview.api&&window.pywebview.api.pick_folder){
    pickBtn.style.display='flex';
  }
}
window.addEventListener('pywebviewready',enablePick); enablePick();
pickBtn.addEventListener('click',async()=>{
  try{ const r=await window.pywebview.api.pick_folder(); if(r&&r.ok) location.reload(); }
  catch(e){ /* ignore */ }
});

let scanning=false, scanSeen=0, pollTimer=null;
function applyData(data){
  PHOTOS=data.photos||[];
  CAN_RECYCLE=!!data.canRecycle;
  rawSupport=!!data.rawOk;
  appVersion=data.version||"";
  scanning=!!data.scanning; scanSeen=data.seen||PHOTOS.length;
  refreshSub();
  if(scanning && !PHOTOS.length){
    document.getElementById('rail').innerHTML='';
    main.innerHTML='<div class="empty"><div class="spinner" style="margin:0 auto 16px"></div>Scanning your library…<br><span style="color:var(--muted2)">this can take a moment the first time</span></div>';
    return;
  }
  const lbOpen=document.getElementById('lb').classList.contains('open');
  if(!lbOpen){ const sc=main.scrollTop; render(); main.scrollTop=sc; }
}
function poll(){
  fetch("/api/photos").then(r=>r.json()).then(data=>{
    applyData(data);
    if(scanning){ if(!pollTimer) pollTimer=setInterval(poll,1500); }
    else if(pollTimer){ clearInterval(pollTimer); pollTimer=null; }
  }).catch(()=>{ /* server not ready yet */ setTimeout(poll,800); });
}
poll();
</script>
</body>
</html>"""


# ---------------------------------------------------------------- server

CTYPE = {".png": "image/png", ".gif": "image/gif", ".webp": "image/webp",
         ".bmp": "image/bmp", ".avif": "image/avif", ".ico": "image/x-icon",
         ".tif": "image/tiff", ".tiff": "image/tiff",
         ".mp4": "video/mp4", ".m4v": "video/mp4", ".mov": "video/quicktime",
         ".webm": "video/webm", ".3gp": "video/3gpp"}


def _delete_file(pid):
    """Delete one item by id. Returns (ok, recycled, error)."""
    global PHOTOS
    fp = ID_TO_PATH.get(pid)
    if not fp or not os.path.exists(fp):
        return False, False, "not found"
    recycled = False
    try:
        if _send2trash is not None:
            _send2trash(fp)
            recycled = True
        else:
            os.remove(fp)
    except Exception as e:
        return False, False, str(e)
    ID_TO_PATH.pop(pid, None)
    PHOTOS = [p for p in PHOTOS if p["id"] != pid]
    try:
        for fn in os.listdir(THUMB_DIR):
            if fn.startswith(pid + "_"):
                try:
                    os.remove(os.path.join(THUMB_DIR, fn))
                except OSError:
                    pass
    except OSError:
        pass
    return True, recycled, None


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def _send(self, code, ctype, body):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _serve_file(self, fp):
        """Serve a file with HTTP Range support (needed for video seeking)."""
        ext = os.path.splitext(fp)[1].lower()
        ctype = CTYPE.get(ext, "image/jpeg")
        try:
            fsize = os.path.getsize(fp)
        except OSError:
            self._send(404, "text/plain", b"not found"); return
        rng = self.headers.get("Range")
        start, end = 0, fsize - 1
        status = 200
        if rng:
            m = re.match(r"bytes=(\d*)-(\d*)", rng)
            if m:
                if m.group(1):
                    start = int(m.group(1))
                if m.group(2):
                    end = int(m.group(2))
                start = max(0, start)
                end = min(end, fsize - 1)
                if start > end:
                    start, end = 0, fsize - 1
                status = 206
        length = end - start + 1
        try:
            with open(fp, "rb") as f:
                f.seek(start)
                self.send_response(status)
                self.send_header("Content-Type", ctype)
                self.send_header("Accept-Ranges", "bytes")
                self.send_header("Content-Length", str(length))
                if status == 206:
                    self.send_header("Content-Range", f"bytes {start}-{end}/{fsize}")
                self.end_headers()
                if self.command == "HEAD":
                    return
                remaining = length
                chunk = 64 * 1024
                while remaining > 0:
                    data = f.read(min(chunk, remaining))
                    if not data:
                        break
                    try:
                        self.wfile.write(data)
                    except (BrokenPipeError, ConnectionResetError):
                        return
                    remaining -= len(data)
        except Exception:
            pass

    def do_POST(self):
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)
        if parsed.path == "/delete":
            pid = (qs.get("id") or [""])[0]
            ok, recycled, err = _delete_file(pid)
            code = 404 if (not ok and err == "not found") else 200
            self._send(code, "application/json",
                       json.dumps({"ok": ok, "recycled": recycled, "error": err}).encode("utf-8"))
            return
        if parsed.path == "/delete_many":
            ids = (qs.get("ids") or [""])[0]
            id_list = [x for x in ids.split(",") if x]
            deleted = 0
            recycled_any = False
            failed = []
            for pid in id_list:
                ok, recycled, err = _delete_file(pid)
                if ok:
                    deleted += 1
                    recycled_any = recycled_any or recycled
                else:
                    failed.append(pid)
            self._send(200, "application/json",
                       json.dumps({"ok": True, "deleted": deleted,
                                   "recycled": recycled_any, "failed": failed}).encode("utf-8"))
            return
        self._send(404, "text/plain", b"not found")

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        qs = parse_qs(parsed.query)

        if path in ("/", "/index.html"):
            self._send(200, "text/html; charset=utf-8", INDEX_HTML.encode("utf-8"))
            return

        if path == "/api/photos":
            snap = list(PHOTOS)  # snapshot (scan may still be appending)
            rng = ""
            if snap:
                ts = [p["ts"] for p in snap]
                lo = datetime.fromtimestamp(min(ts)).strftime("%b %Y")
                hi = datetime.fromtimestamp(max(ts)).strftime("%b %Y")
                rng = f"{lo} – {hi}"
            imgs = sum(1 for p in snap if p["kind"] == "image")
            vids = len(snap) - imgs
            summary = f"{imgs:,} photos · {vids:,} videos"
            body = json.dumps({"photos": snap, "range": rng, "summary": summary,
                               "canRecycle": _send2trash is not None,
                               "rawOk": RAW_OK, "heifOk": HEIF_OK, "version": APP_VERSION,
                               "scanning": not SCAN["done"], "seen": SCAN["seen"]}).encode("utf-8")
            self._send(200, "application/json", body)
            return

        if path == "/thumb":
            pid = (qs.get("id") or [""])[0]
            fp = ID_TO_PATH.get(pid)
            if not fp:
                self._send(404, "text/plain", b"not found"); return
            p = next((x for x in PHOTOS if x["id"] == pid), None)
            data = make_video_thumb(fp, pid) if (p and p["kind"] == "video") else make_image_thumb(fp, pid)
            if data is None:
                data = placeholder_thumb()
            self._send(200, "image/jpeg", data)
            return

        if path == "/preview":
            pid = (qs.get("id") or [""])[0]
            fp = ID_TO_PATH.get(pid)
            if not fp or not os.path.exists(fp):
                self._send(404, "text/plain", b"not found"); return
            data = make_preview(fp, pid)
            if data is None:
                self._serve_file(fp); return
            self._send(200, "image/jpeg", data)
            return

        if path == "/full":
            pid = (qs.get("id") or [""])[0]
            fp = ID_TO_PATH.get(pid)
            if not fp or not os.path.exists(fp):
                self._send(404, "text/plain", b"not found"); return
            self._serve_file(fp)
            return

        self._send(404, "text/plain", b"not found")


# ---------------------------------------------------------------- config / folder

CONFIG_DIR = os.path.join(
    os.environ.get("APPDATA") or os.path.join(os.path.expanduser("~"), ".config"),
    "PhotoBrowser")
CONFIG_FILE = os.path.join(CONFIG_DIR, "config.json")


def load_config():
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(cfg):
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f)
    except Exception:
        pass


def choose_folder_dialog(initial=None):
    """Native folder picker (used when launched with no folder, e.g. the .exe)."""
    try:
        import tkinter as tk
        from tkinter import filedialog
        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        folder = filedialog.askdirectory(
            title="Choose your photos folder",
            initialdir=initial or os.path.expanduser("~"))
        root.destroy()
        return folder or None
    except Exception:
        return None


def _log_error(text):
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(os.path.join(CONFIG_DIR, "error.log"), "a", encoding="utf-8") as f:
            f.write(text + "\n")
    except Exception:
        pass


def write_startup_log(folders):
    """Write which optional features loaded, so problems are easy to diagnose."""
    lines = [
        f"Photo Browser {APP_VERSION}",
        f"time: {datetime.now().isoformat(timespec='seconds')}",
        f"python: {sys.version.split()[0]}",
        f"running as bundled .exe: {getattr(sys, 'frozen', False)}",
        f"folders: {folders}",
        "RAW display: built-in embedded-preview extractor (always on)",
        f"RAW full-decode (rawpy) loaded: {RAW_OK}" +
        (f"  [rawpy {getattr(rawpy, '__version__', '?')}]" if RAW_OK else f"  (optional; not bundled: {RAW_ERR})"),
        f"HEIC (pillow-heif) loaded: {HEIF_OK}" + ("" if HEIF_OK else f"  ERROR: {HEIF_ERR}"),
        f"Recycle Bin (send2trash): {_send2trash is not None}",
        f"ffmpeg: {FFMPEG or 'not found'}",
    ]
    txt = "\n".join(lines) + "\n"
    print(txt)
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(os.path.join(CONFIG_DIR, "startup.log"), "w", encoding="utf-8") as f:
            f.write(txt)
    except Exception:
        pass


def _show_error_box(text):
    try:
        import tkinter as tk
        from tkinter import messagebox
        r = tk.Tk(); r.withdraw(); r.attributes("-topmost", True)
        messagebox.showerror("Photo Browser — error", text)
        r.destroy()
    except Exception:
        pass


def background_scan(folders, debug=False):
    """Run the scan off the UI thread so the window can appear immediately."""
    global _PREWARM_STARTED
    SCAN["done"] = False
    SCAN["seen"] = 0
    try:
        scan(folders, debug=debug)
    except Exception:
        _log_error(traceback.format_exc())
    finally:
        SCAN["done"] = True
    prewarm_thumbnails()


def rescan(folders):
    """Clear the index and scan again in the background (in-app 'Change folder')."""
    global _PREWARM_STARTED
    PHOTOS.clear()
    ID_TO_PATH.clear()
    _PREWARM_STARTED = False
    threading.Thread(target=background_scan, args=(folders, False), daemon=True).start()


class WebviewApi:
    """Exposed to the native window's JavaScript as window.pywebview.api."""
    def pick_folder(self):
        try:
            import webview
            win = webview.windows[0] if webview.windows else None
            result = win.create_file_dialog(webview.FOLDER_DIALOG) if win else None
        except Exception:
            result = None
        if not result:
            return {"ok": False}
        folder = result[0] if isinstance(result, (list, tuple)) else result
        save_config({"folders": [folder]})
        rescan([folder])
        return {"ok": True, "folder": folder}


def _run_main():
    ap = argparse.ArgumentParser(description="Browse photos and videos by date (non-destructive).")
    ap.add_argument("folders", nargs="*", help="Folder(s) to scan. If omitted, uses your saved folder or asks.")
    ap.add_argument("--port", type=int, default=0, help="Port (default: auto-pick a free one).")
    ap.add_argument("--browser", action="store_true", help="Open in your web browser instead of the app window.")
    ap.add_argument("--no-browser", action="store_true", help="With --browser, don't auto-open the browser.")
    ap.add_argument("--pick", action="store_true", help="Choose the photo folder now (and remember it).")
    ap.add_argument("--debug", action="store_true", help="Print every folder scanned and file counts.")
    args = ap.parse_args()

    folders = list(args.folders)
    if not folders and not args.pick:
        folders = load_config().get("folders") or []
    if args.pick or not folders:
        chosen = choose_folder_dialog((folders or [None])[0])
        if chosen:
            folders = [chosen]
            save_config({"folders": folders})
        elif not folders:
            sys.exit("No folder selected.")

    folders = [f for f in folders if os.path.isdir(f)]
    if not folders:
        sys.exit("No valid folder to scan. Run again to pick one.")

    write_startup_log(folders)

    # Start the web server, then scan in the background so the window shows at once.
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    port = server.server_address[1]
    threading.Thread(target=server.serve_forever, daemon=True).start()
    url = f"http://localhost:{port}"
    threading.Thread(target=background_scan, args=(folders, args.debug), daemon=True).start()

    if not args.browser:
        try:
            import webview
            webview.create_window("Photos", url, width=1240, height=840,
                                  min_size=(860, 600), js_api=WebviewApi())
            print(f"Opening the Photos app window…  (running locally at {url})")
            webview.start()
            return
        except Exception as e:
            _log_error("webview unavailable: " + repr(e))
            print(f"Native app window unavailable ({e}); opening in your browser instead.")

    print(f"\nOpen this in your browser:  {url}\nPress Ctrl+C to stop.\n")
    if not args.no_browser:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        threading.Event().wait()
    except KeyboardInterrupt:
        print("\nStopped.")


def main():
    try:
        _run_main()
    except SystemExit:
        raise
    except Exception:
        tb = traceback.format_exc()
        _log_error(tb)
        _show_error_box("Photo Browser hit an error on startup:\n\n" + tb +
                        "\n\nA copy was saved to:\n" + os.path.join(CONFIG_DIR, "error.log"))
        raise


if __name__ == "__main__":
    main()
