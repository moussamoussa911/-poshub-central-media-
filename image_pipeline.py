"""One path for every new dish/article photo (Paket 2).

A photo can come from the PC (3-6 MB phone pictures), from Open Food Facts,
from the Pexels/Pixabay photo search or from any other public https URL.
Every route ends here:

1. fetch once (https only, public host, TLS verified, short timeouts,
   streamed and cut at 5 MB),
2. check with Pillow that the bytes really are an image (never by file
   extension), fix the EXIF orientation, shrink to 1280 px plus a 400 px
   thumbnail and drop camera metadata such as GPS,
3. store the result content-addressed in the Speisen image folder
   (``menu_image_store``); the existing upload queue (Paket 1) then takes
   the file to the image server.

The module also holds the image provenance (licence + credit line) that
travels with a dish, the per-restaurant owner token used to keep customer
uploads private on the central image server, and the client of the image
server's photo-search proxy.

Rules: no Tk, no ``main.py`` imports. Every function is blocking and
thread-safe and is meant to run in a worker thread. All HTTP verifies TLS.
Only :class:`ImagePipelineError` is raised (``search_stock_photos`` never
raises).
"""

from __future__ import annotations

import hashlib
import io
import ipaddress
import os
import re
import secrets
import socket
import threading
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import urljoin, urlparse

IMAGE_OWNER_HEADER = "X-Image-Owner"
LICENSE_OFF = "CC BY-SA 3.0"
LICENSE_PEXELS = "Pexels-Lizenz"
LICENSE_PIXABAY = "Pixabay-Inhaltslizenz"
LICENSE_URLS = {LICENSE_OFF: "https://creativecommons.org/licenses/by-sa/3.0/deed.de"}
SYMBOLBILD_PREFIX = "Symbolbild"
MAX_EDGE = 1280
THUMB_EDGE = 400
MAX_DOWNLOAD_BYTES = 5 * 1024 * 1024
MAX_LOCAL_FILE_BYTES = 25 * 1024 * 1024
MAX_PIXELS = 50_000_000

PROVIDER_LINKS = {"pexels": "https://www.pexels.com", "pixabay": "https://pixabay.com"}

# Limits for the provenance columns (hub, website API, Scan & Order).
SOURCE_URL_MAX = 500
LICENSE_MAX = 60
ATTRIBUTION_MAX = 200

_JPEG_QUALITY = 82
_THUMB_JPEG_QUALITY = 80
_DEFAULT_USER_AGENT = "M3Kassensystem"
_MAX_REDIRECTS = 4
_CHUNK = 64 * 1024
# Formats Pillow may decode here. EPS/PS (Ghostscript) and other exotic
# plugins are never opened for data that came from the internet.
_PIL_FORMATS = ("JPEG", "MPO", "PNG", "WEBP", "GIF", "BMP", "TIFF", "AVIF")
_HEIF_FORMATS = ("HEIF",)
_HEIF_BRANDS = frozenset({b"heic", b"heix", b"hevc", b"hevx", b"heim", b"heis", b"mif1", b"msf1"})

_MESSAGES = {
    "network": "Bild konnte nicht geladen werden – keine Verbindung.",
    "timeout": "Bild konnte nicht geladen werden – Zeitüberschreitung.",
    "http_status": "Bild konnte nicht geladen werden (HTTP {status}).",
    "too_large": "Bild ist zu groß (max. 5 MB).",
    "too_large_file": "Datei ist zu groß (max. 25 MB).",
    "not_image": "Die Datei ist kein gültiges Bild.",
    "too_many_pixels": "Das Bild ist zu groß (max. 50 Megapixel).",
    "heic_unsupported": (
        "iPhone-Fotos im HEIC-Format werden auf diesem PC nicht unterstützt. "
        "Bitte das Foto als JPG speichern oder am iPhone unter Einstellungen › "
        "Kamera › Formate „Maximale Kompatibilität“ wählen."
    ),
    "unsafe_url": "Diese Bildadresse ist nicht erlaubt.",
    "store": "Bild konnte nicht gespeichert werden: {detail}",
}


class ImagePipelineError(Exception):
    """A photo could not be fetched, decoded or stored.

    ``code`` is one of network, timeout, http_status, too_large, not_image,
    too_many_pixels, heic_unsupported, unsafe_url, store. ``message`` is the
    German text for the till's status line; ``str(exc) == message``.
    """

    def __init__(self, code: str, message: str = "", **fmt: Any) -> None:
        self.code = str(code or "store")
        if not message:
            template = _MESSAGES.get(self.code) or _MESSAGES["store"]
            try:
                message = template.format(**{"status": "", "detail": "", **fmt})
            except Exception:
                message = template
        self.message = message
        super().__init__(message)

    def __str__(self) -> str:  # pragma: no cover - trivial
        return self.message


# ---------------------------------------------------------------------------
# Provenance
# ---------------------------------------------------------------------------

_WS_RE = re.compile(r"\s+")


def _one_line(value: Any) -> str:
    if value is None:
        return ""
    text = str(value)
    text = "".join(ch if (ch >= " " or ch in "\t\r\n") else " " for ch in text)
    return _WS_RE.sub(" ", text).strip()


def clean_source_url(value: Any) -> str:
    """https link for a credit, or "" (never truncated: a cut URL is broken)."""

    url = _one_line(value)
    if not url or len(url) > SOURCE_URL_MAX or not url.lower().startswith("https://"):
        return ""
    if " " in url:
        return ""
    return url


def clean_license(value: Any) -> str:
    return _one_line(value)[:LICENSE_MAX].strip()


def clean_attribution(value: Any) -> str:
    return _one_line(value)[:ATTRIBUTION_MAX].strip()


def clean_provenance_values(source_url: Any, license: Any, attribution: Any) -> tuple[str, str, str]:
    """The cleaning every channel applies: strip, one line, length limits."""

    return clean_source_url(source_url), clean_license(license), clean_attribution(attribution)


def _pick(item: Mapping, *keys: str) -> Any:
    for key in keys:
        try:
            if key in item and item.get(key) is not None:
                return item.get(key)
        except Exception:
            continue
    return ""


@dataclass(frozen=True)
class ImageProvenance:
    source_url: str = ""
    license: str = ""
    attribution: str = ""

    @property
    def is_symbolic(self) -> bool:
        return str(self.attribution or "").strip().startswith(SYMBOLBILD_PREFIX)

    @property
    def is_empty(self) -> bool:
        return not (self.source_url or self.license or self.attribution)

    def cleaned(self) -> "ImageProvenance":
        src, lic, attr = clean_provenance_values(self.source_url, self.license, self.attribution)
        return ImageProvenance(source_url=src, license=lic, attribution=attr)

    def as_payload(self) -> dict:
        c = self.cleaned()
        return {
            "image_source_url": c.source_url,
            "imageSourceUrl": c.source_url,
            "image_license": c.license,
            "imageLicense": c.license,
            "image_attribution": c.attribution,
            "imageAttribution": c.attribution,
        }

    @classmethod
    def from_item(cls, item: Mapping | None) -> "ImageProvenance":
        if not isinstance(item, Mapping):
            return cls()
        return cls(
            source_url=str(_pick(item, "image_source_url", "imageSourceUrl") or ""),
            license=str(_pick(item, "image_license", "imageLicense") or ""),
            attribution=str(_pick(item, "image_attribution", "imageAttribution") or ""),
        ).cleaned()


def off_attribution(site_name: str = "Open Food Facts") -> str:
    return f"Foto: {site_name or 'Open Food Facts'}, {LICENSE_OFF}"


def pexels_attribution(photographer: str = "") -> str:
    name = clean_attribution(photographer)[:80].strip()
    if name:
        return clean_attribution(f"{SYMBOLBILD_PREFIX} · Foto: {name} / Pexels")
    return f"{SYMBOLBILD_PREFIX} · Foto: Pexels"


def pixabay_attribution(user: str = "") -> str:
    name = clean_attribution(user)[:80].strip()
    if name:
        return clean_attribution(f"{SYMBOLBILD_PREFIX} · Bild: {name} / Pixabay")
    return f"{SYMBOLBILD_PREFIX} · Pixabay"


# ---------------------------------------------------------------------------
# URL safety
# ---------------------------------------------------------------------------

_PRIVATE_SUFFIXES = (
    ".local", ".lan", ".fritz.box", ".internal", ".localhost", ".localdomain",
    ".home.arpa", ".intranet", ".corp", ".home",
)
_NUMERIC_HOST_RE = re.compile(r"^[0-9a-fx.]+$")


def _ip_is_public(ip: "ipaddress.IPv4Address | ipaddress.IPv6Address") -> bool:
    mapped = getattr(ip, "ipv4_mapped", None)
    if mapped is not None:
        ip = mapped
    if (
        ip.is_private
        or ip.is_loopback
        or ip.is_link_local
        or ip.is_multicast
        or ip.is_reserved
        or ip.is_unspecified
    ):
        return False
    return bool(ip.is_global)


def is_public_image_url(url: str) -> bool:
    """True only for an absolute http(s) URL on a public internet host.

    False for relative paths, localhost, 127/8, ::1, 10/8, 172.16/12,
    192.168/16, 169.254/16, *.local/.lan/.fritz.box/.internal and bare host
    names. Such addresses must never be published as an online image URL.
    The check looks at the address only; it does not resolve DNS.
    """

    text = str(url or "").strip()
    if not text or any(ch.isspace() for ch in text):
        return False
    try:
        parsed = urlparse(text)
    except Exception:
        return False
    if parsed.scheme.lower() not in ("http", "https"):
        return False
    try:
        host = (parsed.hostname or "").strip().rstrip(".").lower()
        _ = parsed.port  # raises ValueError for a malformed port
    except Exception:
        return False
    if not host:
        return False
    if host == "localhost" or host.endswith(_PRIVATE_SUFFIXES):
        return False
    try:
        return _ip_is_public(ipaddress.ip_address(host))
    except ValueError:
        pass
    if _NUMERIC_HOST_RE.match(host):
        # Shorthand IPv4 forms such as 0x7f.1 or 127.1 reach loopback too.
        try:
            packed = socket.inet_aton(host)
        except (OSError, ValueError):
            packed = b""
        if packed:
            return _ip_is_public(ipaddress.IPv4Address(packed))
    if "." not in host:
        return False
    labels = host.split(".")
    if any(not label for label in labels):
        return False
    return True


def _require_safe_https(url: str) -> str:
    text = str(url or "").strip()
    if not text.lower().startswith("https://") or not is_public_image_url(text):
        raise ImagePipelineError("unsafe_url")
    return text


# ---------------------------------------------------------------------------
# Fetching
# ---------------------------------------------------------------------------

def _requests_module():
    import requests  # local import: keeps the module importable in tools without requests

    return requests


def _classify_request_error(exc: BaseException) -> ImagePipelineError:
    try:
        requests = _requests_module()
        if isinstance(exc, requests.exceptions.Timeout):
            return ImagePipelineError("timeout")
    except Exception:
        pass
    if isinstance(exc, TimeoutError) or "timed out" in str(exc).lower():
        return ImagePipelineError("timeout")
    return ImagePipelineError("network")


def _close_quietly(resp: Any) -> None:
    try:
        resp.close()
    except Exception:
        pass


def _read_timeout(timeout: Any) -> float:
    try:
        if isinstance(timeout, (tuple, list)):
            return float(timeout[-1])
        return float(timeout)
    except Exception:
        return 8.0


def fetch_image_bytes(
    url: str,
    *,
    max_bytes: int = MAX_DOWNLOAD_BYTES,
    timeout: Any = (4.0, 8.0),
    session: Any = None,
    user_agent: str = "",
) -> bytes:
    """Download an image once: https only, public host, TLS verified.

    A declared Content-Length above *max_bytes* is refused before reading;
    the body is streamed and cut at *max_bytes*. Redirects are followed by
    hand (at most 4) and every hop must pass the same URL check.
    """

    current = _require_safe_https(url)
    try:
        limit = max(1, int(max_bytes))
    except Exception:
        limit = MAX_DOWNLOAD_BYTES
    http = session if session is not None else _requests_module()
    headers = {
        "User-Agent": _one_line(user_agent) or _DEFAULT_USER_AGENT,
        # No AVIF: not every Pillow build on the tills can decode it.
        "Accept": "image/jpeg,image/png,image/webp,image/*;q=0.8",
    }
    # A server that drips bytes must not hold a worker for minutes.
    deadline = time.monotonic() + max(20.0, _read_timeout(timeout) * 3.0)

    resp = None
    for _hop in range(_MAX_REDIRECTS + 1):
        try:
            resp = http.get(
                current,
                headers=headers,
                timeout=timeout,
                stream=True,
                verify=True,
                allow_redirects=False,
            )
        except ImagePipelineError:
            raise
        except Exception as exc:
            raise _classify_request_error(exc) from None
        status = int(getattr(resp, "status_code", 0) or 0)
        if status in (301, 302, 303, 307, 308):
            location = str((getattr(resp, "headers", None) or {}).get("Location") or "").strip()
            _close_quietly(resp)
            if not location:
                raise ImagePipelineError("http_status", status=status)
            current = _require_safe_https(urljoin(current, location))
            continue
        break
    else:
        if resp is not None:
            _close_quietly(resp)
        raise ImagePipelineError("network")

    try:
        status = int(getattr(resp, "status_code", 0) or 0)
        if status != 200:
            raise ImagePipelineError("http_status", status=status)
        declared = str((getattr(resp, "headers", None) or {}).get("Content-Length") or "").strip()
        if declared.isdigit() and int(declared) > limit:
            raise ImagePipelineError("too_large")
        buf = bytearray()
        try:
            for chunk in resp.iter_content(chunk_size=_CHUNK):
                if not chunk:
                    continue
                buf.extend(chunk)
                if len(buf) > limit:
                    raise ImagePipelineError("too_large")
                if time.monotonic() > deadline:
                    raise ImagePipelineError("timeout")
        except ImagePipelineError:
            raise
        except Exception as exc:
            raise _classify_request_error(exc) from None
        if not buf:
            raise ImagePipelineError("not_image")
        return bytes(buf)
    finally:
        _close_quietly(resp)


# ---------------------------------------------------------------------------
# Decoding / normalising
# ---------------------------------------------------------------------------

_HEIF_LOCK = threading.Lock()
_HEIF_STATE: dict = {"checked": False, "ok": False}


def heif_supported() -> bool:
    """True when ``pillow_heif`` is importable (its opener is registered once)."""

    with _HEIF_LOCK:
        if _HEIF_STATE["checked"]:
            return bool(_HEIF_STATE["ok"])
        ok = False
        try:
            import pillow_heif  # type: ignore

            try:
                pillow_heif.register_heif_opener()
            except Exception:
                pass
            ok = True
        except Exception:
            ok = False
        _HEIF_STATE["checked"] = True
        _HEIF_STATE["ok"] = ok
        return ok


def file_dialog_types() -> list[tuple[str, str]]:
    """File types for the "Vom PC" dialog. HEIC is always listed so that an
    iPhone photo can be picked and the German hint can explain what to do."""

    return [
        ("Bilder", "*.jpg *.jpeg *.png *.webp *.heic *.heif *.gif *.bmp"),
        ("Alle Dateien", "*.*"),
    ]


def _is_heif(data: bytes) -> bool:
    head = bytes(data[:12])
    return len(head) >= 12 and head[4:8] == b"ftyp" and head[8:12] in _HEIF_BRANDS


@dataclass(frozen=True)
class NormalizedImage:
    data: bytes
    ext: str
    width: int
    height: int
    format: str
    thumb_data: bytes
    thumb_ext: str


def _has_real_alpha(im: Any) -> bool:
    try:
        if im.mode in ("RGBA", "LA", "PA") or (im.mode in ("P", "L", "RGB") and "transparency" in im.info):
            alpha = im.convert("RGBA").getchannel("A")
            lo, _hi = alpha.getextrema()
            return lo < 255
    except Exception:
        return False
    return False


# Camera/editor metadata that never leaves the till (EXIF incl. GPS, XMP,
# IPTC, comments).
_METADATA_KEYS = ("exif", "xmp", "XML:com.adobe.xmp", "photoshop", "iptc", "comment")


def _encode(im: Any, fmt: str, *, quality: int, icc: bytes | None) -> bytes:
    # Pillow copies im.info through resize/transpose, and its JPEG writer
    # re-embeds info["xmp"] (Pillow 11.0) and info["comment"] on save.
    for key in _METADATA_KEYS:
        im.info.pop(key, None)
    out = io.BytesIO()
    if fmt == "PNG":
        im.save(out, format="PNG", optimize=True)
    else:
        kwargs = {"quality": quality, "optimize": True, "progressive": True}
        if icc:
            kwargs["icc_profile"] = icc
        im.save(out, format="JPEG", **kwargs)
    return out.getvalue()


def normalize_image_bytes(
    data: bytes,
    *,
    max_edge: int = MAX_EDGE,
    thumb_edge: int = THUMB_EDGE,
    max_pixels: int = MAX_PIXELS,
) -> NormalizedImage:
    """Check with Pillow, fix orientation, shrink, re-encode; plus a thumbnail.

    PNG only when the picture really has transparency, else progressive JPEG
    (quality 82). GIFs use their first frame. Never upscales. Camera metadata
    (EXIF incl. GPS) is dropped.
    """

    try:
        from PIL import Image, ImageOps
    except Exception as exc:  # pragma: no cover - Pillow ships with the POS
        raise ImagePipelineError("store", detail=f"Pillow fehlt ({type(exc).__name__})") from None

    blob = bytes(data or b"")
    if not blob:
        raise ImagePipelineError("not_image")
    if _is_heif(blob) and not heif_supported():
        raise ImagePipelineError("heic_unsupported")
    wanted = _PIL_FORMATS + (_HEIF_FORMATS if heif_supported() else ())
    try:
        Image.init()  # loads the plugins so the allow-list below can be used
    except Exception:
        pass
    formats = tuple(name for name in wanted if name in getattr(Image, "OPEN", {}))
    if not formats:
        formats = ("JPEG", "PNG")

    decode_errors: tuple = (OSError, SyntaxError, ValueError, TypeError, EOFError, IndexError, KeyError)
    bomb = getattr(Image, "DecompressionBombError", None)
    try:
        with Image.open(io.BytesIO(blob), formats=list(formats)) as probe:
            width, height = probe.size
            src_size = (int(width), int(height))
            if int(width) * int(height) > int(max_pixels):
                raise ImagePipelineError("too_many_pixels")
            probe.verify()
        im = Image.open(io.BytesIO(blob), formats=list(formats))
        src_format = str(im.format or "").upper()
        if int(im.size[0]) * int(im.size[1]) > int(max_pixels):
            raise ImagePipelineError("too_many_pixels")
        # Camera/editor metadata (EXIF incl. GPS, XMP, IPTC, comments): a file
        # carrying any of it is always re-encoded, never kept byte-for-byte.
        has_exif = any(im.info.get(key) for key in _METADATA_KEYS)
        # A CMYK/grey profile must not be attached to the RGB output.
        icc = (im.info.get("icc_profile") or None) if im.mode in ("RGB", "RGBA") else None
        if src_format in ("JPEG", "MPO"):
            try:
                # DCT scaling: decoding a 12 MP phone photo at 1/2-1/8 size
                # is several times faster on slow till PCs.
                im.draft(None, (int(max_edge), int(max_edge)))
            except Exception:
                pass
        try:
            im.seek(0)
        except Exception:
            pass
        im.load()
    except ImagePipelineError:
        raise
    except Exception as exc:
        if bomb is not None and isinstance(exc, bomb):
            raise ImagePipelineError("too_many_pixels") from None
        if isinstance(exc, decode_errors) or type(exc).__name__ == "UnidentifiedImageError":
            raise ImagePipelineError("not_image") from None
        raise ImagePipelineError("not_image") from None

    try:
        orientation = 1
        try:
            orientation = int(im.getexif().get(0x0112, 1) or 1)
        except Exception:
            orientation = 1
        try:
            fixed = ImageOps.exif_transpose(im)
            if fixed is not None:
                im = fixed
        except Exception:
            pass
        transparent = _has_real_alpha(im)
        out_format = "PNG" if transparent else "JPEG"
        if transparent:
            work = im.convert("RGBA")
        else:
            work = im.convert("RGB") if im.mode != "RGB" else im.copy()
        work.thumbnail((int(max_edge), int(max_edge)), Image.LANCZOS)
        encoded = _encode(work, out_format, quality=_JPEG_QUALITY, icc=icc)
        # "Never larger than needed": a small, upright, metadata-free file in
        # the same format is kept byte-for-byte when re-encoding would grow it.
        # Compared with the size of the file itself (JPEG draft decoding may
        # already have scaled the pixels down).
        if (
            src_format == out_format
            and not has_exif
            and orientation == 1
            and tuple(work.size) == tuple(src_size)
            and len(blob) <= len(encoded)
        ):
            encoded = blob
        thumb = work.copy()
        thumb.thumbnail((int(thumb_edge), int(thumb_edge)), Image.LANCZOS)
        thumb_data = _encode(thumb, out_format, quality=_THUMB_JPEG_QUALITY, icc=None)
        ext = ".png" if out_format == "PNG" else ".jpg"
        return NormalizedImage(
            data=encoded,
            ext=ext,
            width=int(work.size[0]),
            height=int(work.size[1]),
            format=out_format,
            thumb_data=thumb_data,
            thumb_ext=ext,
        )
    except ImagePipelineError:
        raise
    except MemoryError:
        raise ImagePipelineError("too_many_pixels") from None
    except Exception:
        raise ImagePipelineError("not_image") from None
    finally:
        try:
            im.close()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Storing
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PipelineResult:
    local_url: str
    local_path: str
    thumb_local_url: str
    width: int
    height: int
    format: str
    bytes_written: int
    reused: bool
    provenance: ImageProvenance = field(default_factory=ImageProvenance)


def _write_thumb(static_dir: Path, name: str, data: bytes) -> bool:
    thumbs = static_dir / "thumbs"
    target = thumbs / name
    try:
        thumbs.mkdir(parents=True, exist_ok=True)
        try:
            if target.is_file() and not target.is_symlink() and target.read_bytes() == data:
                return True
        except OSError:
            pass
        tmp = thumbs / f".thumb-{os.getpid()}-{uuid.uuid4().hex}.tmp"
        try:
            with tmp.open("xb") as fh:
                fh.write(data)
                fh.flush()
                try:
                    os.fsync(fh.fileno())
                except OSError:
                    pass
            os.replace(tmp, target)
        finally:
            try:
                tmp.unlink(missing_ok=True)
            except OSError:
                pass
        return True
    except Exception:
        return False


def ingest_bytes(
    data: bytes,
    static_dir: str,
    *,
    provenance: ImageProvenance = ImageProvenance(),
) -> PipelineResult:
    """Normalise *data* and store it in *static_dir* (the Speisen image folder)."""

    norm = normalize_image_bytes(data)
    try:
        from app_core.menu_image_store import store_menu_image_bytes

        stored = store_menu_image_bytes(norm.data, static_dir, norm.ext)
    except ImagePipelineError:
        raise
    except Exception as exc:
        detail = str(exc).strip() or type(exc).__name__
        raise ImagePipelineError("store", detail=detail[:160]) from None
    base = Path(static_dir)
    thumb_name = f"{stored.path.stem}{norm.thumb_ext}"
    thumb_url = f"/static/menu_images/thumbs/{thumb_name}" if _write_thumb(base, thumb_name, norm.thumb_data) else ""
    prov = provenance.cleaned() if isinstance(provenance, ImageProvenance) else ImageProvenance()
    return PipelineResult(
        local_url=f"/static/menu_images/{stored.filename}",
        local_path=str(Path(stored.path).resolve()),
        thumb_local_url=thumb_url,
        width=norm.width,
        height=norm.height,
        format=norm.format,
        bytes_written=len(norm.data),
        reused=bool(stored.reused),
        provenance=prov,
    )


def ingest_file(
    path: str,
    static_dir: str,
    *,
    provenance: ImageProvenance = ImageProvenance(),
) -> PipelineResult:
    """A photo chosen on the PC: at most 25 MB, then like :func:`ingest_bytes`."""

    fp = str(path or "").strip()
    try:
        size = os.path.getsize(fp)
    except OSError:
        raise ImagePipelineError("not_image") from None
    if size > MAX_LOCAL_FILE_BYTES:
        raise ImagePipelineError("too_large", _MESSAGES["too_large_file"])
    try:
        with open(fp, "rb") as fh:
            data = fh.read(MAX_LOCAL_FILE_BYTES + 1)
    except OSError:
        raise ImagePipelineError("not_image") from None
    if len(data) > MAX_LOCAL_FILE_BYTES:
        raise ImagePipelineError("too_large", _MESSAGES["too_large_file"])
    return ingest_bytes(data, static_dir, provenance=provenance)


def ingest_url(
    url: str,
    static_dir: str,
    *,
    provenance: ImageProvenance,
    timeout: Any = (4.0, 8.0),
    max_bytes: int = MAX_DOWNLOAD_BYTES,
    session: Any = None,
    user_agent: str = "",
) -> PipelineResult:
    """Fetch a public https image once and store it like a PC photo."""

    data = fetch_image_bytes(url, max_bytes=max_bytes, timeout=timeout, session=session, user_agent=user_agent)
    return ingest_bytes(data, static_dir, provenance=provenance)


# ---------------------------------------------------------------------------
# Owner token / storage scopes on the image server
# ---------------------------------------------------------------------------

_OWNER_TOKEN_RE = re.compile(r"^[A-Za-z0-9_-]{32,128}$")
_SCOPE_FOLDER_RE = re.compile(r"^[ot]_[0-9a-f]{32}$")


def new_owner_token() -> str:
    return secrets.token_urlsafe(32)


def is_valid_owner_token(s: str) -> bool:
    return isinstance(s, str) and bool(_OWNER_TOKEN_RE.match(s))


def owner_scope_folder(token: str) -> str:
    if not is_valid_owner_token(token):
        raise ValueError("invalid owner token")
    digest = hashlib.sha256(("poshub-image-owner-v1:" + token).encode("utf-8")).hexdigest()
    return "o_" + digest[:32]


def tenant_scope_folder(tenant_id: str) -> str:
    tid = str(tenant_id or "").strip()
    if not tid:
        raise ValueError("empty tenant id")
    digest = hashlib.sha256(("poshub-image-tenant-v1:" + tid).encode("utf-8")).hexdigest()
    return "t_" + digest[:32]


def is_scope_folder_name(name: str) -> bool:
    return bool(_SCOPE_FOLDER_RE.match(str(name or "")))


# ---------------------------------------------------------------------------
# Photo search (client of the image server's /api/images/search proxy)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class StockPhoto:
    provider: str
    id: str
    thumb_url: str
    image_url: str
    width: int
    height: int
    license: str
    attribution: str
    source_url: str
    photographer: str = ""
    photographer_url: str = ""

    def provenance(self) -> ImageProvenance:
        attribution = clean_attribution(self.attribution)
        if not attribution:
            if self.provider == "pixabay":
                attribution = pixabay_attribution(self.photographer)
            else:
                attribution = pexels_attribution(self.photographer)
        elif not attribution.startswith(SYMBOLBILD_PREFIX):
            attribution = clean_attribution(f"{SYMBOLBILD_PREFIX} · {attribution}")
        license = clean_license(self.license) or (
            LICENSE_PIXABAY if self.provider == "pixabay" else LICENSE_PEXELS
        )
        return ImageProvenance(source_url=clean_source_url(self.source_url), license=license, attribution=attribution)


@dataclass(frozen=True)
class StockSearchResult:
    status: str
    items: tuple = ()
    message: str = ""
    provider_links: dict = field(default_factory=lambda: dict(PROVIDER_LINKS))

    @property
    def ok(self) -> bool:
        return self.status == "ok"


_SEARCH_MESSAGES = {
    "empty": "Keine Fotos gefunden für „{q}“.",
    "not_configured": "Die Fotosuche ist auf dem Bild-Server nicht eingerichtet.",
    "not_available": "Der Bild-Server kennt die Fotosuche noch nicht (Update nötig).",
    "rate_limited": "Zu viele Suchanfragen – bitte kurz warten.",
    "offline": "Keine Verbindung zum Bild-Server.",
    "error": "Fotosuche fehlgeschlagen ({detail}).",
}


def _search_result(status: str, *, q: str = "", detail: str = "", items: tuple = (), links: Mapping | None = None) -> StockSearchResult:
    template = _SEARCH_MESSAGES.get(status, "")
    detail_txt = _one_line(detail).rstrip(".") or "unbekannter Fehler"
    message = template.format(q=_one_line(q), detail=detail_txt) if template else ""
    provider_links = dict(PROVIDER_LINKS)
    if isinstance(links, Mapping):
        for key in ("pexels", "pixabay"):
            val = str(links.get(key) or "").strip()
            if val.startswith("https://"):
                provider_links[key] = val
    return StockSearchResult(status=status, items=tuple(items), message=message, provider_links=provider_links)


def _to_int(value: Any) -> int:
    try:
        return max(0, int(float(value)))
    except Exception:
        return 0


def _parse_stock_item(raw: Any) -> StockPhoto | None:
    if not isinstance(raw, Mapping):
        return None
    provider = str(raw.get("provider") or "").strip().lower()
    if provider not in ("pexels", "pixabay"):
        return None
    thumb = str(raw.get("thumb_url") or "").strip()
    image = str(raw.get("image_url") or "").strip()
    if not (thumb.startswith("https://") and image.startswith("https://")):
        return None
    if not (is_public_image_url(thumb) and is_public_image_url(image)):
        return None
    photo = StockPhoto(
        provider=provider,
        id=_one_line(raw.get("id"))[:80] or f"{provider}:{hashlib.sha1(image.encode('utf-8')).hexdigest()[:12]}",
        thumb_url=thumb,
        image_url=image,
        width=_to_int(raw.get("width")),
        height=_to_int(raw.get("height")),
        license=clean_license(raw.get("license")),
        attribution=clean_attribution(raw.get("attribution")),
        source_url=clean_source_url(raw.get("source_url")),
        photographer=_one_line(raw.get("photographer"))[:80],
        photographer_url=clean_source_url(raw.get("photographer_url")),
    )
    prov = photo.provenance()
    return StockPhoto(
        provider=photo.provider,
        id=photo.id,
        thumb_url=photo.thumb_url,
        image_url=photo.image_url,
        width=photo.width,
        height=photo.height,
        license=prov.license,
        attribution=prov.attribution,
        source_url=prov.source_url,
        photographer=photo.photographer,
        photographer_url=photo.photographer_url,
    )


def search_stock_photos(
    api_base: str,
    api_key: str,
    query: str,
    *,
    owner_token: str = "",
    per_page: int = 12,
    page: int = 1,
    timeout: Any = (3.0, 8.0),
    session: Any = None,
) -> StockSearchResult:
    """Ask the image server for Pexels/Pixabay photos. Never raises."""

    q = _one_line(query)
    try:
        base = str(api_base or "").strip().rstrip("/")
        if not base.lower().startswith(("https://", "http://")):
            return _search_result("offline", q=q)
        if len(q) < 2:
            return StockSearchResult(status="empty", items=(), message="Suchbegriff fehlt oder ist zu kurz.")
        headers = {"Accept": "application/json", "User-Agent": _DEFAULT_USER_AGENT}
        key = str(api_key or "").strip()
        if key:
            headers["X-Api-Key"] = key
        if owner_token and is_valid_owner_token(owner_token):
            headers[IMAGE_OWNER_HEADER] = owner_token
        http = session if session is not None else _requests_module()
        try:
            resp = http.get(
                f"{base}/images/search",
                params={"q": q[:80], "per_page": int(per_page or 12), "page": int(page or 1)},
                headers=headers,
                timeout=timeout,
                verify=True,
            )
        except Exception as exc:
            try:
                transport = isinstance(exc, (_requests_module().exceptions.RequestException, OSError))
            except Exception:
                transport = isinstance(exc, OSError)
            if transport:
                return _search_result("offline", q=q)
            return _search_result("error", q=q, detail=type(exc).__name__)
        status = int(getattr(resp, "status_code", 0) or 0)
        if status == 404:
            return _search_result("not_available", q=q)
        if status == 429:
            return _search_result("rate_limited", q=q)
        try:
            payload = resp.json()
        except Exception:
            payload = None
        if status != 200:
            detail = ""
            if isinstance(payload, Mapping):
                detail = _one_line(payload.get("detail"))[:120]
            return _search_result("error", q=q, detail=detail or f"HTTP {status}")
        if not isinstance(payload, Mapping):
            return _search_result("error", q=q, detail="ungültige Antwort")
        links = payload.get("provider_links") if isinstance(payload.get("provider_links"), Mapping) else None
        if payload.get("configured") is False:
            return _search_result("not_configured", q=q, links=links)
        raw_items = payload.get("items")
        items = tuple(
            photo for photo in (_parse_stock_item(r) for r in (raw_items if isinstance(raw_items, list) else []))
            if photo is not None
        )
        if items:
            return _search_result("ok", q=q, items=items, links=links)
        if payload.get("ok") is False:
            return _search_result("error", q=q, detail=_one_line(payload.get("detail")) or "Bildanbieter nicht erreichbar", links=links)
        return _search_result("empty", q=q, links=links)
    except Exception as exc:  # never raise into the UI worker
        return _search_result("error", q=q, detail=type(exc).__name__)


__all__ = [
    "ATTRIBUTION_MAX",
    "IMAGE_OWNER_HEADER",
    "ImagePipelineError",
    "ImageProvenance",
    "LICENSE_MAX",
    "LICENSE_OFF",
    "LICENSE_PEXELS",
    "LICENSE_PIXABAY",
    "LICENSE_URLS",
    "MAX_DOWNLOAD_BYTES",
    "MAX_EDGE",
    "MAX_LOCAL_FILE_BYTES",
    "MAX_PIXELS",
    "NormalizedImage",
    "PROVIDER_LINKS",
    "PipelineResult",
    "SOURCE_URL_MAX",
    "SYMBOLBILD_PREFIX",
    "StockPhoto",
    "StockSearchResult",
    "THUMB_EDGE",
    "clean_attribution",
    "clean_license",
    "clean_provenance_values",
    "clean_source_url",
    "fetch_image_bytes",
    "file_dialog_types",
    "heif_supported",
    "ingest_bytes",
    "ingest_file",
    "ingest_url",
    "is_public_image_url",
    "is_scope_folder_name",
    "is_valid_owner_token",
    "new_owner_token",
    "normalize_image_bytes",
    "off_attribution",
    "owner_scope_folder",
    "pexels_attribution",
    "pixabay_attribution",
    "search_stock_photos",
    "tenant_scope_folder",
]
