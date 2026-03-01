"""
POS Hub (Local LAN Server) — SQLite-backed API for Windows Tkinter POS + Android app.

DROP-IN FULL SERVER FILE (CLEANED + FIXED):
- FIX 1: RTDB catch-all routes (/api/{node}...) moved to the END so they don't steal /api/menu, /api/kv, /api/Pdfs
- FIX 2: Removed duplicate /api/kv and /api/menu definitions (no ambiguous routing)
- FIX 3: menu_items schema includes Android columns (including barcode) from the start
- FIX 4: barcode unique partial index created only AFTER barcode exists (and only once)

Keeps:
- RTDB emulation under /api/Tables etc (Firebase-like merge)
- /api/menu CRUD (Windows UI + Android)
- /api/kv get/set (robust body parser to avoid 422)
- PDF Inbox endpoints under /api/Pdfs (Android uploads PDFs, POS downloads/acks)
- Root-level endpoints kept for backward compatibility: /menu, /kv, /events, /ws, /orders, /auth/pin, /vouchers, /customers
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import json
import logging
import os
import re
import shutil
import socket
import sqlite3
import threading
import time
import uuid
import sys
import ssl
import tempfile
import zipfile
import urllib.request
import urllib.error
import secrets
from urllib.parse import urlparse
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Optional, List, Dict
from contextvars import ContextVar

from fastapi import (
    FastAPI,
    Header,
    HTTPException,
    Response,
    WebSocket,
    WebSocketDisconnect,
    UploadFile,
    File,
    Form,
    Body,
)
from fastapi.staticfiles import StaticFiles
from fastapi.responses import FileResponse
from starlette.requests import Request
from pydantic import BaseModel, Field, ConfigDict

log = logging.getLogger("poshub")
_REQ_CTX: ContextVar[Optional[Request]] = ContextVar("poshub_request_ctx", default=None)
_AUTH_CTX: ContextVar[Optional[dict]] = ContextVar("poshub_auth_ctx", default=None)


def _norm_key(s: Optional[str]) -> str:
    return (s or "").strip()


def _mask_key(s: str) -> str:
    """Safe masking: show only first 3 + last 3 chars."""
    if not s:
        return "<empty>"
    if len(s) <= 8:
        return s[0:1] + "…" + s[-1:]
    return s[:3] + "…" + s[-3:]


# ------------------------------
# Path helpers (EXE-safe)
# ------------------------------
def _app_root() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def _default_data_dir() -> Path:
    env = os.environ.get("POS_HUB_DATA_DIR", "").strip()

    # Windows compatibility:
    # keep legacy default under app_root/Data unless explicitly configured.
    # Linux/Render probing below remains unchanged.
    if os.name == "nt":
        candidates: list[Path] = []
        if env:
            candidates.append(Path(env).expanduser())
        candidates.append(_app_root() / "Data")
        for p in candidates:
            try:
                p.mkdir(parents=True, exist_ok=True)
                return p.resolve()
            except Exception:
                continue
        return (_app_root() / "Data").resolve()

    candidates: list[Path] = []

    def _var_data_space_variants() -> list[Path]:
        out: list[Path] = []
        try:
            varp = Path("/var")
            if not varp.exists():
                return out
            for n in os.listdir("/var"):
                # Render mount-path UI can accidentally store trailing spaces (e.g. "data  ").
                if isinstance(n, str) and n.startswith("data"):
                    p = varp / n
                    if p.is_dir():
                        out.append(p)
        except Exception:
            pass
        return out

    if env:
        candidates.append(Path(env).expanduser())
        # If env says /var/data but that exact path is missing, try discovered /var/data* mounts.
        if env.rstrip("/") == "/var/data":
            candidates.extend(_var_data_space_variants())
    # Prefer persistent disk locations before ephemeral /tmp.
    candidates.extend(_var_data_space_variants())
    candidates.append(Path("/var/data"))
    candidates.append(_app_root() / "Data")
    candidates.append(Path("/tmp/poshub-data"))

    for p in candidates:
        try:
            p.mkdir(parents=True, exist_ok=True)
            return p.resolve()
        except Exception:
            continue

    # last resort: keep prior behavior
    return _app_root() / "Data"


def _default_db_path() -> Path:
    env_db = os.environ.get("POS_HUB_DB_PATH", "").strip()
    if env_db:
        p = Path(env_db).expanduser()
        try:
            p.parent.mkdir(parents=True, exist_ok=True)
            return p
        except Exception:
            # invalid/unwritable configured DB path -> fall back to writable default
            pass

    # Local compatibility:
    # if runtime config specifies a DB path, prefer it.
    try:
        rt = (_app_root() / "poshub_runtime.json").resolve()
        if rt.exists():
            cfg = json.loads(rt.read_text(encoding="utf-8"))
            rt_db = str((cfg or {}).get("db_path") or "").strip()
            if rt_db:
                p = Path(rt_db).expanduser()
                if not p.is_absolute():
                    p = (_app_root() / p).resolve()
                try:
                    p.parent.mkdir(parents=True, exist_ok=True)
                    return p
                except Exception:
                    pass
    except Exception:
        pass

    data_dir = _default_data_dir()

    # If the classic POS DB exists, use it by default.
    online_db = data_dir / "online_OrderData.db"
    if online_db.exists():
        return online_db

    return data_dir / "poshub.db"


def _default_api_key() -> str:
    env_key = (
        os.environ.get("POS_HUB_API_KEY", "").strip()
        or os.environ.get("POS_HUB_KEY", "").strip()
    )
    if env_key:
        return env_key
    try:
        from poshub_runtime import load_poshub_runtime  # local import to avoid hard dependency during module import
        cfg = load_poshub_runtime(default_url="https://127.0.0.1:8766", default_key="")
        return str((cfg or {}).get("api_key") or "").strip()
    except Exception:
        return ""


def _ensure_dirs(data_dir: Path) -> dict[str, Path]:
    data_dir.mkdir(parents=True, exist_ok=True)

    static_dir = data_dir / "static"
    menu_img_dir = static_dir / "menu_images"
    # New global shared gallery folder (cross-customer media base).
    global_gallery_dir = static_dir / "global_gallery"

    local_server_dir = data_dir / "local_server"
    pdf_in_dir = local_server_dir / "pdfs_in"
    pdf_done_dir = local_server_dir / "pdfs_done"

    static_dir.mkdir(parents=True, exist_ok=True)
    menu_img_dir.mkdir(parents=True, exist_ok=True)
    global_gallery_dir.mkdir(parents=True, exist_ok=True)
    local_server_dir.mkdir(parents=True, exist_ok=True)
    pdf_in_dir.mkdir(parents=True, exist_ok=True)
    pdf_done_dir.mkdir(parents=True, exist_ok=True)

    return {
        "DATA_DIR": data_dir,
        "STATIC_DIR": static_dir,
        "MENU_IMG_DIR": menu_img_dir,
        "GLOBAL_GALLERY_DIR": global_gallery_dir,
        "LOCAL_SERVER_DIR": local_server_dir,
        "PDF_IN_DIR": pdf_in_dir,
        "PDF_DONE_DIR": pdf_done_dir,
    }


def _probe_persistence(data_dir: Path) -> dict[str, Any]:
    """
    Detect whether runtime storage looks fresh on each start.
    If this keeps returning fresh=True on every deploy, storage is ephemeral.
    """
    marker = data_dir / ".poshub_persistence_marker"
    first_seen = ""
    fresh = False
    try:
        if marker.exists():
            first_seen = (marker.read_text(encoding="utf-8") or "").strip()
        if not first_seen:
            fresh = True
            first_seen = _now()
            marker.write_text(first_seen, encoding="utf-8")
    except Exception:
        pass

    return {
        "marker_path": str(marker),
        "fresh_start": bool(fresh),
        "first_seen": first_seen,
    }


DEFAULT_DIRS = _ensure_dirs(_default_data_dir())
POS_HUB_DATA_DIR = DEFAULT_DIRS["DATA_DIR"]
POS_HUB_STATIC_DIR = DEFAULT_DIRS["STATIC_DIR"]
POS_HUB_MENU_IMG_DIR = DEFAULT_DIRS["MENU_IMG_DIR"]
POS_HUB_GLOBAL_GALLERY_DIR = DEFAULT_DIRS["GLOBAL_GALLERY_DIR"]


# ------------------------------
# SQLite helpers
# ------------------------------
def _connect(db_path: str) -> sqlite3.Connection:
    con = sqlite3.connect(db_path, timeout=5.0, check_same_thread=False)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA journal_mode=WAL;")
    con.execute("PRAGMA synchronous=NORMAL;")
    con.execute("PRAGMA foreign_keys=ON;")
    con.execute("PRAGMA busy_timeout=5000;")
    return con


def _now() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _json_loads(s: str | None, default):
    if not s:
        return default
    try:
        return json.loads(s)
    except Exception:
        return default


def _json_dumps(v) -> str:
    return json.dumps(v, ensure_ascii=False)


def _b64url_encode(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def _b64url_decode(s: str) -> bytes:
    t = str(s or "").strip()
    if not t:
        return b""
    pad = "=" * ((4 - len(t) % 4) % 4)
    return base64.urlsafe_b64decode((t + pad).encode("ascii"))


def _jwt_now() -> int:
    return int(datetime.now(timezone.utc).timestamp())


def _jwt_secret() -> str:
    return (
        os.environ.get("POS_HUB_JWT_SECRET", "").strip()
        or os.environ.get("JWT_SECRET", "").strip()
        or os.environ.get("POS_HUB_API_KEY", "").strip()
        or "poshub-dev-secret-change-me"
    )


def _jwt_alg() -> str:
    v = str(os.environ.get("POS_HUB_JWT_ALG", "HS256") or "HS256").strip().upper()
    return "RS256" if v == "RS256" else "HS256"


def _auth_mode() -> str:
    """
    Auth mode strategy:
    - api_key_only (default): simplest Android-compatible mode
    - hybrid: allow JWT bearer OR API key
    - jwt_required: bearer token required for protected endpoints
    """
    v = str(os.environ.get("POS_HUB_AUTH_MODE", "api_key_only") or "api_key_only").strip().lower()
    if v in {"hybrid", "jwt_required"}:
        return v
    return "api_key_only"


def _jwt_iss() -> str:
    return os.environ.get("POS_HUB_JWT_ISS", "poshub.local").strip() or "poshub.local"


def _jwt_aud() -> str:
    return os.environ.get("POS_HUB_JWT_AUD", "poshub-api").strip() or "poshub-api"


def _jwt_access_ttl_sec() -> int:
    try:
        return max(60, int(os.environ.get("POS_HUB_ACCESS_TTL_SEC", "900")))
    except Exception:
        return 900


def _jwt_refresh_ttl_sec() -> int:
    try:
        return max(3600, int(os.environ.get("POS_HUB_REFRESH_TTL_SEC", "2592000")))
    except Exception:
        return 2592000


def _jwt_clock_skew_sec() -> int:
    try:
        return max(0, min(300, int(os.environ.get("POS_HUB_JWT_CLOCK_SKEW_SEC", "60"))))
    except Exception:
        return 60


_RS256_PRIV_CACHE = None
_RS256_PUB_CACHE = None


def _jwt_rs256_private_pem() -> str:
    env_inline = str(os.environ.get("POS_HUB_JWT_PRIVATE_KEY_PEM", "") or "").strip()
    if env_inline:
        return env_inline
    path = str(os.environ.get("POS_HUB_JWT_PRIVATE_KEY_PATH", "") or "").strip()
    if path:
        try:
            return Path(path).read_text(encoding="utf-8", errors="replace")
        except Exception:
            return ""
    return ""


def _jwt_rs256_public_pem() -> str:
    env_inline = str(os.environ.get("POS_HUB_JWT_PUBLIC_KEY_PEM", "") or "").strip()
    if env_inline:
        return env_inline
    path = str(os.environ.get("POS_HUB_JWT_PUBLIC_KEY_PATH", "") or "").strip()
    if path:
        try:
            return Path(path).read_text(encoding="utf-8", errors="replace")
        except Exception:
            return ""
    return ""


def _jwt_rs256_load_keys():
    global _RS256_PRIV_CACHE, _RS256_PUB_CACHE
    if _RS256_PRIV_CACHE is not None and _RS256_PUB_CACHE is not None:
        return _RS256_PRIV_CACHE, _RS256_PUB_CACHE
    try:
        from cryptography.hazmat.primitives import serialization
    except Exception:
        raise HTTPException(status_code=500, detail="RS256 requires cryptography package")

    priv_pem = _jwt_rs256_private_pem()
    pub_pem = _jwt_rs256_public_pem()
    if not priv_pem or not pub_pem:
        raise HTTPException(status_code=500, detail="RS256 keys not configured")
    try:
        priv = serialization.load_pem_private_key(priv_pem.encode("utf-8"), password=None)
        pub = serialization.load_pem_public_key(pub_pem.encode("utf-8"))
    except Exception:
        raise HTTPException(status_code=500, detail="Invalid RS256 PEM keys")
    _RS256_PRIV_CACHE = priv
    _RS256_PUB_CACHE = pub
    return priv, pub


def _int_to_bytes(v: int) -> bytes:
    if int(v) == 0:
        return b"\x00"
    n = int(v)
    out = bytearray()
    while n > 0:
        out.append(n & 0xFF)
        n >>= 8
    out.reverse()
    return bytes(out)


def _jwt_kid() -> str:
    if _jwt_alg() != "RS256":
        return "hs256-local"
    pub_pem = _jwt_rs256_public_pem()
    if not pub_pem:
        return "rs256-missing-key"
    return hashlib.sha256(pub_pem.encode("utf-8")).hexdigest()[:16]


def _jwt_public_jwk() -> dict:
    if _jwt_alg() != "RS256":
        return {}
    try:
        from cryptography.hazmat.primitives.asymmetric import rsa
    except Exception:
        raise HTTPException(status_code=500, detail="RS256 requires cryptography package")
    _, pub = _jwt_rs256_load_keys()
    if not isinstance(pub, rsa.RSAPublicKey):
        raise HTTPException(status_code=500, detail="Configured public key is not RSA")
    nums = pub.public_numbers()
    n_b64 = _b64url_encode(_int_to_bytes(int(nums.n)))
    e_b64 = _b64url_encode(_int_to_bytes(int(nums.e)))
    return {
        "kty": "RSA",
        "kid": _jwt_kid(),
        "use": "sig",
        "alg": "RS256",
        "n": n_b64,
        "e": e_b64,
    }


def _jwt_sign_hs256(header: dict, payload: dict, secret_key: str) -> str:
    h = _b64url_encode(json.dumps(header, separators=(",", ":"), ensure_ascii=False).encode("utf-8"))
    p = _b64url_encode(json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8"))
    msg = f"{h}.{p}".encode("ascii")
    sig = hmac.new(secret_key.encode("utf-8"), msg, hashlib.sha256).digest()
    s = _b64url_encode(sig)
    return f"{h}.{p}.{s}"


def _jwt_sign_rs256(header: dict, payload: dict) -> str:
    try:
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives.asymmetric import padding
    except Exception:
        raise HTTPException(status_code=500, detail="RS256 requires cryptography package")
    priv, _ = _jwt_rs256_load_keys()
    h = _b64url_encode(json.dumps(header, separators=(",", ":"), ensure_ascii=False).encode("utf-8"))
    p = _b64url_encode(json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8"))
    msg = f"{h}.{p}".encode("ascii")
    try:
        sig = priv.sign(msg, padding.PKCS1v15(), hashes.SHA256())
    except Exception:
        raise HTTPException(status_code=500, detail="RS256 sign failed")
    s = _b64url_encode(sig)
    return f"{h}.{p}.{s}"


def _jwt_issue_access_token(*, tenant_id: str, subject: str, client_id: str, scopes: list[str], location_id: str = "") -> tuple[str, dict]:
    now = _jwt_now()
    ttl = _jwt_access_ttl_sec()
    claims = {
        "iss": _jwt_iss(),
        "aud": _jwt_aud(),
        "sub": str(subject or "").strip() or str(client_id or "").strip(),
        "tenant_id": str(tenant_id or "").strip(),
        "location_id": str(location_id or "").strip(),
        "client_id": str(client_id or "").strip(),
        "scope": [str(x).strip() for x in (scopes or []) if str(x).strip()],
        "iat": now,
        "nbf": now - 1,
        "exp": now + ttl,
        "jti": secrets.token_urlsafe(16),
    }
    alg = _jwt_alg()
    if alg == "RS256":
        token = _jwt_sign_rs256({"alg": "RS256", "typ": "JWT"}, claims)
    else:
        token = _jwt_sign_hs256({"alg": "HS256", "typ": "JWT"}, claims, _jwt_secret())
    return token, claims


def _jwt_decode_and_validate(token: str) -> dict:
    if not token or token.count(".") != 2:
        raise HTTPException(status_code=401, detail="Invalid bearer token format")
    h_b64, p_b64, s_b64 = token.split(".")
    try:
        hdr = json.loads(_b64url_decode(h_b64).decode("utf-8", "ignore") or "{}")
        pl = json.loads(_b64url_decode(p_b64).decode("utf-8", "ignore") or "{}")
    except Exception:
        raise HTTPException(status_code=401, detail="Invalid bearer token encoding")

    alg = str((hdr or {}).get("alg") or "").strip().upper()
    expected_alg = _jwt_alg()
    if alg != expected_alg:
        raise HTTPException(status_code=401, detail="Invalid bearer token algorithm")

    msg = f"{h_b64}.{p_b64}".encode("ascii")
    got_sig = _b64url_decode(s_b64)
    if expected_alg == "RS256":
        try:
            from cryptography.hazmat.primitives import hashes
            from cryptography.hazmat.primitives.asymmetric import padding
        except Exception:
            raise HTTPException(status_code=500, detail="RS256 requires cryptography package")
        _, pub = _jwt_rs256_load_keys()
        try:
            pub.verify(got_sig, msg, padding.PKCS1v15(), hashes.SHA256())
        except Exception:
            raise HTTPException(status_code=401, detail="Invalid bearer token signature")
    else:
        exp_sig = hmac.new(_jwt_secret().encode("utf-8"), msg, hashlib.sha256).digest()
        if not hmac.compare_digest(exp_sig, got_sig):
            raise HTTPException(status_code=401, detail="Invalid bearer token signature")

    now = _jwt_now()
    skew = _jwt_clock_skew_sec()
    iss = str((pl or {}).get("iss") or "")
    aud = str((pl or {}).get("aud") or "")
    sub = str((pl or {}).get("sub") or "")
    if iss != _jwt_iss():
        raise HTTPException(status_code=401, detail="Invalid token issuer")
    if aud != _jwt_aud():
        raise HTTPException(status_code=401, detail="Invalid token audience")
    if not sub:
        raise HTTPException(status_code=401, detail="Invalid token subject")

    def _int_claim(name: str) -> int:
        try:
            return int((pl or {}).get(name))
        except Exception:
            raise HTTPException(status_code=401, detail=f"Invalid token claim: {name}")

    iat = _int_claim("iat")
    nbf = _int_claim("nbf")
    exp = _int_claim("exp")
    if iat > now + skew:
        raise HTTPException(status_code=401, detail="Token not valid yet (iat)")
    if nbf > now + skew:
        raise HTTPException(status_code=401, detail="Token not valid yet (nbf)")
    if exp <= now - skew:
        raise HTTPException(status_code=401, detail="Token expired")

    out = dict(pl or {})
    out["_alg"] = expected_alg
    return out


def _api_key_pepper() -> str:
    return os.environ.get("POS_HUB_APIKEY_PEPPER", "").strip() or "poshub-api-pepper"


def _api_key_hash(raw: str) -> str:
    return hashlib.sha256((str(raw or "").strip() + "::" + _api_key_pepper()).encode("utf-8")).hexdigest()


def _env_int(name: str, default_v: int, min_v: int, max_v: int) -> int:
    try:
        v = int(str(os.environ.get(name, str(default_v)) or str(default_v)).strip())
    except Exception:
        v = int(default_v)
    return max(int(min_v), min(int(max_v), int(v)))


def _to_bool(v: Any) -> bool:
    s = str(v or "").strip().lower()
    return s in {"1", "true", "yes", "on", "y", "ja"}


def _scope_suffix(tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> str:
    tid = str(tenant_id or "").strip()
    lid = str(location_id or "").strip()
    if not tid and not lid:
        return ""
    return f"::tenant={tid}::loc={lid}"


def _scoped_kv_key(key: str, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> str:
    return f"{str(key or '').strip()}{_scope_suffix(tenant_id, location_id)}"


def _scoped_rtdb_node(node: str, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> str:
    return f"{str(node or '').strip()}{_scope_suffix(tenant_id, location_id)}"


def _delivery_main_key(location_id: Optional[str]) -> str:
    loc = str(location_id or "").strip() or "__default__"
    return f"delivery_main_pc::{loc}"


def _get_delivery_main_device(db_path: str, location_id: Optional[str]) -> dict:
    con = _connect(db_path)
    try:
        k = _delivery_main_key(location_id)
        row = con.execute("SELECT value FROM pos_kv WHERE key=? LIMIT 1", (k,)).fetchone()
        if not row:
            return {}
        try:
            obj = json.loads(str(row["value"] or "{}"))
            if isinstance(obj, dict):
                return obj
        except Exception:
            pass
        return {}
    finally:
        con.close()


def _set_delivery_main_device(db_path: str, location_id: Optional[str], device_id: str) -> dict:
    payload = {
        "device_id": str(device_id or "").strip(),
        "location_id": str(location_id or "").strip(),
        "updated_at": _now(),
    }
    con = _connect(db_path)
    try:
        con.execute(
            "INSERT INTO pos_kv(key,value,updated_at) VALUES(?,?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
            (_delivery_main_key(location_id), json.dumps(payload, ensure_ascii=False), _now()),
        )
        con.commit()
    finally:
        con.close()
    return payload


def _ensure_menu_columns(con: sqlite3.Connection) -> None:
    """
    Auto-migrate existing DBs (safe to run every startup).
    Adds columns required by Android Item structure.
    """
    cols = {r["name"] for r in con.execute("PRAGMA table_info(menu_items)").fetchall()}

    def add(col_name: str, ddl: str):
        if col_name not in cols:
            con.execute(f"ALTER TABLE menu_items ADD COLUMN {ddl}")

    add("default_ingredients_json", "default_ingredients_json TEXT")
    add("sauce_prices_json", "sauce_prices_json TEXT")
    add("selected_sauces_json", "selected_sauces_json TEXT")
    add("btn_sauce_on_item_json", "btn_sauce_on_item_json TEXT")
    add("btn_sauce_extra_json", "btn_sauce_extra_json TEXT")
    add("quantity", "quantity INTEGER DEFAULT 1")
    add("category", "category TEXT")
    add("available_sizes_json", "available_sizes_json TEXT")
    add("has_free_item", "has_free_item INTEGER DEFAULT 0")
    add("stock", "stock INTEGER DEFAULT 0")
    add("stock_enum", "stock_enum TEXT DEFAULT 'QUANTITY'")
    add("barcode", "barcode TEXT")
    add("incl_sauce_json", "incl_sauce_json TEXT")
    add("image_url_local", "image_url_local TEXT")
    add("image_url_online", "image_url_online TEXT")
    add("sync_online", "sync_online INTEGER DEFAULT 1")
    add("tenant_id", "tenant_id TEXT")
    add("location_id", "location_id TEXT")


def _ensure_delivery_columns(con: sqlite3.Connection) -> None:
    """
    Auto-migrate old delivery tables.
    Important: CREATE TABLE IF NOT EXISTS does not add missing columns
    when the table already exists from older versions.
    """
    cols = {r["name"] for r in con.execute("PRAGMA table_info(lieferung_daily)").fetchall()}

    def add(col_name: str, ddl: str):
        if col_name not in cols:
            con.execute(f"ALTER TABLE lieferung_daily ADD COLUMN {ddl}")

    add("store_id", "store_id TEXT")
    add("register_id", "register_id TEXT")
    add("created_at", "created_at TEXT")
    add("updated_at", "updated_at TEXT")
    add("finished_at", "finished_at TEXT")
    add("tenant_id", "tenant_id TEXT")
    add("location_id", "location_id TEXT")


def _ensure_pdf_columns(con: sqlite3.Connection) -> None:
    cols = {r["name"] for r in con.execute("PRAGMA table_info(pdf_inbox)").fetchall()}

    def add(col_name: str, ddl: str):
        if col_name not in cols:
            con.execute(f"ALTER TABLE pdf_inbox ADD COLUMN {ddl}")

    add("tenant_id", "tenant_id TEXT")
    add("location_id", "location_id TEXT")


def _init_schema(db_path: str) -> None:
    os.makedirs(os.path.dirname(db_path) or ".", exist_ok=True)
    con = _connect(db_path)
    try:
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS lieferung_daily (
            ID INTEGER PRIMARY KEY AUTOINCREMENT,
            tenant_id TEXT,
            location_id TEXT,
            store_id TEXT,
            register_id TEXT,
            tish TEXT,
            zeit INTEGER,
            gesamtepreis INTEGER,
            ordernumber TEXT,
            telefonnummber TEXT,
            adresse TEXT,
            name TEXT,
            hausnummer TEXT,
            PLZ TEXT,
            stadt TEXT,
            distance TEXT,
            driver TEXT,
            side TEXT,
            status TEXT,
            created_at TEXT,
            updated_at TEXT,
            finished_at TEXT
        )
        """
        )

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS lieferung_daily_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            lieferung_id INTEGER NOT NULL,
            item_json TEXT NOT NULL,
            FOREIGN KEY(lieferung_id) REFERENCES lieferung_daily(ID) ON DELETE CASCADE
        )
        """
        )

        # menu_items: include Android columns from the start (including barcode)
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS menu_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tenant_id TEXT,
            location_id TEXT,
            article_number TEXT UNIQUE,
            barcode TEXT,
            name TEXT NOT NULL,
            main_category TEXT,
            sub_category TEXT,
            prices_json TEXT,
            ingredients_json TEXT,
            default_ingredients_json TEXT,
            sauce_prices_json TEXT,
            selected_sauces_json TEXT,
            btn_sauce_on_item_json TEXT,
            btn_sauce_extra_json TEXT,
            incl_sauce_json TEXT,
            quantity INTEGER DEFAULT 1,
            category TEXT,
            available_sizes_json TEXT,
            has_free_ingredients INTEGER DEFAULT 0,
            number_of_ingredients INTEGER DEFAULT 0,
            has_free_item INTEGER DEFAULT 0,
            stock INTEGER DEFAULT 0,
            stock_enum TEXT DEFAULT 'QUANTITY',
            image_url TEXT,
            image_url_local TEXT,
            image_url_online TEXT,
            sync_online INTEGER DEFAULT 1,
            is_active INTEGER DEFAULT 1,
            updated_at TEXT
        )
        """
        )

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS ingredients_catalog (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            main_category TEXT NOT NULL,
            prices_json TEXT,
            is_active INTEGER DEFAULT 1,
            updated_at TEXT
        )
        """
        )
        con.execute(
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_ing_cat_name_main_unique "
            "ON ingredients_catalog(name, main_category)"
        )

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS sauces_catalog (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            main_category TEXT NOT NULL,
            prices_json TEXT,
            is_active INTEGER DEFAULT 1,
            updated_at TEXT
        )
        """
        )
        con.execute(
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_sauce_cat_name_main_unique "
            "ON sauces_catalog(name, main_category)"
        )

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS pos_kv (
            key TEXT PRIMARY KEY,
            value TEXT,
            updated_at TEXT
        )
        """
        )
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS auth_clients (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tenant_id TEXT NOT NULL,
            client_id TEXT NOT NULL,
            client_secret_hash TEXT NOT NULL,
            subject TEXT,
            scopes_json TEXT DEFAULT '[]',
            location_id TEXT DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT,
            updated_at TEXT
        )
        """
        )
        con.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_auth_clients_unique ON auth_clients(tenant_id, client_id)")

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS auth_refresh_tokens (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            token_hash TEXT NOT NULL UNIQUE,
            tenant_id TEXT NOT NULL,
            client_id TEXT NOT NULL,
            subject TEXT,
            location_id TEXT DEFAULT '',
            scopes_json TEXT DEFAULT '[]',
            jti TEXT,
            issued_at INTEGER,
            expires_at INTEGER,
            revoked_at INTEGER,
            rotated_from_hash TEXT DEFAULT '',
            replaced_by_hash TEXT DEFAULT ''
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_auth_refresh_active ON auth_refresh_tokens(tenant_id, client_id, revoked_at, expires_at)")

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS auth_api_keys (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tenant_id TEXT NOT NULL,
            location_id TEXT DEFAULT '',
            key_hash TEXT NOT NULL UNIQUE,
            key_prefix TEXT NOT NULL,
            name TEXT DEFAULT 'default',
            scopes_json TEXT DEFAULT '[]',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT,
            expires_at INTEGER,
            revoked_at INTEGER
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_auth_api_keys_tenant ON auth_api_keys(tenant_id, active, expires_at, revoked_at)")

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS events (
            seq INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT NOT NULL,
            type TEXT NOT NULL,
            payload_json TEXT
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_events_ts ON events(ts)")

        # --- vouchers (encrypted at rest) ---
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS vouchers (
            voucher_id TEXT PRIMARY KEY,
            encrypted TEXT NOT NULL,
            amount_cents INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            is_active INTEGER NOT NULL DEFAULT 1
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_vouchers_updated_at ON vouchers(updated_at)")

        con.execute(
            """
        CREATE TABLE IF NOT EXISTS voucher_tx (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            voucher_id TEXT NOT NULL,
            ts TEXT NOT NULL,
            delta_cents INTEGER NOT NULL,
            invoice_number TEXT,
            note TEXT,
            employee_id TEXT,
            employee_name TEXT,
            employee_role TEXT,
            FOREIGN KEY (voucher_id) REFERENCES vouchers(voucher_id) ON DELETE CASCADE
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_voucher_tx_voucher_id ON voucher_tx(voucher_id)")

        # Optional: minimal customers bridge for voucher lookups/upserts
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS customers (
            phone TEXT PRIMARY KEY,
            name TEXT,
            email TEXT,
            updated_at TEXT
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_customers_updated_at ON customers(updated_at)")

        # Reservations
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS reservations (
            reservation_id TEXT PRIMARY KEY,
            guest_name TEXT NOT NULL,
            phone TEXT,
            reservation_date TEXT,
            reservation_time TEXT,
            guests_count INTEGER NOT NULL DEFAULT 1,
            table_no TEXT,
            status TEXT NOT NULL DEFAULT 'booked',
            notes TEXT,
            source TEXT NOT NULL DEFAULT 'local',
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            is_active INTEGER NOT NULL DEFAULT 1
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_reservations_date_time ON reservations(reservation_date, reservation_time)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_reservations_guest ON reservations(guest_name)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_reservations_updated ON reservations(updated_at)")

        # RTDB emulation
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS rtdb_nodes (
            node TEXT NOT NULL,
            node_key TEXT NOT NULL,
            json TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            PRIMARY KEY (node, node_key)
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_rtdb_nodes_node ON rtdb_nodes(node)")

        # PDF Inbox (Android -> POS)
        con.execute(
            """
        CREATE TABLE IF NOT EXISTS pdf_inbox (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tenant_id TEXT,
            location_id TEXT,
            store_id TEXT,
            register_id TEXT,
            table_id TEXT,
            mode TEXT,
            filename TEXT,
            rel_path TEXT,
            sha256 TEXT,
            size_bytes INTEGER,
            status TEXT,
            note TEXT,
            created_at TEXT,
            updated_at TEXT
        )
        """
        )
        con.execute("CREATE INDEX IF NOT EXISTS idx_pdf_inbox_status ON pdf_inbox(status)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_pdf_inbox_updated ON pdf_inbox(updated_at)")

        # Ensure columns exist for older DBs
        _ensure_menu_columns(con)
        _ensure_delivery_columns(con)
        _ensure_pdf_columns(con)

        # Legacy migration: keep existing ingredient/sauce rows usable in new catalogs.
        try:
            rows = con.execute(
                "SELECT name, main_category, sub_category, prices_json, is_active FROM menu_items WHERE is_active=1"
            ).fetchall()
            for r in rows:
                name = (r["name"] or "").strip()
                main_cat = (r["main_category"] or "").strip()
                subc = (r["sub_category"] or "").strip()
                if not name or not main_cat:
                    continue
                if subc in ("__INGREDIENTS__", "Ingredients"):
                    con.execute(
                        """
                        INSERT INTO ingredients_catalog(name, main_category, prices_json, is_active, updated_at)
                        VALUES(?,?,?,?,?)
                        ON CONFLICT(name, main_category)
                        DO UPDATE SET prices_json=excluded.prices_json, is_active=excluded.is_active, updated_at=excluded.updated_at
                        """,
                        (name, main_cat, r["prices_json"] or "{}", int(r["is_active"] or 1), _now()),
                    )
                elif subc == "Sauce":
                    con.execute(
                        """
                        INSERT INTO sauces_catalog(name, main_category, prices_json, is_active, updated_at)
                        VALUES(?,?,?,?,?)
                        ON CONFLICT(name, main_category)
                        DO UPDATE SET prices_json=excluded.prices_json, is_active=excluded.is_active, updated_at=excluded.updated_at
                        """,
                        (name, main_cat, r["prices_json"] or "{}", int(r["is_active"] or 1), _now()),
                    )
        except Exception:
            pass

        # Unique barcode, but allow empty/NULL barcodes (partial unique index)
        try:
            con.execute(
                "CREATE UNIQUE INDEX IF NOT EXISTS idx_menu_items_barcode_unique "
                "ON menu_items(barcode) "
                "WHERE barcode IS NOT NULL AND TRIM(barcode) <> ''"
            )
        except Exception:
            # If an older SQLite build complains, don't break startup.
            pass

        con.commit()
    finally:
        con.close()


def _emit_event(db_path: str, typ: str, payload: dict | None = None) -> int:
    con = _connect(db_path)
    try:
        cur = con.cursor()
        cur.execute(
            "INSERT INTO events(ts, type, payload_json) VALUES(?,?,?)",
            (_now(), typ, json.dumps(payload or {}, ensure_ascii=False)),
        )
        con.commit()
        return int(cur.lastrowid)
    finally:
        con.close()


def _menu_next_id(con: sqlite3.Connection) -> int:
    row = con.execute("SELECT MAX(id) AS mx FROM menu_items").fetchone()
    mx = int(row["mx"] or 0) if row else 0
    return mx + 1


def _menu_next_article_number(con: sqlite3.Connection, *, start_from: int = 1) -> str:
    row = con.execute(
        "SELECT MAX(CAST(article_number AS INTEGER)) AS mx "
        "FROM menu_items "
        "WHERE article_number IS NOT NULL AND article_number != '' "
        "AND article_number GLOB '[0-9]*'"
    ).fetchone()
    mx = int(row["mx"] or 0) if row else 0
    nxt = max(mx + 1, int(start_from))
    return str(nxt)


def _ensure_unique_article_number(con: sqlite3.Connection, proposed: Optional[str]) -> str:
    s = (proposed or "").strip()
    if not s:
        return _menu_next_article_number(con)

    exists = con.execute("SELECT 1 FROM menu_items WHERE article_number=? LIMIT 1", (s,)).fetchone()
    if exists:
        if s.isdigit():
            return _menu_next_article_number(con, start_from=int(s) + 1)
        return _menu_next_article_number(con)
    return s


def _normalize_article_number(value: Optional[str]) -> Optional[str]:
    s = (value or "").strip()
    return s if s else None


def _best_lan_ip() -> str:
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        try:
            s.close()
        except Exception:
            pass


# ------------------------------
# Models
# ------------------------------
_ALLOWED_STOCK_ENUM = {"WEIGHT", "QUANTITY", "EXCEPTION"}


class MenuItem(BaseModel):
    """
    Backwards compatible:
    - Accepts snake_case (your Windows app)
    - Also accepts Android camelCase (Kotlin Item)
    - We store snake_case in DB, but return BOTH key styles in /menu list
    """
    model_config = ConfigDict(populate_by_name=True, extra="ignore")

    article_number: Optional[str] = Field(default=None, alias="articleNumber")
    name: str
    main_category: Optional[str] = Field(default=None, alias="mainCategory")
    sub_category: Optional[str] = Field(default=None, alias="subCategory")
    prices: Dict[str, float] = Field(default_factory=dict)
    ingredients: List[str] = Field(default_factory=list)
    has_free_ingredients: bool = Field(default=False, alias="hasFreeIngredients")
    number_of_ingredients: int = Field(default=0, alias="numberOfIngredients")
    image_url: Optional[str] = Field(default=None, alias="imageUrl")
    image_url_local: Optional[str] = Field(default=None, alias="imageUrlLocal")
    image_url_online: Optional[str] = Field(default=None, alias="imageUrlOnline")
    sync_online: bool = Field(default=True, alias="syncOnline")
    is_active: bool = True
    barcode: Optional[str] = None

    # Android fields
    default_ingredients: List[str] = Field(default_factory=list, alias="defaultIngredients")
    sauce_prices: Dict[str, float] = Field(default_factory=dict, alias="saucePrices")
    selected_sauces: List[dict] = Field(default_factory=list, alias="selectedSauces")
    btn_sauce_on_item: List[dict] = Field(default_factory=list, alias="btnSauceOnItem")
    btn_sauce_extra: List[dict] = Field(default_factory=list, alias="btnSauceExtra")
    incl_sauce: Optional[dict] = Field(default=None, alias="inclSauce")

    quantity: int = 1
    category: Optional[str] = None
    available_sizes: List[str] = Field(default_factory=list, alias="availableSizes")
    has_free_item: bool = Field(default=False, alias="hasFreeItem")

    stock: int = 0
    stock_enum: str = Field(default="QUANTITY", alias="stockEnum")
    tenant_id: Optional[str] = Field(default=None, alias="tenantId")
    location_id: Optional[str] = Field(default=None, alias="locationId")


class DeliveryItem(BaseModel):
    name: str
    qty: float = 1.0
    price: float = 0.0
    variant: Optional[str] = None
    # Legacy Android field: keep as extra ingredients only.
    extras: Optional[List[str]] = None
    # Canonical addon fields
    extra_ingredients: Optional[List[str]] = Field(default=None, alias="extraIngredients")
    sauce_on_item: Optional[List[dict]] = Field(default=None, alias="sauceOnItem")
    extra_sauces: Optional[List[dict]] = Field(default=None, alias="extraSauces")
    notes: Optional[str] = None
    category: Optional[str] = None


class CreateDeliveryOrder(BaseModel):
    store_id: str = Field(default="STORE_1", alias="storeId")
    register_id: str = Field(default="KASSE_1", alias="registerId")
    tish: Optional[str] = None
    ordernumber: Optional[str] = None
    telefonnummber: Optional[str] = None
    adresse: Optional[str] = None
    hausnummer: Optional[str] = None
    PLZ: Optional[str] = None
    stadt: Optional[str] = None
    name: Optional[str] = None
    distance: Optional[str] = None
    gesamtepreis: Optional[float] = None
    side: Optional[str] = None
    status: str = "In the Kitchen"
    items: List[DeliveryItem] = Field(default_factory=list)
    tenant_id: Optional[str] = Field(default=None, alias="tenantId")
    location_id: Optional[str] = Field(default=None, alias="locationId")


class UpdateDeliveryOrder(BaseModel):
    status: Optional[str] = None
    driver: Optional[str] = None
    finished_at: Optional[str] = None
    gesamtepreis: Optional[float] = None
    updated_at: Optional[str] = None


class KVSet(BaseModel):
    key: str
    value: str
    tenant_id: Optional[str] = Field(default=None, alias="tenantId")
    location_id: Optional[str] = Field(default=None, alias="locationId")


class CatalogItem(BaseModel):
    model_config = ConfigDict(populate_by_name=True, extra="ignore")
    name: str
    main_category: str = Field(alias="mainCategory")
    prices: Dict[str, float] = Field(default_factory=dict)
    is_active: bool = Field(default=True, alias="isActive")


class PinRequest(BaseModel):
    model_config = ConfigDict(populate_by_name=True, extra="ignore")
    pin: Optional[str] = Field(default=None, min_length=1, max_length=64)
    password: Optional[str] = Field(default=None, min_length=1, max_length=64)
    code: Optional[str] = Field(default=None, min_length=1, max_length=64)


class AuthLoginRequest(BaseModel):
    tenant_id: str
    client_id: str
    client_secret: str
    location_id: Optional[str] = None


class AuthRefreshRequest(BaseModel):
    refresh_token: str


class AuthRevokeRequest(BaseModel):
    refresh_token: str


class AuthClientCreateRequest(BaseModel):
    tenant_id: str
    client_id: str
    subject: Optional[str] = None
    scopes: List[str] = Field(default_factory=list)
    location_id: Optional[str] = None
    secret: Optional[str] = None


class ApiKeyCreateRequest(BaseModel):
    tenant_id: str
    name: str = "default"
    scopes: List[str] = Field(default_factory=list)
    expires_in_days: Optional[int] = 365
    location_id: Optional[str] = None


class ApiKeyRevokeRequest(BaseModel):
    key_id: int


class VoucherUpsert(BaseModel):
    voucher_id: str
    encrypted: str
    amount_cents: int = 0
    note: Optional[str] = None
    invoice_number: Optional[str] = None
    employee: Optional[dict] = None


class VoucherDelete(BaseModel):
    voucher_id: str
    employee: Optional[dict] = None


class CustomerUpsert(BaseModel):
    phone: str
    name: Optional[str] = None
    email: Optional[str] = None


class ReservationUpsert(BaseModel):
    reservation_id: Optional[str] = None
    guest_name: str
    phone: Optional[str] = None
    reservation_date: Optional[str] = None
    reservation_time: Optional[str] = None
    guests_count: int = 1
    table_no: Optional[str] = None
    status: Optional[str] = "booked"
    notes: Optional[str] = None
    source: Optional[str] = "online"
    updated_at: Optional[str] = None


class ReservationDelete(BaseModel):
    reservation_id: str


class PdfAck(BaseModel):
    status: str = "PROCESSED"  # NEW, PROCESSED, ERROR
    note: Optional[str] = None


class AdminBranchTarget(BaseModel):
    branch_name: str
    tenant_id: Optional[str] = None
    location_id: Optional[str] = None
    base_url: str
    api_key: str
    active: bool = True
    verify_ssl: Optional[bool] = None


class AdminSummaryRequest(BaseModel):
    targets: List[AdminBranchTarget] = Field(default_factory=list)
    include_inactive: bool = False
    timeout_sec: int = 10


class AdminOutboxActionRequest(BaseModel):
    kind: str = "both"  # orders | menu | both
    include_pending: bool = False
    reset_tries: bool = True


# ------------------------------
# App factory
# ------------------------------
def create_app(
    *,
    db_path: str,
    api_key: str,
    data_dir: Optional[str] = None,
    public_scheme: str = "https",
    public_port: int = 8766,
    public_http_port: int = 0,
) -> FastAPI:
    dirs = _ensure_dirs(Path(data_dir).resolve() if data_dir else _default_data_dir())
    persist = _probe_persistence(dirs["DATA_DIR"])
    _init_schema(db_path)

    app = FastAPI(title="POS Hub", version="1.2.0")
    app.mount("/static", StaticFiles(directory=str(dirs["STATIC_DIR"])), name="static")

    app.state.public_scheme = str(public_scheme or "https").strip().lower()
    app.state.public_port = int(public_port or 8766)
    app.state.public_http_port = int(public_http_port or 0)
    app.state.db_path = db_path
    app.state.data_dir = str(dirs["DATA_DIR"])
    app.state.local_server_dir = str(dirs["LOCAL_SERVER_DIR"])
    app.state.pdf_in_dir = str(dirs["PDF_IN_DIR"])
    app.state.pdf_done_dir = str(dirs["PDF_DONE_DIR"])
    app.state.persistence_info = persist
    app.state.rate_limit_global_max = _env_int("POS_HUB_RATE_LIMIT_GLOBAL_MAX", 120, 10, 10000)
    app.state.rate_limit_global_window = _env_int("POS_HUB_RATE_LIMIT_GLOBAL_WINDOW_SEC", 60, 1, 3600)
    app.state.rate_limit_auth_max = _env_int("POS_HUB_RATE_LIMIT_AUTH_MAX", 20, 1, 2000)
    app.state.rate_limit_auth_window = _env_int("POS_HUB_RATE_LIMIT_AUTH_WINDOW_SEC", 60, 1, 3600)
    app.state.rate_limit_orders_max = _env_int("POS_HUB_RATE_LIMIT_ORDERS_MAX", 60, 1, 5000)
    app.state.rate_limit_orders_window = _env_int("POS_HUB_RATE_LIMIT_ORDERS_WINDOW_SEC", 60, 1, 3600)
    app.state.rate_limit_pdf_max = _env_int("POS_HUB_RATE_LIMIT_PDF_MAX", 20, 1, 2000)
    app.state.rate_limit_pdf_window = _env_int("POS_HUB_RATE_LIMIT_PDF_WINDOW_SEC", 60, 1, 3600)
    app.state.max_request_bytes = _env_int("POS_HUB_MAX_REQUEST_BYTES", 15 * 1024 * 1024, 64 * 1024, 1024 * 1024 * 1024)

    # Gallery admin cookie session (simple secure operator login).
    _gallery_sessions: dict[str, float] = {}
    _GALLERY_COOKIE = "gallery_admin_session"
    _GALLERY_TTL_SEC = int(_env_int("POS_HUB_GALLERY_SESSION_TTL_SEC", 12 * 3600, 900, 7 * 24 * 3600))

    def _gallery_session_purge(now_ts: Optional[float] = None):
        t = float(now_ts or time.time())
        dead = [k for k, exp in _gallery_sessions.items() if float(exp or 0.0) <= t]
        for k in dead:
            _gallery_sessions.pop(k, None)

    def _gallery_session_issue() -> tuple[str, float]:
        _gallery_session_purge()
        tok = secrets.token_urlsafe(32)
        exp = float(time.time() + _GALLERY_TTL_SEC)
        _gallery_sessions[tok] = exp
        return tok, exp

    def _gallery_session_check(request: Request) -> bool:
        _gallery_session_purge()
        try:
            tok = str(request.cookies.get(_GALLERY_COOKIE) or "").strip()
        except Exception:
            tok = ""
        if not tok:
            return False
        exp = float(_gallery_sessions.get(tok) or 0.0)
        if exp <= float(time.time()):
            _gallery_sessions.pop(tok, None)
            return False
        return True

    def _auth_gallery_admin(request: Request, x_api_key: Optional[str]) -> dict:
        # 1) Operator cookie session
        if _gallery_session_check(request):
            return {"kind": "gallery_session", "tenant_id": "", "location_id": "", "sub": "gallery-admin"}
        # 2) Fallback API key header (for scripts/tools)
        return _auth(x_api_key)

    # Strong warning for deployments that likely lose data on redeploy.
    if str(os.environ.get("RENDER", "")).strip().lower() == "true":
        if not os.environ.get("POS_HUB_DATA_DIR", "").strip() and not os.environ.get("POS_HUB_DB_PATH", "").strip():
            log.warning(
                "[persistence] RENDER detected but POS_HUB_DATA_DIR/POS_HUB_DB_PATH are not set. "
                "Redeploy can reset menu items/images if no persistent disk is attached."
            )
        if persist.get("fresh_start"):
            log.warning(
                "[persistence] Fresh data dir detected at startup (%s). "
                "If this happens on every deploy, storage is ephemeral.",
                persist.get("marker_path"),
            )

    # -----------------------
    # URL helpers
    # -----------------------
    def _request_base(request: Optional[Request] = None) -> dict:
        lan = _best_lan_ip()
        canon_scheme = getattr(app.state, "public_scheme", "https")
        canon_port = getattr(app.state, "public_port", 8766)

        if request is not None:
            req_scheme = (request.url.scheme or canon_scheme).lower()
            req_host = request.url.hostname or lan
            req_port = request.url.port or canon_port
        else:
            req_scheme = canon_scheme
            req_host = lan
            req_port = canon_port

        return {
            "lan_ip": lan,
            "canonical_local": f"{canon_scheme}://127.0.0.1:{canon_port}",
            "canonical_lan": f"{canon_scheme}://{lan}:{canon_port}",
            "request_base": f"{req_scheme}://{req_host}:{req_port}",
            "request_scheme": req_scheme,
            "request_host": req_host,
            "request_port": req_port,
        }

    def _normalize_barcode(value: Optional[str]) -> Optional[str]:
        s = (value or "").strip()
        return s if s else None

    def _coerce_image_url(request: Request, raw: Optional[str]) -> str:
        s = (raw or "").strip()
        if not s:
            return ""

        if s.startswith("http://") or s.startswith("https://"):
            try:
                pu = urlparse(s)
                host = (pu.hostname or "").strip().lower()
                if (host == "localhost" or host.startswith("127.")) and "/static/" in (pu.path or ""):
                    tail = (pu.path or "").split("/static/", 1)[1].lstrip("/")
                    try:
                        return str(request.url_for("static", path=tail))
                    except Exception:
                        base = _request_base(request)["request_base"].rstrip("/")
                        return f"{base}/static/{tail}"
            except Exception:
                pass
            return s

        if "/static/" in s:
            tail = s.split("/static/", 1)[1].lstrip("/")
            try:
                return str(request.url_for("static", path=tail))
            except Exception:
                base = _request_base(request)["request_base"].rstrip("/")
                return f"{base}/static/{tail}"

        s2 = s.lstrip("/")
        if s2.startswith("static/"):
            tail = s2.split("static/", 1)[1].lstrip("/")
            try:
                return str(request.url_for("static", path=tail))
            except Exception:
                base = _request_base(request)["request_base"].rstrip("/")
                return f"{base}/static/{tail}"

        if s2.startswith("menu_images/") or s2.startswith("global_gallery/"):
            tail = s2
            try:
                return str(request.url_for("static", path=tail))
            except Exception:
                base = _request_base(request)["request_base"].rstrip("/")
                return f"{base}/static/{tail}"

        filename = os.path.basename(s2)
        try:
            return str(request.url_for("static", path=f"global_gallery/{filename}"))
        except Exception:
            base = _request_base(request)["request_base"].rstrip("/")
            return f"{base}/static/global_gallery/{filename}"

    def _force_http_static_url(request: Request, url: str) -> str:
        s = (url or "").strip()
        if not s or "/static/" not in s:
            return s
        try:
            tail = s.split("/static/", 1)[1].lstrip("/")
            http_port = int(getattr(app.state, "public_http_port", 0) or 0)
            if http_port <= 0:
                return s
            req_host = (request.url.hostname or "").strip()
            if not req_host:
                req_host = _best_lan_ip()
            return f"http://{req_host}:{http_port}/static/{tail}"
        except Exception:
            return s

    # Log every request (GUI can show these)
    _req_rate_lock = threading.Lock()
    _req_rate_hits: dict[str, list[float]] = {}

    def _rate_allow(bucket: str, max_hits: int, window_sec: int) -> bool:
        nowf = time.time()
        b = str(bucket or "").strip()
        if not b:
            return True
        with _req_rate_lock:
            arr = list(_req_rate_hits.get(b, []))
            arr = [x for x in arr if (nowf - x) <= float(window_sec)]
            if len(arr) >= int(max_hits):
                _req_rate_hits[b] = arr
                return False
            arr.append(nowf)
            _req_rate_hits[b] = arr
            return True

    def _request_ip(request: Request) -> str:
        try:
            fwd = str(request.headers.get("x-forwarded-for") or "").strip()
            if fwd:
                return fwd.split(",")[0].strip()
        except Exception:
            pass
        try:
            real = str(request.headers.get("x-real-ip") or "").strip()
            if real:
                return real
        except Exception:
            pass
        try:
            if request.client and request.client.host:
                return str(request.client.host)
        except Exception:
            pass
        return "unknown"

    def _sensitive_bucket_for_path(path: str) -> tuple[str, int, int] | None:
        p = str(path or "").lower()
        if p.startswith("/auth/") or p.startswith("/api/auth/"):
            return ("auth", int(app.state.rate_limit_auth_max), int(app.state.rate_limit_auth_window))
        if p == "/orders/delivery" or p.startswith("/orders/delivery/"):
            return ("orders", int(app.state.rate_limit_orders_max), int(app.state.rate_limit_orders_window))
        if p.startswith("/api/pdfs") or p.startswith("/pdfs"):
            return ("pdf", int(app.state.rate_limit_pdf_max), int(app.state.rate_limit_pdf_window))
        return None

    def _is_unlimited_path(path: str) -> bool:
        p = str(path or "").lower()
        return p in {"/health", "/.well-known/jwks.json", "/.well-known/auth-meta"}

    @app.middleware("http")
    async def log_requests(request: Request, call_next):
        t0 = time.perf_counter()
        client = request.client.host if request.client else "?"
        method = request.method
        path = request.url.path
        ip = _request_ip(request)

        # Request size guard (best effort; relies on Content-Length header when present)
        try:
            cl = int(str(request.headers.get("content-length") or "0").strip() or "0")
        except Exception:
            cl = 0
        if cl > int(app.state.max_request_bytes):
            from fastapi.responses import JSONResponse
            return JSONResponse(
                status_code=413,
                content={"detail": f"Request too large (max {int(app.state.max_request_bytes)} bytes)"},
            )

        if not _is_unlimited_path(path):
            # Global limiter (all protected/business endpoints)
            g_bucket = f"g:{ip}"
            if not _rate_allow(g_bucket, int(app.state.rate_limit_global_max), int(app.state.rate_limit_global_window)):
                from fastapi.responses import JSONResponse
                return JSONResponse(status_code=429, content={"detail": "Too many requests (global limit)"})

            # Additional strict limiter for sensitive endpoints
            sens = _sensitive_bucket_for_path(path)
            if sens is not None:
                sk, sm, sw = sens
                s_bucket = f"{sk}:{ip}"
                if not _rate_allow(s_bucket, int(sm), int(sw)):
                    from fastapi.responses import JSONResponse
                    return JSONResponse(status_code=429, content={"detail": f"Too many requests ({sk} limit)"})

        req_tok = _REQ_CTX.set(request)
        auth_tok = _AUTH_CTX.set(None)
        try:
            response = await call_next(request)
            _ = int((time.perf_counter() - t0) * 1000)
            return response
        except Exception:
            ms = int((time.perf_counter() - t0) * 1000)
            log.exception("%s %s %s -> EXCEPTION (%dms)", client, method, path, ms)
            raise
        finally:
            try:
                _REQ_CTX.reset(req_tok)
            except Exception:
                pass
            try:
                _AUTH_CTX.reset(auth_tok)
            except Exception:
                pass

    # -----------------------
    # WS broadcast
    # -----------------------
    ws_clients: set[WebSocket] = set()
    ws_lock = threading.Lock()

    def _extract_bearer_from_request() -> str:
        req = _REQ_CTX.get()
        if req is None:
            return ""
        try:
            authz = str(req.headers.get("Authorization") or "").strip()
        except Exception:
            return ""
        if not authz.lower().startswith("bearer "):
            return ""
        return authz.split(" ", 1)[1].strip()

    def _load_active_api_key_tenant(raw_key: str) -> Optional[dict]:
        rk = str(raw_key or "").strip()
        if not rk:
            return None
        kh = _api_key_hash(rk)
        now_ts = _jwt_now()
        con = _connect(db_path)
        try:
            row = con.execute(
                """
                SELECT id, tenant_id, location_id, scopes_json, active, expires_at, revoked_at
                FROM auth_api_keys
                WHERE key_hash=? AND active=1
                LIMIT 1
                """,
                (kh,),
            ).fetchone()
            if not row:
                return None
            if row["revoked_at"] is not None:
                return None
            ex = row["expires_at"]
            if ex is not None and int(ex) <= now_ts:
                return None
            scopes = []
            try:
                v = json.loads(row["scopes_json"] or "[]")
                if isinstance(v, list):
                    scopes = [str(x).strip() for x in v if str(x).strip()]
            except Exception:
                pass
            return {
                "kind": "api_key",
                "api_key_id": int(row["id"]),
                "tenant_id": str(row["tenant_id"] or "").strip(),
                "location_id": str(row["location_id"] or "").strip(),
                "scope": scopes,
                "sub": f"apikey:{int(row['id'])}",
            }
        finally:
            con.close()

    def _save_refresh_token(*, token_raw: str, tenant_id: str, client_id: str, subject: str, location_id: str, scopes: list[str], jti: str, exp_ts: int, rotated_from_hash: str = "") -> None:
        con = _connect(db_path)
        try:
            con.execute(
                """
                INSERT INTO auth_refresh_tokens(
                    token_hash, tenant_id, client_id, subject, location_id, scopes_json,
                    jti, issued_at, expires_at, revoked_at, rotated_from_hash, replaced_by_hash
                ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    hashlib.sha256(str(token_raw or "").encode("utf-8")).hexdigest(),
                    str(tenant_id or "").strip(),
                    str(client_id or "").strip(),
                    str(subject or "").strip(),
                    str(location_id or "").strip(),
                    json.dumps([str(x).strip() for x in (scopes or []) if str(x).strip()], ensure_ascii=False),
                    str(jti or "").strip(),
                    _jwt_now(),
                    int(exp_ts),
                    None,
                    str(rotated_from_hash or "").strip(),
                    "",
                ),
            )
            con.commit()
        finally:
            con.close()

    def _revoke_refresh_token(token_raw: str, replaced_by_hash: str = "") -> Optional[dict]:
        th = hashlib.sha256(str(token_raw or "").encode("utf-8")).hexdigest()
        con = _connect(db_path)
        try:
            row = con.execute(
                """
                SELECT id, tenant_id, client_id, subject, location_id, scopes_json, expires_at, revoked_at
                FROM auth_refresh_tokens
                WHERE token_hash=?
                LIMIT 1
                """,
                (th,),
            ).fetchone()
            if not row:
                return None
            if row["revoked_at"] is None:
                con.execute(
                    "UPDATE auth_refresh_tokens SET revoked_at=?, replaced_by_hash=? WHERE id=?",
                    (_jwt_now(), str(replaced_by_hash or "").strip(), int(row["id"])),
                )
                con.commit()
            scopes = []
            try:
                vv = json.loads(row["scopes_json"] or "[]")
                if isinstance(vv, list):
                    scopes = [str(x).strip() for x in vv if str(x).strip()]
            except Exception:
                pass
            return {
                "tenant_id": str(row["tenant_id"] or "").strip(),
                "client_id": str(row["client_id"] or "").strip(),
                "subject": str(row["subject"] or "").strip(),
                "location_id": str(row["location_id"] or "").strip(),
                "scope": scopes,
                "expires_at": int(row["expires_at"] or 0),
                "revoked_at": row["revoked_at"],
                "token_hash": th,
            }
        finally:
            con.close()

    def _auth(x_api_key: Optional[str]) -> dict:
        mode = _auth_mode()

        # 1) JWT path (enabled in hybrid/jwt_required)
        bearer = _extract_bearer_from_request()
        if mode in {"hybrid", "jwt_required"} and bearer:
            claims = _jwt_decode_and_validate(bearer)
            auth_obj = {
                "kind": "jwt",
                "tenant_id": str(claims.get("tenant_id") or "").strip(),
                "location_id": str(claims.get("location_id") or "").strip(),
                "sub": str(claims.get("sub") or "").strip(),
                "client_id": str(claims.get("client_id") or "").strip(),
                "scope": claims.get("scope") if isinstance(claims.get("scope"), list) else [],
                "claims": claims,
            }
            _AUTH_CTX.set(auth_obj)
            return auth_obj

        if mode == "jwt_required":
            raise HTTPException(status_code=401, detail="Bearer token required")

        # 2) API key path (api_key_only/hybrid)
        received_raw = x_api_key
        received = _norm_key(received_raw)
        expected = _norm_key(api_key)
        if received and received == expected:
            auth_obj = {"kind": "legacy_api_key", "tenant_id": "", "location_id": "", "sub": "legacy"}
            _AUTH_CTX.set(auth_obj)
            return auth_obj

        # 3) Per-tenant hashed API keys
        tkey_obj = _load_active_api_key_tenant(received)
        if tkey_obj is not None:
            _AUTH_CTX.set(tkey_obj)
            return tkey_obj

        if received != expected:
            log.warning(
                "AUTH FAIL: got header=%s len=%d mask=%s | expected len=%d mask=%s",
                "present" if received_raw is not None else "missing",
                len(received),
                _mask_key(received),
                len(expected),
                _mask_key(expected),
            )
            raise HTTPException(status_code=401, detail="Invalid or missing X-Api-Key")

        auth_obj = {"kind": "legacy_api_key", "tenant_id": "", "location_id": "", "sub": "legacy"}
        _AUTH_CTX.set(auth_obj)
        return auth_obj

    def _auth_context() -> dict:
        return dict(_AUTH_CTX.get() or {})

    def _enforce_tenant_access(
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        *,
        require_tenant_for_jwt: bool = True,
    ) -> None:
        a = _auth_context()
        kind = str(a.get("kind") or "")
        if kind == "legacy_api_key":
            return
        req_tid = str(tenant_id or "").strip()
        req_lid = str(location_id or "").strip()
        tok_tid = str(a.get("tenant_id") or "").strip()
        tok_lid = str(a.get("location_id") or "").strip()

        if kind == "jwt":
            if require_tenant_for_jwt and not tok_tid:
                raise HTTPException(status_code=403, detail="JWT missing tenant_id")
            if req_tid and tok_tid and req_tid != tok_tid:
                raise HTTPException(status_code=403, detail="Tenant isolation violation")
            if req_lid and tok_lid and req_lid != tok_lid:
                raise HTTPException(status_code=403, detail="Location isolation violation")
        elif kind == "api_key":
            if req_tid and tok_tid and req_tid != tok_tid:
                raise HTTPException(status_code=403, detail="Tenant isolation violation")
            if req_lid and tok_lid and req_lid != tok_lid:
                raise HTTPException(status_code=403, detail="Location isolation violation")

    async def _broadcast(msg: dict) -> None:
        dead = []
        with ws_lock:
            clients = list(ws_clients)
        for ws in clients:
            try:
                await ws.send_json(msg)
            except Exception:
                dead.append(ws)
        if dead:
            with ws_lock:
                for d in dead:
                    ws_clients.discard(d)

    # -----------------------
    # Shared parsers
    # -----------------------
    async def _read_payload_any(request: Request) -> dict:
        """
        Robust body parser:
        - JSON body
        - x-www-form-urlencoded (form)
        - query param ?body=<json> or ?payload=<json>
        - query param ?key=...&value=...
        """
        # 1) JSON
        try:
            data = await request.json()
            if isinstance(data, dict):
                return data
        except Exception:
            pass

        # 2) Form
        try:
            form = await request.form()
            if form:
                return dict(form)
        except Exception:
            pass

        # 3) Query fallback (JSON packed)
        qp = request.query_params.get("body") or request.query_params.get("payload")
        if qp:
            try:
                v = json.loads(qp)
                if isinstance(v, dict):
                    return v
            except Exception:
                pass

        # 4) Simple query params
        k = request.query_params.get("key")
        if k is not None:
            out = {"key": k}
            if "value" in request.query_params:
                out["value"] = request.query_params.get("value")
            return out

        return {}

    def _extract_name_list(v: Any) -> list[str]:
        out: list[str] = []

        def _add(s: str):
            ss = str(s or "").strip()
            if not ss:
                return
            if len(ss) >= 2 and ((ss[0] == ss[-1] == '"') or (ss[0] == ss[-1] == "'")):
                ss = ss[1:-1].strip()
            if ss and ss.lower() not in {"null", "none"}:
                out.append(ss)

        def _walk(x: Any):
            if x is None:
                return
            if isinstance(x, list):
                for it in x:
                    _walk(it)
                return
            if isinstance(x, dict):
                _walk(
                    x.get("name")
                    or x.get("title")
                    or x.get("label")
                    or x.get("ingredient")
                    or x.get("value")
                )
                return
            s = str(x).strip()
            if not s:
                return
            if s[:1] in {"{", "["}:
                try:
                    _walk(json.loads(s))
                    return
                except Exception:
                    m = re.search(r"(?:name|title|label|ingredient)\s*[:=]\s*([^,}\\]]+)", s, flags=re.IGNORECASE)
                    if m:
                        _add(m.group(1))
                        return
            _add(s)

        _walk(v)
        return out

    def _normalize_str_list(v: Any) -> list[str]:
        vals = _extract_name_list(v)
        out: list[str] = []
        seen = set()
        for it in vals:
            key = it.lower()
            if key in seen:
                continue
            seen.add(key)
            out.append(it)
        return out

    def _normalize_price_map(v: Any) -> dict[str, float]:
        if not isinstance(v, dict):
            return {}
        out: dict[str, float] = {}
        for k, val in v.items():
            key = str(k or "").strip()
            if not key:
                continue
            try:
                out[key] = float(val or 0)
            except Exception:
                continue
        return out

    def _normalize_sauce_options(v: Any) -> list[dict[str, Any]]:
        """
        Compatibility: older DB rows may store sauce arrays as plain strings,
        while Android expects objects: {"name": "...", "prices": {...}}.
        """
        if not isinstance(v, list):
            return []
        out: list[dict[str, Any]] = []
        for it in v:
            if isinstance(it, dict):
                nm = str(it.get("name") or it.get("label") or it.get("title") or "").strip()
                prices = _normalize_price_map(it.get("prices"))
                if nm:
                    out.append({"name": nm, "prices": prices})
                continue
            nm = str(it or "").strip()
            if nm:
                out.append({"name": nm, "prices": {}})
        return out

    def _normalize_named_price_items(v: Any) -> list[dict[str, Any]]:
        """
        Normalize addon payloads to a stable shape expected by Android:
        [{"name":"...", "prices": {...}}]
        """
        if not isinstance(v, list):
            return []
        out: list[dict[str, Any]] = []
        for it in v:
            if isinstance(it, dict):
                nm = str(
                    it.get("name")
                    or it.get("title")
                    or it.get("label")
                    or it.get("ingredient")
                    or it.get("sauce")
                    or ""
                ).strip()
                prices = _normalize_price_map(it.get("prices"))
                if nm:
                    out.append({"name": nm, "prices": prices})
                continue
            nm = str(it or "").strip()
            if nm:
                out.append({"name": nm, "prices": {}})
        return out

    # -----------------------
    # Menu list implementation (used by /menu and /api/menu)
    # -----------------------
    def _menu_list_impl(
        request: Request,
        since=None,
        main_category=None,
        sub_category=None,
        active_only=False,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
    ) -> dict:
        con = _connect(db_path)
        try:
            where = []
            params: list[Any] = []

            if since:
                where.append("updated_at > ?")
                params.append(since)
            if main_category is not None and str(main_category).strip() != "":
                where.append("main_category = ?")
                params.append(main_category)
            if sub_category is not None and str(sub_category).strip() != "":
                where.append("sub_category = ?")
                params.append(sub_category)
            if tenant_id is not None and str(tenant_id).strip() != "":
                where.append("tenant_id = ?")
                params.append(str(tenant_id).strip())
            if location_id is not None and str(location_id).strip() != "":
                where.append("location_id = ?")
                params.append(str(location_id).strip())
            if active_only:
                where.append("is_active = 1")

            sql = "SELECT * FROM menu_items"
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY name COLLATE NOCASE ASC"

            rows = con.execute(sql, tuple(params)).fetchall()

            out = []
            req_host = (request.url.hostname or "").strip().lower()
            is_local_req = (
                req_host == "localhost"
                or req_host.startswith("127.")
                or req_host.startswith("10.")
                or req_host.startswith("192.168.")
                or (req_host.startswith("172.") and any(req_host.startswith(f"172.{i}.") for i in range(16, 32)))
            )
            for r in rows:
                rd = dict(r)

                prices = _normalize_price_map(_json_loads(rd.get("prices_json"), {}))
                try:
                    p_small = float(prices.get("Small", 0) or 0)
                except Exception:
                    p_small = 0.0
                try:
                    p_large = float(prices.get("Large", 0) or 0)
                except Exception:
                    p_large = 0.0
                try:
                    p_family = float(prices.get("Family", 0) or 0)
                except Exception:
                    p_family = 0.0
                p_default = p_small
                if p_default <= 0:
                    try:
                        p_default = float(prices.get("default", 0) or 0)
                    except Exception:
                        p_default = 0.0
                if p_default <= 0:
                    for _v in (prices or {}).values():
                        try:
                            _fv = float(_v or 0)
                            if _fv > 0:
                                p_default = _fv
                                break
                        except Exception:
                            continue
                ingredients = _normalize_str_list(_json_loads(rd.get("ingredients_json"), []))
                default_ingredients = _json_loads(rd.get("default_ingredients_json"), None)
                image_local_abs = _coerce_image_url(request, rd.get("image_url_local") or rd.get("image_url"))
                image_online_abs = _coerce_image_url(request, rd.get("image_url_online"))
                if is_local_req:
                    # Local/LAN clients should get local image URLs first.
                    # _coerce_image_url() already rewrites localhost/127.* static links
                    # to the active request host, so Android on LAN can reach them.
                    image_abs = image_local_abs or image_online_abs
                    image_local_out = image_local_abs
                    # Android image loaders often reject self-signed HTTPS certs for static files.
                    # Keep API on HTTPS, but expose local static image links over HTTP if available.
                    image_abs = _force_http_static_url(request, image_abs)
                    image_local_out = _force_http_static_url(request, image_local_out)
                else:
                    image_abs = image_online_abs or image_local_abs
                    image_local_out = image_local_abs
                if default_ingredients is None:
                    default_ingredients = list(ingredients)
                else:
                    default_ingredients = _normalize_str_list(default_ingredients)

                available_sizes = _json_loads(rd.get("available_sizes_json"), None)
                if available_sizes is None:
                    available_sizes = list(prices.keys())
                else:
                    available_sizes = _normalize_str_list(available_sizes)

                sauce_prices = _normalize_price_map(_json_loads(rd.get("sauce_prices_json"), {}))
                selected_sauces = _normalize_sauce_options(_json_loads(rd.get("selected_sauces_json"), []))
                btn_sauce_on_item = _normalize_sauce_options(_json_loads(rd.get("btn_sauce_on_item_json"), []))
                btn_sauce_extra = _normalize_sauce_options(_json_loads(rd.get("btn_sauce_extra_json"), []))
                incl_sauce = _json_loads(rd.get("incl_sauce_json"), None)

                category = rd.get("category") or rd.get("sub_category") or rd.get("main_category") or ""
                stock_enum = (rd.get("stock_enum") or "QUANTITY").strip().upper()
                if stock_enum not in _ALLOWED_STOCK_ENUM:
                    stock_enum = "QUANTITY"

                item = {
                    "id": int(rd["id"]),
                    "name": rd.get("name") or "",
                    "articleNumber": rd.get("article_number") or "",
                    "imageUrl": image_abs or "",
                    "imageUrlLocal": image_local_out or "",
                    "imageUrlOnline": image_online_abs or "",
                    "prices": prices,
                    "ingredients": ingredients,
                    "defaultIngredients": default_ingredients,
                    "saucePrices": sauce_prices,
                    "selectedSauces": selected_sauces,
                    "btnSauceOnItem": btn_sauce_on_item,
                    "btnSauceExtra": btn_sauce_extra,
                    "inclSauce": incl_sauce,
                    "quantity": int(rd.get("quantity") or 1),
                    "category": category,
                    "availableSizes": available_sizes,
                    "hasFreeIngredients": bool(rd.get("has_free_ingredients") or 0),
                    "numberOfIngredients": int(rd.get("number_of_ingredients") or 0),
                    "hasFreeItem": bool(rd.get("has_free_item") or 0),
                    "stock": int(rd.get("stock") or 0),
                    "stockEnum": stock_enum,
                    "syncOnline": bool(1 if rd.get("sync_online") is None else rd.get("sync_online")),

                    # legacy keys
                    "article_number": rd.get("article_number"),
                    "main_category": rd.get("main_category"),
                    "sub_category": rd.get("sub_category"),
                    "image_url": image_abs,
                    "image_url_local": image_local_out,
                    "image_url_online": image_online_abs,
                    "is_active": bool(rd.get("is_active") or 0),
                    "updated_at": rd.get("updated_at"),
                    "barcode": (rd.get("barcode") or "").strip(),
                    "incl_sauce": incl_sauce,
                    "sync_online": bool(1 if rd.get("sync_online") is None else rd.get("sync_online")),
                    # compat for clients that still read flat price fields
                    "price": p_default,
                    "price_small": p_small,
                    "price_large": p_large,
                    "price_family": p_family,
                    "tenant_id": (rd.get("tenant_id") or "").strip(),
                    "location_id": (rd.get("location_id") or "").strip(),
                }
                out.append(item)

            return {"items": out}
        finally:
            con.close()

    # ==========================================================
    # /api router (KV + Menu + PDFs + RTDB)
    # ==========================================================
    from fastapi import APIRouter
    api = APIRouter(prefix="/api")

    backup_root = (dirs["DATA_DIR"] / "backups").resolve()
    backup_snapshots_dir = (backup_root / "snapshots").resolve()
    backup_snapshots_dir.mkdir(parents=True, exist_ok=True)

    def _safe_part(v: str, fallback: str = "x") -> str:
        s = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(v or "").strip())
        return s[:80] if s else fallback

    def _snapshot_file(name: str) -> Path:
        n = str(name or "").strip()
        if not n or len(n) > 180:
            raise HTTPException(status_code=400, detail="invalid snapshot name")
        if "/" in n or "\\" in n or ".." in n:
            raise HTTPException(status_code=400, detail="invalid snapshot name")
        if not n.lower().endswith(".zip"):
            raise HTTPException(status_code=400, detail="snapshot must be .zip")
        p = (backup_snapshots_dir / n).resolve()
        if p.parent != backup_snapshots_dir:
            raise HTTPException(status_code=400, detail="invalid snapshot path")
        return p

    def _snapshot_rows(limit: int = 50) -> list[dict]:
        lim = min(max(int(limit or 50), 1), 200)
        rows = []
        for p in backup_snapshots_dir.glob("*.zip"):
            try:
                st = p.stat()
                rows.append(
                    {
                        "name": p.name,
                        "size": int(st.st_size or 0),
                        "mtime": int(st.st_mtime or 0),
                        "updated_at": datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M:%S"),
                    }
                )
            except Exception:
                continue
        rows.sort(key=lambda x: int(x.get("mtime") or 0), reverse=True)
        return rows[:lim]

    @api.post("/backup/upload_snapshot")
    async def api_backup_upload_snapshot(
        snapshot: UploadFile = File(...),
        reason: str = Form(default="manual"),
        source_host: str = Form(default=""),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        if not snapshot:
            raise HTTPException(status_code=400, detail="snapshot file required")

        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        host = _safe_part(source_host or "pc", "pc")
        rsn = _safe_part(reason or "manual", "manual")
        uniq = uuid.uuid4().hex[:8]
        out_name = f"{ts}_{host}_{rsn}_{uniq}.zip"
        out_path = _snapshot_file(out_name)

        total = 0
        try:
            with open(out_path, "wb") as f:
                while True:
                    chunk = await snapshot.read(1024 * 1024)
                    if not chunk:
                        break
                    total += len(chunk)
                    if total > (1024 * 1024 * 1024):  # 1GB guard
                        raise HTTPException(status_code=413, detail="snapshot too large")
                    f.write(chunk)
        except HTTPException:
            try:
                if out_path.exists():
                    out_path.unlink()
            except Exception:
                pass
            raise
        except Exception as e:
            try:
                if out_path.exists():
                    out_path.unlink()
            except Exception:
                pass
            raise HTTPException(status_code=500, detail=f"upload failed: {e}")

        meta = {
            "name": out_name,
            "path": f"backups/snapshots/{out_name}",
            "size": int(total),
            "updated_at": _now(),
            "reason": rsn,
            "source_host": host,
        }
        try:
            (backup_root / "latest_snapshot.json").write_text(
                json.dumps(meta, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
        except Exception:
            pass

        return {"ok": True, **meta}

    @api.get("/backup/list_snapshots")
    def api_backup_list_snapshots(
        limit: int = 50,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        rows = _snapshot_rows(limit=limit)
        return {"ok": True, "count": len(rows), "items": rows}

    @api.get("/backup/download_snapshot")
    def api_backup_download_snapshot(
        name: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ):
        _auth(x_api_key)
        chosen: Optional[Path] = None
        if name:
            p = _snapshot_file(name)
            if not p.exists():
                raise HTTPException(status_code=404, detail="snapshot not found")
            chosen = p
        else:
            rows = _snapshot_rows(limit=1)
            if not rows:
                raise HTTPException(status_code=404, detail="no snapshots found")
            chosen = _snapshot_file(str(rows[0].get("name") or ""))
            if not chosen.exists():
                raise HTTPException(status_code=404, detail="snapshot not found")

        return FileResponse(
            path=str(chosen),
            filename=chosen.name,
            media_type="application/zip",
        )

    @api.get("/backup/download_shared_only")
    def api_backup_download_shared_only(
        request: Request,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        menu = (_menu_list_impl(request, None, None, None, False) or {}).get("items") or []
        ingredients = _catalog_rows("ingredients_catalog", None, False, None)
        sauces = _catalog_rows("sauces_catalog", None, False, None)

        shared_keys = [
            "store_opening_settings",
            "employees_public",
            "tse_settings",
            "receipt_profile",
        ]
        kv: dict[str, Any] = {}
        con = _connect(db_path)
        try:
            for k in shared_keys:
                row = con.execute("SELECT value FROM pos_kv WHERE key=? LIMIT 1", (k,)).fetchone()
                if not row:
                    continue
                raw = str(row["value"] or "")
                if not raw:
                    continue
                try:
                    kv[k] = json.loads(raw)
                except Exception:
                    kv[k] = raw
        finally:
            con.close()

        return {
            "ok": True,
            "updated_at": _now(),
            "payload": {
                "menu_items": menu,
                "ingredients_catalog": ingredients,
                "sauces_catalog": sauces,
                "kv_shared": kv,
            },
            "counts": {
                "menu_items": len(menu),
                "ingredients_catalog": len(ingredients),
                "sauces_catalog": len(sauces),
                "kv_shared": len(kv),
            },
        }

    # -------------------
    # /api/kv  (GET/POST)
    # -------------------
    def _kv_get_with_fallback(key: str, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> Any:
        k = (key or "").strip()
        k_scoped = _scoped_kv_key(k, tenant_id, location_id)
        con = _connect(db_path)
        try:
            row = con.execute("SELECT value FROM pos_kv WHERE key=?", (k_scoped,)).fetchone()
            if not row and (str(tenant_id or "").strip() or str(location_id or "").strip()):
                row = con.execute("SELECT value FROM pos_kv WHERE key=?", (k,)).fetchone()
            raw = (row["value"] or "") if row else ""
        finally:
            con.close()

        parsed: Any = None
        has_parsed = False
        if raw:
            try:
                parsed = json.loads(raw)
                has_parsed = True
            except Exception:
                parsed = {"value": raw}
                has_parsed = True

        # Android expects employee payload in KV key employees_public.
        # If KV is missing/empty/stale, serve it directly from Employes tables.
        if k in ("employees_public", "employees"):
            needs_fallback = not has_parsed
            if isinstance(parsed, dict):
                items = parsed.get("items")
                if not isinstance(items, list) or len(items) == 0:
                    needs_fallback = True
            if needs_fallback:
                emps = _list_employees_basic(active_only=True)
                if emps:
                    # Keep exact Android contract from doku: items + count only.
                    return {"items": emps, "count": len(emps)}

        if has_parsed:
            return parsed
        return {}

    @api.get("/kv/{key}")
    def api_kv_get(
        key: str,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> Any:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        return _kv_get_with_fallback(key, tenant_id, location_id)

    @api.post("/kv")
    async def api_kv_set(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)

        key = (payload.get("key") or "").strip()
        if not key:
            raise HTTPException(status_code=400, detail="JSON body must contain 'key'")
        tenant_id = (payload.get("tenant_id") or payload.get("tenantId") or "").strip()
        location_id = (payload.get("location_id") or payload.get("locationId") or "").strip()
        _enforce_tenant_access(tenant_id, location_id)
        key_db = _scoped_kv_key(key, tenant_id, location_id)

        value = payload.get("value", {})

        # Store as JSON string consistently
        if isinstance(value, str):
            s = value.strip()
            if s:
                try:
                    json.loads(s)
                    stored = s
                except Exception:
                    stored = json.dumps(value, ensure_ascii=False)
            else:
                stored = json.dumps("", ensure_ascii=False)
        else:
            stored = json.dumps(value, ensure_ascii=False)

        con = _connect(db_path)
        try:
            con.execute(
                "INSERT INTO pos_kv(key,value,updated_at) VALUES(?,?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
                (key_db, stored, _now()),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(
            db_path,
            "kv.updated",
            {"key": key, "tenant_id": tenant_id, "location_id": location_id},
        )
        try:
            import anyio
            anyio.from_thread.run(
                _broadcast,
                {
                    "type": "kv.updated",
                    "seq": seq,
                    "key": key,
                    "tenant_id": tenant_id,
                    "location_id": location_id,
                },
            )
        except Exception:
            pass

        return {"ok": True, "seq": seq, "key": key, "tenant_id": tenant_id, "location_id": location_id}

    # ---------------------
    # /api/menu (GET/POST/PUT/DELETE)
    # ---------------------
    @api.get("/menu")
    def api_menu_list(
        request: Request,
        since: Optional[str] = None,
        main_category: Optional[str] = None,
        sub_category: Optional[str] = None,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        active_only: bool = False,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        return _menu_list_impl(request, since, main_category, sub_category, active_only, tenant_id, location_id)

    @api.get("/ingredients-catalog")
    def api_ingredients_catalog_list(
        main_category: Optional[str] = None,
        active_only: bool = True,
        q: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        rows = _catalog_rows("ingredients_catalog", main_category, active_only, q)
        return {"items": rows, "count": len(rows)}

    @api.post("/ingredients-catalog")
    async def api_ingredients_catalog_create(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)
        body = CatalogItem.model_validate(payload or {})
        return _catalog_upsert("ingredients_catalog", body, item_id=None)

    @api.put("/ingredients-catalog/{item_id}")
    async def api_ingredients_catalog_update(item_id: int, request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)
        body = CatalogItem.model_validate(payload or {})
        return _catalog_upsert("ingredients_catalog", body, item_id=int(item_id))

    @api.delete("/ingredients-catalog/{item_id}")
    def api_ingredients_catalog_delete(item_id: int, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return _catalog_soft_delete("ingredients_catalog", int(item_id))

    @api.get("/sauces-catalog")
    def api_sauces_catalog_list(
        main_category: Optional[str] = None,
        active_only: bool = True,
        q: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        rows = _catalog_rows("sauces_catalog", main_category, active_only, q)
        return {"items": rows, "count": len(rows)}

    @api.post("/sauces-catalog")
    async def api_sauces_catalog_create(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)
        body = CatalogItem.model_validate(payload or {})
        return _catalog_upsert("sauces_catalog", body, item_id=None)

    @api.put("/sauces-catalog/{item_id}")
    async def api_sauces_catalog_update(item_id: int, request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)
        body = CatalogItem.model_validate(payload or {})
        return _catalog_upsert("sauces_catalog", body, item_id=int(item_id))

    @api.delete("/sauces-catalog/{item_id}")
    def api_sauces_catalog_delete(item_id: int, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return _catalog_soft_delete("sauces_catalog", int(item_id))

    @api.post("/menu")
    async def api_menu_create(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)
        if not payload:
            raise HTTPException(status_code=400, detail="JSON body required")

        body = MenuItem.model_validate(payload)
        _enforce_tenant_access(body.tenant_id, body.location_id)
        body.article_number = _normalize_article_number(body.article_number)
        barcode = _normalize_barcode(getattr(body, "barcode", None))

        stock_enum = (body.stock_enum or "QUANTITY").strip().upper()
        if stock_enum not in _ALLOWED_STOCK_ENUM:
            stock_enum = "QUANTITY"

        default_ingredients = body.default_ingredients or list(body.ingredients or [])
        available_sizes = body.available_sizes or list((body.prices or {}).keys())
        category = (body.category or body.sub_category or body.main_category or "").strip()

        con = _connect(db_path)
        ts = _now()
        try:
            _ensure_menu_columns(con)
            cur = con.cursor()
            incl_sauce = _resolve_incl_sauce(con, body.main_category, body.incl_sauce)
            incl_sauce_db = None if incl_sauce is None else _json_dumps(incl_sauce)
            img_local = (body.image_url_local or "").strip()
            img_online = (body.image_url_online or "").strip()
            img_primary = (body.image_url or "").strip() or img_local or img_online

            # Unique barcode (if provided)
            if barcode is not None:
                exists_bc = con.execute("SELECT 1 FROM menu_items WHERE barcode=? LIMIT 1", (barcode,)).fetchone()
                if exists_bc:
                    raise HTTPException(status_code=409, detail="barcode already exists")

            article_number = _ensure_unique_article_number(con, body.article_number)

            try:
                cur.execute(
                    """
                    INSERT INTO menu_items(
                        tenant_id, location_id,
                        article_number, barcode, name, main_category, sub_category,
                        prices_json, ingredients_json, default_ingredients_json,
                        sauce_prices_json, selected_sauces_json, btn_sauce_on_item_json, btn_sauce_extra_json, incl_sauce_json,
                        quantity, category, available_sizes_json,
                        has_free_ingredients, number_of_ingredients,
                        has_free_item, stock, stock_enum,
                        image_url, image_url_local, image_url_online, sync_online, is_active, updated_at
                    )
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        (body.tenant_id or "").strip(),
                        (body.location_id or "").strip(),
                        article_number,
                        barcode,
                        body.name,
                        body.main_category,
                        body.sub_category,
                        _json_dumps(body.prices),
                        _json_dumps(body.ingredients),
                        _json_dumps(default_ingredients),
                        _json_dumps(body.sauce_prices),
                        _json_dumps(body.selected_sauces),
                        _json_dumps(body.btn_sauce_on_item),
                        _json_dumps(body.btn_sauce_extra),
                        incl_sauce_db,
                        int(body.quantity or 1),
                        category,
                        _json_dumps(available_sizes),
                        1 if body.has_free_ingredients else 0,
                        int(body.number_of_ingredients),
                        1 if body.has_free_item else 0,
                        int(body.stock or 0),
                        stock_enum,
                        img_primary,
                        img_local,
                        img_online,
                        1 if body.sync_online else 0,
                        1 if body.is_active else 0,
                        ts,
                    ),
                )
            except sqlite3.IntegrityError as e:
                msg = str(e).lower()
                if "barcode" in msg:
                    raise HTTPException(status_code=409, detail="barcode already exists")
                # assume article_number collision -> retry
                article_number = _menu_next_article_number(con)
                cur.execute(
                    """
                    INSERT INTO menu_items(
                        tenant_id, location_id,
                        article_number, barcode, name, main_category, sub_category,
                        prices_json, ingredients_json, default_ingredients_json,
                        sauce_prices_json, selected_sauces_json, btn_sauce_on_item_json, btn_sauce_extra_json, incl_sauce_json,
                        quantity, category, available_sizes_json,
                        has_free_ingredients, number_of_ingredients,
                        has_free_item, stock, stock_enum,
                        image_url, image_url_local, image_url_online, sync_online, is_active, updated_at
                    )
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        (body.tenant_id or "").strip(),
                        (body.location_id or "").strip(),
                        article_number,
                        barcode,
                        body.name,
                        body.main_category,
                        body.sub_category,
                        _json_dumps(body.prices),
                        _json_dumps(body.ingredients),
                        _json_dumps(default_ingredients),
                        _json_dumps(body.sauce_prices),
                        _json_dumps(body.selected_sauces),
                        _json_dumps(body.btn_sauce_on_item),
                        _json_dumps(body.btn_sauce_extra),
                        incl_sauce_db,
                        int(body.quantity or 1),
                        category,
                        _json_dumps(available_sizes),
                        1 if body.has_free_ingredients else 0,
                        int(body.number_of_ingredients),
                        1 if body.has_free_item else 0,
                        int(body.stock or 0),
                        stock_enum,
                        img_primary,
                        img_local,
                        img_online,
                        1 if body.sync_online else 0,
                        1 if body.is_active else 0,
                        ts,
                    ),
                )

            con.commit()
            new_id = int(cur.lastrowid)
        finally:
            con.close()

        seq = _emit_event(db_path, "menu.created", {"id": new_id})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "menu.created", "seq": seq, "id": new_id})
        except Exception:
            pass

        return {"ok": True, "id": new_id, "seq": seq, "article_number": article_number, "barcode": barcode or ""}

    @api.post("/menu/upload_image")
    async def api_menu_upload_image(
        request: Request,
        file: UploadFile = File(...),
        category: str = Form("all"),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)

        original = os.path.basename((file.filename or "").strip() or "image.png")
        ext = os.path.splitext(original)[1].lower()
        if ext not in (".png", ".jpg", ".jpeg", ".webp"):
            ext = ".png"

        # Store all shared media in global_gallery/<category>/...
        # Keep menu_images only for backward compatibility with older data.
        cat_raw = str(category or "all").strip().lower()
        cat_safe = re.sub(r"[^a-z0-9_\-]+", "_", cat_raw).strip("_") or "all"
        gallery_root = Path(POS_HUB_GLOBAL_GALLERY_DIR)
        out_dir = (gallery_root / cat_safe).resolve()
        out_dir.mkdir(parents=True, exist_ok=True)
        out_name = f"{uuid.uuid4().hex}{ext}"
        out_path = (out_dir / out_name).resolve()

        try:
            with open(out_path, "wb") as f:
                while True:
                    chunk = await file.read(1024 * 1024)
                    if not chunk:
                        break
                    f.write(chunk)
        finally:
            try:
                await file.close()
            except Exception:
                pass

        rel_url = f"/static/global_gallery/{cat_safe}/{out_name}"
        abs_url = _coerce_image_url(request, rel_url)
        return {
            "ok": True,
            "filename": out_name,
            "category": cat_safe,
            "image_url": abs_url,
            "image_url_rel": rel_url,
        }

    @api.get("/gallery/list")
    def api_gallery_list(
        request: Request,
        category: str = "all",
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        cat = re.sub(r"[^a-z0-9_\-]+", "_", str(category or "all").strip().lower()).strip("_") or "all"
        files = []
        if cat == "all":
            for p in root.rglob("*"):
                if not p.is_file():
                    continue
                ext = p.suffix.lower()
                if ext not in (".png", ".jpg", ".jpeg", ".webp"):
                    continue
                rel = p.relative_to(root).as_posix()
                rel_url = f"/static/global_gallery/{rel}"
                files.append(
                    {
                        "name": p.name,
                        "category": str(p.parent.relative_to(root).as_posix() or "all"),
                        "rel_path": rel,
                        "url": _coerce_image_url(request, rel_url),
                        "size": int(p.stat().st_size if p.exists() else 0),
                    }
                )
        else:
            cat_dir = (root / cat).resolve()
            if cat_dir.exists():
                for p in cat_dir.glob("*"):
                    if not p.is_file():
                        continue
                    ext = p.suffix.lower()
                    if ext not in (".png", ".jpg", ".jpeg", ".webp"):
                        continue
                    rel = p.relative_to(root).as_posix()
                    rel_url = f"/static/global_gallery/{rel}"
                    files.append(
                        {
                            "name": p.name,
                            "category": cat,
                            "rel_path": rel,
                            "url": _coerce_image_url(request, rel_url),
                            "size": int(p.stat().st_size if p.exists() else 0),
                        }
                    )
        files.sort(key=lambda x: (str(x.get("category") or ""), str(x.get("name") or "")))
        return {"ok": True, "category": cat, "count": len(files), "items": files}

    @api.get("/gallery/categories")
    def api_gallery_categories(
        request: Request,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        root.mkdir(parents=True, exist_ok=True)
        out = []
        for p in root.iterdir():
            if not p.is_dir():
                continue
            cnt = 0
            for f in p.glob("*"):
                if f.is_file() and f.suffix.lower() in (".png", ".jpg", ".jpeg", ".webp"):
                    cnt += 1
            out.append({"name": p.name, "count": cnt})
        out.sort(key=lambda x: str(x.get("name") or "").lower())
        if not any(str(x.get("name") or "") == "all" for x in out):
            out.insert(0, {"name": "all", "count": 0})
        return {"ok": True, "items": out}

    @api.post("/gallery/categories")
    def api_gallery_category_create(
        request: Request,
        name: str = Form(...),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        cat = re.sub(r"[^a-z0-9_\-]+", "_", str(name or "").strip().lower()).strip("_")
        if not cat:
            raise HTTPException(status_code=400, detail="invalid category")
        d = (root / cat).resolve()
        d.mkdir(parents=True, exist_ok=True)
        return {"ok": True, "name": cat}

    @api.delete("/gallery/categories")
    def api_gallery_category_delete(
        request: Request,
        name: str,
        move_to: str = "all",
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        cat = re.sub(r"[^a-z0-9_\-]+", "_", str(name or "").strip().lower()).strip("_")
        mv = re.sub(r"[^a-z0-9_\-]+", "_", str(move_to or "all").strip().lower()).strip("_") or "all"
        if not cat:
            raise HTTPException(status_code=400, detail="invalid category")
        if cat == mv:
            raise HTTPException(status_code=400, detail="name and move_to must differ")
        src = (root / cat).resolve()
        if not src.exists() or not src.is_dir():
            raise HTTPException(status_code=404, detail="category not found")
        dst = (root / mv).resolve()
        dst.mkdir(parents=True, exist_ok=True)
        moved = 0
        for f in src.glob("*"):
            if not f.is_file():
                continue
            if f.suffix.lower() not in (".png", ".jpg", ".jpeg", ".webp"):
                continue
            target = (dst / f.name).resolve()
            if target.exists():
                target = (dst / f"{f.stem}_{uuid.uuid4().hex[:8]}{f.suffix}").resolve()
            shutil.move(str(f), str(target))
            moved += 1
        try:
            src.rmdir()
        except Exception:
            pass
        return {"ok": True, "deleted": cat, "moved_to": mv, "moved_count": moved}

    @api.post("/gallery/move")
    def api_gallery_move(
        request: Request,
        rel_path: str = Form(...),
        new_category: str = Form(...),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        safe_rel = str(rel_path or "").strip().replace("\\", "/").lstrip("/")
        if not safe_rel or ".." in safe_rel:
            raise HTTPException(status_code=400, detail="invalid rel_path")
        src = (root / safe_rel).resolve()
        if not str(src).startswith(str(root)):
            raise HTTPException(status_code=400, detail="invalid rel_path")
        if not src.exists() or not src.is_file():
            raise HTTPException(status_code=404, detail="file not found")
        cat = re.sub(r"[^a-z0-9_\-]+", "_", str(new_category or "all").strip().lower()).strip("_") or "all"
        dst_dir = (root / cat).resolve()
        dst_dir.mkdir(parents=True, exist_ok=True)
        dst = (dst_dir / src.name).resolve()
        if str(dst) == str(src):
            return {"ok": True, "rel_path": safe_rel}
        if dst.exists():
            stem = src.stem
            ext = src.suffix
            dst = (dst_dir / f"{stem}_{uuid.uuid4().hex[:8]}{ext}").resolve()
        shutil.move(str(src), str(dst))
        new_rel = dst.relative_to(root).as_posix()
        return {"ok": True, "rel_path": new_rel}

    @api.delete("/gallery/item")
    def api_gallery_delete(
        request: Request,
        rel_path: str,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        safe_rel = str(rel_path or "").strip().replace("\\", "/").lstrip("/")
        if not safe_rel or ".." in safe_rel:
            raise HTTPException(status_code=400, detail="invalid rel_path")
        p = (root / safe_rel).resolve()
        if not str(p).startswith(str(root)):
            raise HTTPException(status_code=400, detail="invalid rel_path")
        if not p.exists() or not p.is_file():
            raise HTTPException(status_code=404, detail="file not found")
        p.unlink(missing_ok=False)
        return {"ok": True}

    @api.post("/gallery/delete_many")
    async def api_gallery_delete_many(
        request: Request,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        payload = await _read_payload_any(request)
        rels = payload.get("rel_paths") if isinstance(payload, dict) else None
        if not isinstance(rels, list):
            raise HTTPException(status_code=400, detail="rel_paths list required")
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        ok = 0
        fail = 0
        for raw in rels:
            try:
                safe_rel = str(raw or "").strip().replace("\\", "/").lstrip("/")
                if not safe_rel or ".." in safe_rel:
                    fail += 1
                    continue
                p = (root / safe_rel).resolve()
                if not str(p).startswith(str(root)) or (not p.exists()) or (not p.is_file()):
                    fail += 1
                    continue
                p.unlink(missing_ok=False)
                ok += 1
            except Exception:
                fail += 1
        return {"ok": True, "deleted": ok, "failed": fail}

    @api.post("/gallery/move_many")
    async def api_gallery_move_many(
        request: Request,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth_gallery_admin(request, x_api_key)
        payload = await _read_payload_any(request)
        rels = payload.get("rel_paths") if isinstance(payload, dict) else None
        nc = payload.get("new_category") if isinstance(payload, dict) else None
        if not isinstance(rels, list) or not rels:
            raise HTTPException(status_code=400, detail="rel_paths list required")
        cat = re.sub(r"[^a-z0-9_\-]+", "_", str(nc or "all").strip().lower()).strip("_") or "all"
        root = Path(POS_HUB_GLOBAL_GALLERY_DIR).resolve()
        dst_dir = (root / cat).resolve()
        dst_dir.mkdir(parents=True, exist_ok=True)
        moved = 0
        failed = 0
        for raw in rels:
            try:
                safe_rel = str(raw or "").strip().replace("\\", "/").lstrip("/")
                if not safe_rel or ".." in safe_rel:
                    failed += 1
                    continue
                src = (root / safe_rel).resolve()
                if not str(src).startswith(str(root)) or (not src.exists()) or (not src.is_file()):
                    failed += 1
                    continue
                dst = (dst_dir / src.name).resolve()
                if dst.exists():
                    dst = (dst_dir / f"{src.stem}_{uuid.uuid4().hex[:8]}{src.suffix}").resolve()
                shutil.move(str(src), str(dst))
                moved += 1
            except Exception:
                failed += 1
        return {"ok": True, "moved": moved, "failed": failed, "category": cat}

    @api.put("/menu/{item_id}")
    async def api_menu_update(item_id: int, request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        payload = await _read_payload_any(request)
        if not payload:
            raise HTTPException(status_code=400, detail="JSON body required")

        body = MenuItem.model_validate(payload)
        body.article_number = _normalize_article_number(body.article_number)
        barcode = _normalize_barcode(getattr(body, "barcode", None))

        stock_enum = (body.stock_enum or "QUANTITY").strip().upper()
        if stock_enum not in _ALLOWED_STOCK_ENUM:
            stock_enum = "QUANTITY"

        default_ingredients = body.default_ingredients or list(body.ingredients or [])
        available_sizes = body.available_sizes or list((body.prices or {}).keys())
        category = (body.category or body.sub_category or body.main_category or "").strip()

        con = _connect(db_path)
        ts = _now()
        try:
            _ensure_menu_columns(con)
            incl_sauce = _resolve_incl_sauce(con, body.main_category, body.incl_sauce)
            incl_sauce_db = None if incl_sauce is None else _json_dumps(incl_sauce)
            prev = con.execute(
                "SELECT image_url, image_url_local, image_url_online, tenant_id, location_id FROM menu_items WHERE id=? LIMIT 1",
                (int(item_id),),
            ).fetchone()
            if not prev:
                raise HTTPException(status_code=404, detail="Menu item not found")
            prev_d = dict(prev)
            img_local = (body.image_url_local if body.image_url_local is not None else prev_d.get("image_url_local") or "").strip()
            img_online = (body.image_url_online if body.image_url_online is not None else prev_d.get("image_url_online") or "").strip()
            img_primary = (body.image_url if body.image_url is not None else prev_d.get("image_url") or "").strip()
            if not img_primary:
                img_primary = img_local or img_online
            tenant_id_eff = (body.tenant_id if body.tenant_id is not None else prev_d.get("tenant_id") or "").strip()
            location_id_eff = (body.location_id if body.location_id is not None else prev_d.get("location_id") or "").strip()
            _enforce_tenant_access(tenant_id_eff, location_id_eff)

            # Unique article_number
            if body.article_number is not None:
                exists = con.execute(
                    "SELECT id FROM menu_items WHERE article_number=? AND id<>? LIMIT 1",
                    (body.article_number, int(item_id)),
                ).fetchone()
                if exists:
                    raise HTTPException(status_code=409, detail="article_number already exists")

            # Unique barcode (if provided)
            if barcode is not None:
                exists_bc = con.execute(
                    "SELECT id FROM menu_items WHERE barcode=? AND id<>? LIMIT 1",
                    (barcode, int(item_id)),
                ).fetchone()
                if exists_bc:
                    raise HTTPException(status_code=409, detail="barcode already exists")

            cur = con.cursor()
            cur.execute(
                """
                UPDATE menu_items
                SET article_number=?,
                    barcode=?,
                    name=?,
                    main_category=?,
                    sub_category=?,
                    prices_json=?,
                    ingredients_json=?,
                    default_ingredients_json=?,
                    sauce_prices_json=?,
                    selected_sauces_json=?,
                    btn_sauce_on_item_json=?,
                    btn_sauce_extra_json=?,
                    incl_sauce_json=?,
                    quantity=?,
                    category=?,
                    available_sizes_json=?,
                    has_free_ingredients=?,
                    number_of_ingredients=?,
                    has_free_item=?,
                    stock=?,
                    stock_enum=?,
                    image_url=?,
                    image_url_local=?,
                    image_url_online=?,
                    sync_online=?,
                    is_active=?,
                    updated_at=?,
                    tenant_id=?,
                    location_id=?
                WHERE id = ?
                """,
                (
                    body.article_number,
                    barcode,
                    body.name,
                    body.main_category,
                    body.sub_category,
                    _json_dumps(body.prices),
                    _json_dumps(body.ingredients),
                    _json_dumps(default_ingredients),
                    _json_dumps(body.sauce_prices),
                    _json_dumps(body.selected_sauces),
                    _json_dumps(body.btn_sauce_on_item),
                    _json_dumps(body.btn_sauce_extra),
                    incl_sauce_db,
                    int(body.quantity or 1),
                    category,
                    _json_dumps(available_sizes),
                    1 if body.has_free_ingredients else 0,
                    int(body.number_of_ingredients),
                    1 if body.has_free_item else 0,
                    int(body.stock or 0),
                    stock_enum,
                    img_primary,
                    img_local,
                    img_online,
                    1 if body.sync_online else 0,
                    1 if body.is_active else 0,
                    ts,
                    tenant_id_eff,
                    location_id_eff,
                    int(item_id),
                ),
            )

            if cur.rowcount == 0:
                raise HTTPException(status_code=404, detail="Menu item not found")

            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "menu.updated", {"id": int(item_id)})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "menu.updated", "seq": seq, "id": int(item_id)})
        except Exception:
            pass

        return {"ok": True, "seq": seq}

    @api.delete("/menu/{item_id}")
    def api_menu_delete(item_id: int, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        con = _connect(db_path)
        ts = _now()
        try:
            cur = con.cursor()
            cur.execute("UPDATE menu_items SET is_active=0, updated_at=? WHERE id=?", (ts, int(item_id)))
            if cur.rowcount == 0:
                raise HTTPException(status_code=404, detail="Menu item not found")
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "menu.deleted", {"id": int(item_id)})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "menu.deleted", "seq": seq, "id": int(item_id)})
        except Exception:
            pass

        return {"ok": True, "seq": seq}

    # ==========================================================
    # Android addon customization datasets
    # ==========================================================
    _ADDON_KV_KEYS = {
        "extra-ingredients": {
            "global": "addon_extra_ingredients_global",
            "by_item": "addon_extra_ingredients_by_item",
        },
        "sauce-on-item": {
            "global": "addon_sauce_on_item_global",
            "by_item": "addon_sauce_on_item_by_item",
        },
        "extra-sauce": {
            "global": "addon_extra_sauce_global",
            "by_item": "addon_extra_sauce_by_item",
        },
    }

    def _kv_read_json(key: str, default):
        con = _connect(db_path)
        try:
            row = con.execute("SELECT value FROM pos_kv WHERE key=? LIMIT 1", ((key or "").strip(),)).fetchone()
            if not row:
                return default
            raw = row["value"] or ""
            try:
                return json.loads(raw)
            except Exception:
                return default
        finally:
            con.close()

    def _catalog_rows(table: str, main_category: Optional[str], active_only: bool, q: Optional[str]) -> list[dict]:
        con = _connect(db_path)
        try:
            where = []
            params: list[Any] = []
            if main_category is not None and str(main_category).strip():
                where.append("main_category = ?")
                params.append(str(main_category).strip())
            if active_only:
                where.append("is_active = 1")
            if q:
                where.append("LOWER(name) LIKE ?")
                params.append(f"%{str(q).strip().lower()}%")

            sql = f"SELECT id,name,main_category,prices_json,is_active,updated_at FROM {table}"
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY main_category COLLATE NOCASE ASC, name COLLATE NOCASE ASC"

            rows = con.execute(sql, tuple(params)).fetchall()
            out = []
            for r in rows:
                out.append({
                    "id": int(r["id"]),
                    "name": (r["name"] or "").strip(),
                    "mainCategory": (r["main_category"] or "").strip(),
                    "main_category": (r["main_category"] or "").strip(),
                    "prices": _json_loads(r["prices_json"], {}),
                    "isActive": bool(r["is_active"] or 0),
                    "is_active": bool(r["is_active"] or 0),
                    "updated_at": r["updated_at"],
                })
            return out
        finally:
            con.close()

    def _catalog_upsert(table: str, payload: CatalogItem, item_id: Optional[int] = None) -> dict:
        con = _connect(db_path)
        ts = _now()
        name = (payload.name or "").strip()
        main_cat = (payload.main_category or "").strip()
        if not name or not main_cat:
            raise HTTPException(status_code=400, detail="name and mainCategory are required")
        try:
            cur = con.cursor()
            if item_id is None:
                cur.execute(
                    f"""
                    INSERT INTO {table}(name, main_category, prices_json, is_active, updated_at)
                    VALUES(?,?,?,?,?)
                    ON CONFLICT(name, main_category)
                    DO UPDATE SET prices_json=excluded.prices_json, is_active=excluded.is_active, updated_at=excluded.updated_at
                    """,
                    (name, main_cat, _json_dumps(payload.prices or {}), 1 if payload.is_active else 0, ts),
                )
                row = con.execute(
                    f"SELECT id FROM {table} WHERE name=? AND main_category=? LIMIT 1",
                    (name, main_cat),
                ).fetchone()
                saved_id = int(row["id"]) if row else int(cur.lastrowid or 0)
            else:
                cur.execute(
                    f"""
                    UPDATE {table}
                    SET name=?, main_category=?, prices_json=?, is_active=?, updated_at=?
                    WHERE id=?
                    """,
                    (name, main_cat, _json_dumps(payload.prices or {}), 1 if payload.is_active else 0, ts, int(item_id)),
                )
                if cur.rowcount == 0:
                    raise HTTPException(status_code=404, detail="Catalog item not found")
                saved_id = int(item_id)
            con.commit()
            return {"ok": True, "id": saved_id, "updated_at": ts}
        finally:
            con.close()

    def _catalog_soft_delete(table: str, item_id: int) -> dict:
        con = _connect(db_path)
        ts = _now()
        try:
            cur = con.cursor()
            cur.execute(f"UPDATE {table} SET is_active=0, updated_at=? WHERE id=?", (ts, int(item_id)))
            if cur.rowcount == 0:
                raise HTTPException(status_code=404, detail="Catalog item not found")
            con.commit()
            return {"ok": True, "id": int(item_id), "updated_at": ts}
        finally:
            con.close()

    def _resolve_incl_sauce(con: sqlite3.Connection, main_category: Optional[str], incl_sauce_value: Any) -> Optional[dict]:
        if incl_sauce_value in (None, "", {}):
            return None

        menu_main = (main_category or "").strip()
        sauce_id = None
        sauce_name = None
        if isinstance(incl_sauce_value, dict):
            try:
                sauce_id = int(incl_sauce_value.get("id")) if incl_sauce_value.get("id") is not None else None
            except Exception:
                sauce_id = None
            sauce_name = str(incl_sauce_value.get("name") or "").strip()
        elif isinstance(incl_sauce_value, str):
            sauce_name = incl_sauce_value.strip()
        else:
            raise HTTPException(status_code=400, detail="inclSauce must be object or string")

        row = None
        if sauce_id is not None:
            row = con.execute(
                "SELECT id, name, main_category, is_active FROM sauces_catalog WHERE id=? LIMIT 1",
                (sauce_id,),
            ).fetchone()
        elif sauce_name:
            if not menu_main:
                raise HTTPException(status_code=400, detail="main_category is required when inclSauce is by name")
            row = con.execute(
                "SELECT id, name, main_category, is_active FROM sauces_catalog "
                "WHERE name=? AND main_category=? LIMIT 1",
                (sauce_name, menu_main),
            ).fetchone()

        if not row:
            raise HTTPException(status_code=400, detail="inclSauce not found in sauces catalog")
        if not bool(row["is_active"] or 0):
            raise HTTPException(status_code=400, detail="inclSauce is inactive")
        sauce_main = (row["main_category"] or "").strip()
        if menu_main and sauce_main and sauce_main != menu_main:
            raise HTTPException(status_code=400, detail="inclSauce main_category must match item main_category")

        return {
            "id": int(row["id"]),
            "name": (row["name"] or "").strip(),
            "mainCategory": sauce_main,
            "main_category": sauce_main,
        }

    def _kv_write_json(key: str, value) -> None:
        con = _connect(db_path)
        try:
            con.execute(
                "INSERT INTO pos_kv(key,value,updated_at) VALUES(?,?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
                ((key or "").strip(), json.dumps(value, ensure_ascii=False), _now()),
            )
            con.commit()
        finally:
            con.close()

    def _resolve_item_id_from_article(article_number: str) -> Optional[int]:
        an = (article_number or "").strip()
        if not an:
            return None
        con = _connect(db_path)
        try:
            row = con.execute(
                "SELECT id FROM menu_items WHERE article_number=? AND is_active=1 ORDER BY id DESC LIMIT 1",
                (an,),
            ).fetchone()
            if not row:
                return None
            return int(row["id"])
        finally:
            con.close()

    def _fallback_from_menu_subcategory(tag: str) -> list:
        if tag == "extra-ingredients":
            wanted = {"Ingredients", "__INGREDIENTS__"}
        else:
            wanted = {"Sauce"}
        con = _connect(db_path)
        try:
            rows = con.execute(
                "SELECT name, prices_json, sub_category FROM menu_items WHERE is_active=1"
            ).fetchall()
            out = []
            seen = set()
            for r in rows:
                name = (r["name"] or "").strip()
                if not name:
                    continue
                sub_category = (r["sub_category"] or "").strip()
                if sub_category not in wanted:
                    continue
                if name.lower() in seen:
                    continue
                seen.add(name.lower())
                prices = _json_loads(r["prices_json"], {})
                if not isinstance(prices, dict):
                    prices = {}
                out.append({"name": name, "prices": prices})
            return out
        finally:
            con.close()

    def _fallback_from_catalog(tag: str) -> list[dict[str, Any]]:
        table = "ingredients_catalog" if tag == "extra-ingredients" else "sauces_catalog"
        try:
            rows = _catalog_rows(table, main_category=None, active_only=True, q=None)
        except Exception:
            return []
        out: list[dict[str, Any]] = []
        for r in rows:
            nm = str((r or {}).get("name") or "").strip()
            if not nm:
                continue
            prices = _normalize_price_map((r or {}).get("prices"))
            out.append({"name": nm, "prices": prices})
        return out

    def _addon_get_impl(
        tag: str,
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
    ) -> dict:
        keys = _ADDON_KV_KEYS[tag]
        iid = int(item_id) if item_id is not None else None
        if iid is None and article_number:
            iid = _resolve_item_id_from_article(article_number)

        by_item = _kv_read_json(keys["by_item"], {})
        if not isinstance(by_item, dict):
            by_item = {}
        if iid is not None:
            item_payload = by_item.get(str(iid))
            if isinstance(item_payload, list):
                vals = _normalize_named_price_items(item_payload)
                return {"items": vals, "scope": "item", "item_id": iid, "source": "kv"}
            if isinstance(item_payload, dict) and isinstance(item_payload.get("items"), list):
                vals = _normalize_named_price_items(item_payload.get("items") or [])
                return {"items": vals, "scope": "item", "item_id": iid, "source": "kv"}

        global_payload = _kv_read_json(keys["global"], [])
        if isinstance(global_payload, list):
            if global_payload:
                vals = _normalize_named_price_items(global_payload)
                return {"items": vals, "scope": "global", "source": "kv"}
        elif isinstance(global_payload, dict) and isinstance(global_payload.get("items"), list):
            vals = global_payload.get("items") or []
            if vals:
                vals_n = _normalize_named_price_items(vals)
                return {"items": vals_n, "scope": "global", "source": "kv"}

        # catalog fallback (preferred over legacy menu-subcategory)
        cat_vals = _fallback_from_catalog(tag)
        if cat_vals:
            return {"items": cat_vals, "scope": "global", "source": "catalog"}

        # menu-based fallback so Android always gets useful records when configured that way
        fallback = _fallback_from_menu_subcategory(tag)
        return {"items": _normalize_named_price_items(fallback), "scope": "global", "source": "menu_sub_category"}

    async def _addon_post_impl(
        tag: str,
        request: Request,
    ) -> dict:
        payload = await _read_payload_any(request)
        keys = _ADDON_KV_KEYS[tag]

        item_id = payload.get("item_id")
        if item_id is None:
            item_id = payload.get("itemId")
        article_number = payload.get("article_number") or payload.get("articleNumber")

        items = payload.get("items")
        if items is None and isinstance(payload.get("value"), list):
            items = payload.get("value")
        if items is None:
            items = []
        if not isinstance(items, list):
            raise HTTPException(status_code=400, detail="items must be an array")

        # canonical write: item-specific if item_id/article provided, else global
        iid = None
        if item_id is not None and str(item_id).strip() != "":
            try:
                iid = int(item_id)
            except Exception:
                raise HTTPException(status_code=400, detail="item_id must be integer")
        if iid is None and article_number:
            iid = _resolve_item_id_from_article(str(article_number))

        if iid is not None:
            by_item = _kv_read_json(keys["by_item"], {})
            if not isinstance(by_item, dict):
                by_item = {}
            by_item[str(iid)] = items
            _kv_write_json(keys["by_item"], by_item)
            seq = _emit_event(db_path, f"addon.{tag}.updated", {"scope": "item", "item_id": iid})
            return {"ok": True, "scope": "item", "item_id": iid, "count": len(items), "seq": seq}

        _kv_write_json(keys["global"], items)
        seq = _emit_event(db_path, f"addon.{tag}.updated", {"scope": "global"})
        return {"ok": True, "scope": "global", "count": len(items), "seq": seq}

    @api.get("/extra-ingredients")
    def api_extra_ingredients_get(
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        return _addon_get_impl("extra-ingredients", item_id=item_id, article_number=article_number)

    @api.get("/extra_ingredients")
    def api_extra_ingredients_get_alias_u(
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        return _addon_get_impl("extra-ingredients", item_id=item_id, article_number=article_number)

    @api.get("/extraIngredients")
    def api_extra_ingredients_get_alias_c(
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        return _addon_get_impl("extra-ingredients", item_id=item_id, article_number=article_number)

    @api.get("/IngredientsExtra")
    @api.get("/ExtraIngredients")
    def api_extra_ingredients_get_alias_caps(
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        return _addon_get_impl("extra-ingredients", item_id=item_id, article_number=article_number)

    @api.post("/extra-ingredients")
    @api.post("/extra_ingredients")
    @api.post("/extraIngredients")
    @api.post("/IngredientsExtra")
    @api.post("/ExtraIngredients")
    async def api_extra_ingredients_post(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return await _addon_post_impl("extra-ingredients", request)

    @api.get("/sauce-on-item")
    @api.get("/sauce")
    @api.get("/sauces")
    @api.get("/Sauce")
    @api.get("/Sauces")
    def api_sauce_on_item_get(
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        return _addon_get_impl("sauce-on-item", item_id=item_id, article_number=article_number)

    @api.post("/sauce-on-item")
    @api.post("/sauce")
    @api.post("/sauces")
    @api.post("/Sauce")
    @api.post("/Sauces")
    async def api_sauce_on_item_post(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return await _addon_post_impl("sauce-on-item", request)

    @api.get("/extra-sauce")
    @api.get("/extra_sauce")
    @api.get("/extraSauce")
    @api.get("/SauceExtra")
    @api.get("/ExtraSauce")
    def api_extra_sauce_get(
        item_id: Optional[int] = None,
        article_number: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        return _addon_get_impl("extra-sauce", item_id=item_id, article_number=article_number)

    @api.post("/extra-sauce")
    @api.post("/extra_sauce")
    @api.post("/extraSauce")
    @api.post("/SauceExtra")
    @api.post("/ExtraSauce")
    async def api_extra_sauce_post(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return await _addon_post_impl("extra-sauce", request)

    # ==========================================================
    # PDF Inbox (Android uploads PDFs, POS downloads + acks)
    # ==========================================================
    def _pdf_abs_from_rel(rel_path: str) -> Path:
        base = Path(app.state.data_dir)
        return (base / rel_path).resolve()

    def _pdf_rel_from_abs(abs_path: Path) -> str:
        base = Path(app.state.data_dir)
        try:
            return str(abs_path.resolve().relative_to(base.resolve()))
        except Exception:
            return abs_path.name

    def _pdf_safe_filename(original: str) -> str:
        name = os.path.basename((original or "").strip() or "upload.pdf")
        name = name.replace(" ", "_")
        if not name.lower().endswith(".pdf"):
            name = name + ".pdf"
        name = re.sub(r"[^A-Za-z0-9._-]+", "_", name)
        prefix = datetime.now().strftime("%Y-%m-%d_%H-%M-%S") + "_" + uuid.uuid4().hex[:8]
        return f"{prefix}_{name}"

    def _legacy_pdf_mirror_targets(filename: str) -> list[Path]:
        """
        Keep old offline flow working:
        mirror uploaded PDF to classic Data/local_server folders that main.py watches.
        """
        out: list[Path] = []
        try:
            root_data = (_app_root() / "Data" / "local_server").resolve()
            out.append((root_data / "pdfs_in" / filename).resolve())
            out.append((root_data / "pdfs" / filename).resolve())
        except Exception:
            pass
        try:
            cwd_data = (Path.cwd() / "Data" / "local_server").resolve()
            out.append((cwd_data / "pdfs_in" / filename).resolve())
            out.append((cwd_data / "pdfs" / filename).resolve())
        except Exception:
            pass
        uniq: list[Path] = []
        seen = set()
        for p in out:
            sp = str(p)
            if sp not in seen:
                seen.add(sp)
                uniq.append(p)
        return uniq

    @api.post("/Pdfs")
    @api.post("/pdfs")
    @app.post("/Pdfs")
    @app.post("/pdfs")
    async def pdf_upload(
        file: Optional[UploadFile] = File(default=None),
        pdf: Optional[UploadFile] = File(default=None),
        document: Optional[UploadFile] = File(default=None),
        tenant_id: str = Form(""),
        location_id: str = Form(""),
        store_id: str = Form("STORE_1"),
        register_id: str = Form("KASSE_1"),
        table_id: str = Form(""),
        mode: str = Form(""),
        note: str = Form(""),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)

        up = file or pdf or document
        if up is None:
            raise HTTPException(status_code=400, detail="file must be provided (file/pdf/document)")

        fn = up.filename or "upload.pdf"
        ctype = (up.content_type or "").strip().lower()
        if (not fn.lower().endswith(".pdf")) and (ctype not in ("application/pdf", "application/octet-stream")):
            raise HTTPException(status_code=400, detail="file must be a PDF")

        pdf_in_dir = Path(app.state.pdf_in_dir)
        pdf_in_dir.mkdir(parents=True, exist_ok=True)

        safe_name = _pdf_safe_filename(fn)
        abs_path = (pdf_in_dir / safe_name).resolve()
        rel_path = _pdf_rel_from_abs(abs_path)

        sha = hashlib.sha256()
        size = 0
        try:
            with open(abs_path, "wb") as f:
                while True:
                    chunk = await up.read(1024 * 1024)
                    if not chunk:
                        break
                    f.write(chunk)
                    sha.update(chunk)
                    size += len(chunk)
        finally:
            try:
                await up.close()
            except Exception:
                pass

        created_at = _now()
        # Legacy offline compatibility: also mirror into Data/local_server/pdfs(_in)
        # so existing polling code in main.py can pick it up from the old folder.
        for mirror_abs in _legacy_pdf_mirror_targets(safe_name):
            try:
                if str(mirror_abs) == str(abs_path):
                    continue
                mirror_abs.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(str(abs_path), str(mirror_abs))
            except Exception:
                pass

        con = _connect(db_path)
        try:
            cur = con.cursor()
            cur.execute(
                """
                INSERT INTO pdf_inbox(tenant_id, location_id, store_id, register_id, table_id, mode, filename, rel_path, sha256, size_bytes, status, note, created_at, updated_at)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    (tenant_id or "").strip(),
                    (location_id or "").strip(),
                    (store_id or "").strip(),
                    (register_id or "").strip(),
                    (table_id or "").strip(),
                    (mode or "").strip(),
                    safe_name,
                    rel_path,
                    sha.hexdigest(),
                    int(size),
                    "NEW",
                    (note or "").strip(),
                    created_at,
                    created_at,
                ),
            )
            con.commit()
            pdf_id = int(cur.lastrowid)
        finally:
            con.close()

        # Optional: auto-mark table when PDF arrives
        tid = (table_id or "").strip()
        if tid:
            _rtdb_patch("Tables", tid, {
                "pdfId": str(pdf_id),
                "pdfUploaded": True,
                "pdfStatus": "NEW",
                "pdfFilename": safe_name,
                "pdfMode": (mode or "").strip(),
            })

        seq = _emit_event(db_path, "pdf.uploaded", {"pdf_id": pdf_id, "filename": safe_name, "table_id": table_id})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "pdf.uploaded", "seq": seq, "pdf_id": pdf_id, "filename": safe_name})
        except Exception:
            pass

        return {
            "ok": True,
            "pdf_id": pdf_id,
            "tenant_id": (tenant_id or "").strip(),
            "location_id": (location_id or "").strip(),
            "filename": safe_name,
            "status": "NEW",
            "download_url": f"/api/Pdfs/{pdf_id}/file",
            "seq": seq,
        }

    @api.get("/Pdfs")
    @api.get("/pdfs")
    @app.get("/Pdfs")
    @app.get("/pdfs")
    def pdf_list(
        status: Optional[str] = None,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        limit: int = 200,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        st = (status or "").strip().upper()
        tid = (tenant_id or "").strip()
        lid = (location_id or "").strip()
        con = _connect(db_path)
        try:
            where = []
            params: list[Any] = []
            if st:
                where.append("status=?")
                params.append(st)
            if tid:
                where.append("tenant_id=?")
                params.append(tid)
            if lid:
                where.append("location_id=?")
                params.append(lid)
            sql = "SELECT * FROM pdf_inbox"
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY id DESC LIMIT ?"
            params.append(min(max(int(limit), 1), 2000))
            rows = con.execute(sql, tuple(params)).fetchall()

            items = []
            for r in rows:
                d = dict(r)
                d["id"] = int(d["id"])
                d["size_bytes"] = int(d.get("size_bytes") or 0)
                items.append(d)
            return {"items": items}
        finally:
            con.close()

    @api.get("/Pdfs/{pdf_id}")
    @api.get("/pdfs/{pdf_id}")
    @app.get("/Pdfs/{pdf_id}")
    @app.get("/pdfs/{pdf_id}")
    def pdf_get(
        pdf_id: int,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        tid = (tenant_id or "").strip()
        lid = (location_id or "").strip()
        con = _connect(db_path)
        try:
            where = ["id=?"]
            params: list[Any] = [int(pdf_id)]
            if tid:
                where.append("tenant_id=?")
                params.append(tid)
            if lid:
                where.append("location_id=?")
                params.append(lid)
            r = con.execute(f"SELECT * FROM pdf_inbox WHERE {' AND '.join(where)} LIMIT 1", tuple(params)).fetchone()
            if not r:
                raise HTTPException(status_code=404, detail="PDF not found")
            d = dict(r)
            d["id"] = int(d["id"])
            d["size_bytes"] = int(d.get("size_bytes") or 0)
            return d
        finally:
            con.close()

    @api.get("/Pdfs/{pdf_id}/file")
    @api.get("/pdfs/{pdf_id}/file")
    @app.get("/Pdfs/{pdf_id}/file")
    @app.get("/pdfs/{pdf_id}/file")
    def pdf_download(
        pdf_id: int,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ):
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        tid = (tenant_id or "").strip()
        lid = (location_id or "").strip()
        con = _connect(db_path)
        try:
            where = ["id=?"]
            params: list[Any] = [int(pdf_id)]
            if tid:
                where.append("tenant_id=?")
                params.append(tid)
            if lid:
                where.append("location_id=?")
                params.append(lid)
            r = con.execute(
                f"SELECT filename, rel_path FROM pdf_inbox WHERE {' AND '.join(where)} LIMIT 1",
                tuple(params),
            ).fetchone()
            if not r:
                raise HTTPException(status_code=404, detail="PDF not found")
            abs_path = _pdf_abs_from_rel(r["rel_path"])
            if not abs_path.exists():
                raise HTTPException(status_code=404, detail="PDF file missing on disk")
            return FileResponse(
                path=str(abs_path),
                media_type="application/pdf",
                filename=str(r["filename"] or f"pdf_{pdf_id}.pdf"),
            )
        finally:
            con.close()

    @api.post("/Pdfs/{pdf_id}/ack")
    @api.post("/pdfs/{pdf_id}/ack")
    @app.post("/Pdfs/{pdf_id}/ack")
    @app.post("/pdfs/{pdf_id}/ack")
    async def pdf_ack(
        pdf_id: int,
        request: Request,
        body: Optional[PdfAck] = None,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        tid = (tenant_id or "").strip()
        lid = (location_id or "").strip()
        status = ""
        note_val = ""
        if body is not None:
            status = (body.status or "").strip().upper()
            note_val = (body.note or "").strip()
        if not status:
            payload = await _read_payload_any(request)
            if isinstance(payload, dict):
                status = str(payload.get("status") or payload.get("Status") or "").strip().upper()
                note_val = str(payload.get("note") or payload.get("Note") or "").strip()
        if status not in ("NEW", "PROCESSED", "ERROR"):
            raise HTTPException(status_code=400, detail="status must be NEW, PROCESSED, or ERROR")

        con = _connect(db_path)
        try:
            r = con.execute(
                (
                    "SELECT id, filename, rel_path, status FROM pdf_inbox "
                    "WHERE id=? "
                    + ("AND tenant_id=? " if tid else "")
                    + ("AND location_id=? " if lid else "")
                    + "LIMIT 1"
                ),
                tuple([int(pdf_id)] + ([tid] if tid else []) + ([lid] if lid else [])),
            ).fetchone()
            if not r:
                raise HTTPException(status_code=404, detail="PDF not found")

            rel_path = r["rel_path"]
            abs_path = _pdf_abs_from_rel(rel_path)

            new_rel = rel_path
            if status == "PROCESSED" and abs_path.exists():
                done_dir = Path(app.state.pdf_done_dir)
                done_dir.mkdir(parents=True, exist_ok=True)
                dest = (done_dir / os.path.basename(abs_path)).resolve()
                try:
                    abs_path.replace(dest)
                    new_rel = _pdf_rel_from_abs(dest)
                except Exception:
                    new_rel = rel_path

            ts = _now()
            con.execute(
                "UPDATE pdf_inbox SET status=?, note=?, rel_path=?, updated_at=? WHERE id=?",
                (status, note_val, new_rel, ts, int(pdf_id)),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "pdf.ack", {"pdf_id": int(pdf_id), "status": status})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "pdf.ack", "seq": seq, "pdf_id": int(pdf_id), "status": status})
        except Exception:
            pass

        return {"ok": True, "pdf_id": int(pdf_id), "status": status, "seq": seq}

    @api.delete("/Pdfs/{pdf_id}")
    @api.delete("/pdfs/{pdf_id}")
    @app.delete("/Pdfs/{pdf_id}")
    @app.delete("/pdfs/{pdf_id}")
    def pdf_delete(
        pdf_id: int,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        tid = (tenant_id or "").strip()
        lid = (location_id or "").strip()
        con = _connect(db_path)
        try:
            where = ["id=?"]
            params: list[Any] = [int(pdf_id)]
            if tid:
                where.append("tenant_id=?")
                params.append(tid)
            if lid:
                where.append("location_id=?")
                params.append(lid)
            r = con.execute(
                f"SELECT rel_path FROM pdf_inbox WHERE {' AND '.join(where)} LIMIT 1",
                tuple(params),
            ).fetchone()
            if not r:
                raise HTTPException(status_code=404, detail="PDF not found")
            abs_path = _pdf_abs_from_rel(r["rel_path"])
            try:
                if abs_path.exists():
                    abs_path.unlink()
            except Exception:
                pass
            con.execute(
                (
                    "DELETE FROM pdf_inbox WHERE id=? "
                    + ("AND tenant_id=? " if tid else "")
                    + ("AND location_id=? " if lid else "")
                ),
                tuple([int(pdf_id)] + ([tid] if tid else []) + ([lid] if lid else [])),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "pdf.deleted", {"pdf_id": int(pdf_id)})
        return {"ok": True, "pdf_id": int(pdf_id), "seq": seq}

    # ==========================================================
    # RTDB emulation — Firebase-like merge (Tables)
    # NOTE: Catch-all routes are registered LAST (fixes your 405 on POST /api/menu)
    # ==========================================================
    _NODE_ALIASES = {
        "tables": "Tables",
        "drawer": "Drawer",
        "log": "Log",
        "onlineordersbereit": "OnlineOrdersBereit",
        "pdfs": "Pdfs",
    }

    def _norm_node(node: str) -> str:
        n = (node or "").strip()
        if not n:
            return n
        return _NODE_ALIASES.get(n.lower(), n)

    _TABLE_DEFAULT_TEMPLATE: dict[str, Any] = {
        "apartment": "",
        "building": "",
        "callWaiter": False,
        "chairs": 4,
        "cityName": "",
        "customerMobile": "",
        "customerName": "",
        "deliveryMobile": "",
        "deliveryStatus": "",
        "displayId": "",
        "driverName": "",
        "email": "",
        "employeeName": "",
        "floor": "",
        "from": "",
        "id": "",
        "imageUrl": "",
        "isBeingReserved": False,
        "isReserved": False,
        "locationAddress": "",
        "locationDescription": "",
        "locationLatitude": 0,
        "locationLongitude": 0,
        "locationName": "",
        "mobile": "",
        "position": 0,
        "printagain": False,
        "provinceCode": "",
        "reservedFor": "",
        "spinning": False,
        "splitJustBeenPaid": False,
        "status": "available",
        "street": "",
        "tableOrderList": False,
        "to": "",
    }

    def _rtdb_get(node: str, key: str, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> Optional[dict]:
        node = _scoped_rtdb_node(_norm_node(node), tenant_id, location_id)
        con = _connect(db_path)
        try:
            r = con.execute(
                "SELECT json FROM rtdb_nodes WHERE node=? AND node_key=? LIMIT 1",
                (node, key),
            ).fetchone()
            if not r:
                return None
            try:
                return json.loads(r["json"] or "{}")
            except Exception:
                return {}
        finally:
            con.close()

    def _rtdb_get_all(node: str, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> dict:
        node = _scoped_rtdb_node(_norm_node(node), tenant_id, location_id)
        con = _connect(db_path)
        try:
            rows = con.execute(
                "SELECT node_key, json FROM rtdb_nodes WHERE node=?",
                (node,),
            ).fetchall()
            out = {}
            for r in rows:
                try:
                    out[r["node_key"]] = json.loads(r["json"] or "{}")
                except Exception:
                    out[r["node_key"]] = {}
            return out
        finally:
            con.close()

    def _default_object_for(node: str, key: str) -> dict:
        node = _norm_node(node)
        if node != "Tables":
            return {}

        obj = dict(_TABLE_DEFAULT_TEMPLATE)
        obj["id"] = str(key)
        obj["displayId"] = str(key)
        try:
            if str(key).isdigit():
                obj["position"] = int(str(key))
        except Exception:
            obj["position"] = 0
        return obj

    def _firebase_like_merge(existing: dict, patch: dict, *, node: str, key: str) -> dict:
        node = _norm_node(node)

        if not isinstance(existing, dict):
            existing = {}
        if not isinstance(patch, dict):
            return existing

        # normalize OrderedItems aliases
        if "orderedItems" in patch and "OrderedItems" not in patch:
            patch["OrderedItems"] = patch.pop("orderedItems")
        if "ordered_items" in patch and "OrderedItems" not in patch:
            patch["OrderedItems"] = patch.pop("ordered_items")

        for k, v in patch.items():
            if v is None:
                existing.pop(k, None)
                continue

            if k == "OrderedItems":
                # Special handling:
                # - Replace the list (Firebase behavior)
                # - Ensure each ordered item has a stable unique id (lineId) so clients/backends can dedupe correctly
                # - Preserve server-side print metadata (printed/printedPortion/printedAt/printedBy) if clients re-send items without these fields
                if v is None or v == [] or v == "" or v is False or v == {}:
                    existing.pop("OrderedItems", None)
                else:
                    if not isinstance(v, list):
                        # If a client sends non-list, just store it as-is
                        existing["OrderedItems"] = v
                        continue

                    ex_list = existing.get("OrderedItems")
                    if not isinstance(ex_list, list):
                        ex_list = []

                    # Build a pool of existing items by content fingerprint so we can re-attach stable ids/print flags
                    import uuid as _uuid
                    import hashlib as _hashlib

                    def _fp_for_merge(it: dict) -> str:
                        if not isinstance(it, dict):
                            return ""
                        payload = {
                            # stable fields (ignore quantity/price so edits keep the same lineId/printedQty)
                            "item": it.get("item") or it.get("name") or "",
                            "selectedSize": it.get("selectedSize") or it.get("size"),
                            "collectionName": it.get("collectionName") or it.get("collection") or it.get("category"),
                            "extraIngredients": it.get("extraIngredients"),
                            "removedIngredients": it.get("removedIngredients"),
                            "selectedSingleSauce": it.get("selectedSingleSauce"),
                            "selectedSauces": it.get("selectedSauces"),
                            "comment": it.get("comment"),
                            "freeSoftDrink": it.get("freeSoftDrink"),
                        }
                        raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, default=str)
                        return _hashlib.sha1(raw.encode("utf-8", "ignore")).hexdigest()

                    # Map by existing id (fast path)
                    ex_by_id: dict[str, dict] = {}
                    fp_pool: dict[str, list[dict]] = {}

                    for ex in ex_list:
                        if not isinstance(ex, dict):
                            continue
                        ex_id = ex.get("lineId") or ex.get("uuid") or ex.get("itemId")
                        if ex_id:
                            ex_by_id[str(ex_id)] = ex
                        fp = _fp_for_merge(ex)
                        if fp:
                            fp_pool.setdefault(fp, []).append(ex)

                    new_list = []
                    for it in v:
                        if not isinstance(it, dict):
                            new_list.append(it)
                            continue

                        # normalize legacy key
                        if "name" in it and "item" not in it:
                            it["item"] = it.get("name")

                        cur_id = it.get("lineId") or it.get("uuid") or it.get("itemId")
                        matched = None

                        if cur_id and str(cur_id) in ex_by_id:
                            matched = ex_by_id[str(cur_id)]
                        else:
                            fp = _fp_for_merge(it)
                            if fp and fp_pool.get(fp):
                                matched = fp_pool[fp].pop(0)
                                # attach stable id if missing
                                if not cur_id:
                                    mid = matched.get("lineId") or matched.get("uuid") or matched.get("itemId") or matched.get("id")
                                    if mid:
                                        it.setdefault("lineId", str(mid))
                                        cur_id = str(mid)

                        # Ensure a stable unique line id exists
                        if not cur_id:
                            it["lineId"] = str(_uuid.uuid4())
                            cur_id = it["lineId"]


                        it.setdefault("printedQty", 0)
# Preserve server-side print meta if client doesn't send it back
                        if isinstance(matched, dict):
                            for fk in ("printed", "printedQty", "printedPortion", "printedAt", "printedBy"):
                                if fk not in it and fk in matched:
                                    it[fk] = matched.get(fk)

                        new_list.append(it)

                    existing["OrderedItems"] = new_list
                continue

            existing[k] = v

        if node == "Tables":
            for kk, dv in _TABLE_DEFAULT_TEMPLATE.items():
                if kk not in existing or existing[kk] is None:
                    existing[kk] = dv

            if not str(existing.get("id") or "").strip():
                existing["id"] = str(key)
            if not str(existing.get("displayId") or "").strip():
                existing["displayId"] = str(key)

            try:
                if int(existing.get("position") or 0) == 0 and str(key).isdigit():
                    existing["position"] = int(str(key))
            except Exception:
                pass

        return existing

    def _rtdb_put(node: str, key: str, obj: dict, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> dict:
        node = _scoped_rtdb_node(_norm_node(node), tenant_id, location_id)
        if not isinstance(obj, dict):
            obj = {}

        con = _connect(db_path)
        try:
            con.execute(
                "INSERT INTO rtdb_nodes(node,node_key,json,updated_at) VALUES(?,?,?,?) "
                "ON CONFLICT(node,node_key) DO UPDATE SET json=excluded.json, updated_at=excluded.updated_at",
                (node, key, json.dumps(obj, ensure_ascii=False), _now()),
            )
            con.commit()
        finally:
            con.close()
        return obj

    def _rtdb_patch(node: str, key: str, patch_obj: dict, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> dict:
        node = _norm_node(node)
        key = str(key)

        cur_obj = _rtdb_get(node, key, tenant_id, location_id)
        if cur_obj is None:
            cur_obj = _default_object_for(node, key)

        new_obj = _firebase_like_merge(cur_obj, patch_obj, node=node, key=key)
        _rtdb_put(node, key, new_obj, tenant_id, location_id)

        _emit_event(db_path, f"rtdb.{node}.patched", {"key": key})
        return new_obj

    def _rtdb_delete(node: str, key: str, tenant_id: Optional[str] = None, location_id: Optional[str] = None) -> None:
        node = _scoped_rtdb_node(_norm_node(node), tenant_id, location_id)
        con = _connect(db_path)
        try:
            con.execute("DELETE FROM rtdb_nodes WHERE node=? AND node_key=?", (node, str(key)))
            con.commit()
        finally:
            con.close()

    AUTO_CREATE_ON_GET = {"Tables"}

    def _table_exists(con: sqlite3.Connection, table_name: str) -> bool:
        try:
            row = con.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name=? LIMIT 1",
                (str(table_name or "").strip(),),
            ).fetchone()
            return bool(row)
        except Exception:
            return False

    def _order_status_is_open(status_raw: Any) -> bool:
        s = str(status_raw or "").strip().lower()
        if not s:
            return True
        closed = {"done", "completed", "finished", "delivered", "canceled", "cancelled", "storniert"}
        return s not in closed

    def _to_eur_from_centsish(val: Any) -> float:
        try:
            if val is None:
                return 0.0
            f = float(val)
            # DB stores cents in lieferung_daily.gesamtepreis.
            if abs(f) >= 1000:
                return round(f / 100.0, 2)
            # best effort for already-eur values
            return round(f, 2)
        except Exception:
            return 0.0

    def _is_today_from_row(created_at: Any, zeit: Any, today_ymd: str) -> bool:
        try:
            s = str(created_at or "").strip()
            if len(s) >= 10 and s[4] == "-" and s[7] == "-":
                return s[:10] == today_ymd
        except Exception:
            pass
        try:
            if zeit is not None and str(zeit).strip():
                ts = int(float(zeit))
                return datetime.fromtimestamp(ts).strftime("%Y-%m-%d") == today_ymd
        except Exception:
            pass
        return False

    def _local_summary_payload() -> dict:
        con = _connect(db_path)
        today = datetime.now().strftime("%Y-%m-%d")
        out = {
            "health": "OK",
            "orders_open": 0,
            "orders_today": 0,
            "orders_total": 0,
            "revenue_today_eur": 0.0,
            "menu_count": 0,
            "orders_outbox_pending": 0,
            "orders_outbox_failed": 0,
            "menu_outbox_pending": 0,
            "menu_outbox_failed": 0,
            "updated_at": _now(),
        }
        try:
            # orders
            if _table_exists(con, "lieferung_daily"):
                rows = con.execute(
                    "SELECT ID, status, created_at, zeit, gesamtepreis FROM lieferung_daily"
                ).fetchall()
                out["orders_total"] = len(rows or [])
                rev_today = 0.0
                o_today = 0
                o_open = 0
                for r in (rows or []):
                    if _order_status_is_open(r["status"]):
                        o_open += 1
                    if _is_today_from_row(r["created_at"], r["zeit"], today):
                        o_today += 1
                        rev_today += _to_eur_from_centsish(r["gesamtepreis"])
                out["orders_open"] = int(o_open)
                out["orders_today"] = int(o_today)
                out["revenue_today_eur"] = round(rev_today, 2)

            # menu count
            if _table_exists(con, "menu_items"):
                try:
                    row = con.execute("SELECT COUNT(*) AS c FROM menu_items").fetchone()
                    out["menu_count"] = int((row["c"] if row else 0) or 0)
                except Exception:
                    pass

            # orders outbox
            if _table_exists(con, "orders_sync_outbox"):
                rows = con.execute(
                    "SELECT status, COUNT(*) AS c FROM orders_sync_outbox GROUP BY status"
                ).fetchall()
                for rr in (rows or []):
                    s = str(rr["status"] or "").strip().lower()
                    c = int(rr["c"] or 0)
                    if s == "pending":
                        out["orders_outbox_pending"] += c
                    elif s == "failed":
                        out["orders_outbox_failed"] += c

            # menu outbox
            if _table_exists(con, "sync_outbox"):
                rows = con.execute(
                    "SELECT status, COUNT(*) AS c FROM sync_outbox GROUP BY status"
                ).fetchall()
                for rr in (rows or []):
                    s = str(rr["status"] or "").strip().lower()
                    c = int(rr["c"] or 0)
                    if s == "pending":
                        out["menu_outbox_pending"] += c
                    elif s == "failed":
                        out["menu_outbox_failed"] += c
        finally:
            con.close()
        return out

    def _http_get_json(url: str, api_key_val: str, timeout_sec: int = 10, verify_ssl: bool = True) -> tuple[int, Any]:
        req = urllib.request.Request(
            url=url,
            method="GET",
            headers={
                "X-Api-Key": str(api_key_val or ""),
                "Accept": "application/json",
                "User-Agent": "pos-hub-admin/1.0",
            },
        )
        ctx = None
        if str(url).lower().startswith("https://") and not bool(verify_ssl):
            ctx = ssl._create_unverified_context()
        try:
            with urllib.request.urlopen(req, timeout=max(1, int(timeout_sec)), context=ctx) as resp:
                raw = resp.read().decode("utf-8", errors="ignore")
                try:
                    obj = json.loads(raw) if raw else {}
                except Exception:
                    obj = {"raw": raw}
                return int(resp.status), obj
        except urllib.error.HTTPError as he:
            try:
                body = he.read().decode("utf-8", errors="ignore")
                obj = json.loads(body) if body else {}
            except Exception:
                obj = {"error": str(he)}
            return int(getattr(he, "code", 500) or 500), obj
        except Exception as e:
            return 0, {"error": str(e)}

    @api.get("/admin/summary-local")
    def api_admin_summary_local(x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return {"ok": True, "summary": _local_summary_payload()}

    @api.post("/admin/locations/summary")
    def api_admin_locations_summary(
        body: AdminSummaryRequest = Body(default_factory=AdminSummaryRequest),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        timeout_sec = min(max(int(body.timeout_sec or 10), 2), 25)
        rows: list[dict] = []
        agg = {
            "branches_total": 0,
            "branches_ok": 0,
            "branches_offline": 0,
            "orders_open": 0,
            "orders_today": 0,
            "revenue_today_eur": 0.0,
            "menu_count_total": 0,
            "orders_outbox_pending": 0,
            "orders_outbox_failed": 0,
            "menu_outbox_pending": 0,
            "menu_outbox_failed": 0,
        }

        targets = body.targets or []
        for t in targets:
            if (not bool(body.include_inactive)) and (not bool(t.active)):
                continue
            base = str(t.base_url or "").strip().rstrip("/")
            key = str(t.api_key or "").strip()
            verify_ssl = bool(t.verify_ssl) if t.verify_ssl is not None else base.lower().startswith("https://")
            item = {
                "branch_name": str(t.branch_name or ""),
                "tenant_id": str(t.tenant_id or ""),
                "location_id": str(t.location_id or ""),
                "base_url": base,
                "health": "OFF",
                "ok": False,
                "summary": {},
                "message": "",
            }
            if not base or not key:
                item["message"] = "base_url/api_key missing"
                rows.append(item)
                agg["branches_total"] += 1
                agg["branches_offline"] += 1
                continue

            # Preferred: ask branch for local summary directly.
            status, obj = _http_get_json(
                f"{base}/api/admin/summary-local",
                key,
                timeout_sec=timeout_sec,
                verify_ssl=verify_ssl,
            )
            if status == 200 and isinstance(obj, dict) and isinstance(obj.get("summary"), dict):
                summ = obj.get("summary") or {}
                item["summary"] = summ
                item["health"] = str(summ.get("health") or "OK")
                item["ok"] = True
                item["message"] = "summary-local"
            else:
                # Fallback if remote hasn't been updated yet: health + orders/menu quick scan.
                h_status, _ = _http_get_json(f"{base}/health", key, timeout_sec=timeout_sec, verify_ssl=verify_ssl)
                item["health"] = "OK" if h_status == 200 else "OFF"
                item["ok"] = bool(h_status == 200)
                item["message"] = f"fallback health={h_status}"

                o_status, o_obj = _http_get_json(
                    f"{base}/orders/delivery",
                    key,
                    timeout_sec=timeout_sec,
                    verify_ssl=verify_ssl,
                )
                rows_orders = []
                if o_status == 200 and isinstance(o_obj, dict) and isinstance(o_obj.get("orders"), list):
                    rows_orders = o_obj.get("orders") or []
                today = datetime.now().strftime("%Y-%m-%d")
                oo = ot = 0
                rev = 0.0
                for rr in rows_orders:
                    if not isinstance(rr, dict):
                        continue
                    if _order_status_is_open(rr.get("status")):
                        oo += 1
                    c_at = str(rr.get("created_at") or rr.get("time") or "").strip()
                    is_today = (len(c_at) >= 10 and c_at[:10] == today) or (not c_at)
                    if is_today:
                        ot += 1
                        if rr.get("gesamtepreis_eur") is not None:
                            rev += float(rr.get("gesamtepreis_eur") or 0.0)
                        else:
                            rev += _to_eur_from_centsish(rr.get("gesamtepreis"))

                m_status, m_obj = _http_get_json(
                    f"{base}/api/menu",
                    key,
                    timeout_sec=timeout_sec,
                    verify_ssl=verify_ssl,
                )
                m_count = 0
                if m_status == 200 and isinstance(m_obj, dict) and isinstance(m_obj.get("items"), list):
                    m_count = len(m_obj.get("items") or [])

                item["summary"] = {
                    "health": item["health"],
                    "orders_open": int(oo),
                    "orders_today": int(ot),
                    "orders_total": len(rows_orders),
                    "revenue_today_eur": round(float(rev), 2),
                    "menu_count": int(m_count),
                    "orders_outbox_pending": 0,
                    "orders_outbox_failed": 0,
                    "menu_outbox_pending": 0,
                    "menu_outbox_failed": 0,
                    "updated_at": _now(),
                }

            summ = item.get("summary") or {}
            agg["branches_total"] += 1
            if bool(item.get("ok")):
                agg["branches_ok"] += 1
            else:
                agg["branches_offline"] += 1
            agg["orders_open"] += int(summ.get("orders_open") or 0)
            agg["orders_today"] += int(summ.get("orders_today") or 0)
            agg["revenue_today_eur"] += float(summ.get("revenue_today_eur") or 0.0)
            agg["menu_count_total"] += int(summ.get("menu_count") or 0)
            agg["orders_outbox_pending"] += int(summ.get("orders_outbox_pending") or 0)
            agg["orders_outbox_failed"] += int(summ.get("orders_outbox_failed") or 0)
            agg["menu_outbox_pending"] += int(summ.get("menu_outbox_pending") or 0)
            agg["menu_outbox_failed"] += int(summ.get("menu_outbox_failed") or 0)
            rows.append(item)

        agg["revenue_today_eur"] = round(float(agg["revenue_today_eur"] or 0.0), 2)
        return {"ok": True, "updated_at": _now(), "summary": agg, "locations": rows}

    def _admin_requeue_outbox(kind: str = "both", include_pending: bool = False, reset_tries: bool = True) -> dict:
        kind_n = str(kind or "both").strip().lower()
        touch_orders = kind_n in ("orders", "both")
        touch_menu = kind_n in ("menu", "both")
        con = _connect(db_path)
        out = {
            "orders_changed": 0,
            "menu_changed": 0,
            "orders_table": False,
            "menu_table": False,
        }
        try:
            cur = con.cursor()
            if touch_orders and _table_exists(con, "orders_sync_outbox"):
                out["orders_table"] = True
                if include_pending:
                    if reset_tries:
                        cur.execute(
                            "UPDATE orders_sync_outbox SET status='pending', tries=0 WHERE status IN ('failed','pending')"
                        )
                    else:
                        cur.execute(
                            "UPDATE orders_sync_outbox SET status='pending' WHERE status IN ('failed','pending')"
                        )
                else:
                    if reset_tries:
                        cur.execute(
                            "UPDATE orders_sync_outbox SET status='pending', tries=0 WHERE status='failed'"
                        )
                    else:
                        cur.execute(
                            "UPDATE orders_sync_outbox SET status='pending' WHERE status='failed'"
                        )
                out["orders_changed"] = int(cur.rowcount or 0)

            if touch_menu and _table_exists(con, "sync_outbox"):
                out["menu_table"] = True
                if include_pending:
                    if reset_tries:
                        cur.execute(
                            "UPDATE sync_outbox SET status='pending', tries=0 WHERE status IN ('failed','pending')"
                        )
                    else:
                        cur.execute(
                            "UPDATE sync_outbox SET status='pending' WHERE status IN ('failed','pending')"
                        )
                else:
                    if reset_tries:
                        cur.execute(
                            "UPDATE sync_outbox SET status='pending', tries=0 WHERE status='failed'"
                        )
                    else:
                        cur.execute(
                            "UPDATE sync_outbox SET status='pending' WHERE status='failed'"
                        )
                out["menu_changed"] = int(cur.rowcount or 0)
            con.commit()
        finally:
            con.close()
        return out

    @api.post("/admin/outbox/retry-failed")
    def api_admin_outbox_retry_failed(
        body: AdminOutboxActionRequest = Body(default_factory=AdminOutboxActionRequest),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        stats = _admin_requeue_outbox(
            kind=body.kind,
            include_pending=bool(body.include_pending),
            reset_tries=bool(body.reset_tries),
        )
        seq = _emit_event(db_path, "admin.outbox.retry_failed", {"kind": body.kind, **stats})
        return {"ok": True, "seq": seq, **stats}

    @api.post("/admin/outbox/force-sync")
    def api_admin_outbox_force_sync(
        body: AdminOutboxActionRequest = Body(default_factory=AdminOutboxActionRequest),
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        # Best-effort force:
        # 1) failed -> pending (or keep pending) so branch workers pick them immediately
        # 2) emit an event so observers know a force was requested
        stats = _admin_requeue_outbox(
            kind=body.kind,
            include_pending=True,
            reset_tries=bool(body.reset_tries),
        )
        seq = _emit_event(db_path, "admin.outbox.force_sync", {"kind": body.kind, **stats})
        return {"ok": True, "seq": seq, **stats}

    @api.get("/employees")
    def api_employees_list(
            active_only: bool = True,
            x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        items = _list_employees_basic(active_only=bool(active_only))
        if not items:
            items = _employees_from_kv_fallback()
        return {"items": items, "count": len(items)}
    # ---- RTDB catch-alls (REGISTER LAST!) ----
    @api.get("/{node}")
    def api_get_node(
        node: str,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        return _rtdb_get_all(node, tenant_id, location_id)

    @api.get("/{node}/{key}")
    def api_get_node_key(
        node: str,
        key: str,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ):
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        node = _norm_node(node)
        key = str(key)

        obj = _rtdb_get(node, key, tenant_id, location_id)
        if obj is None:
            if node in AUTO_CREATE_ON_GET:
                obj = _default_object_for(node, key)
                _rtdb_put(node, key, obj, tenant_id, location_id)
                _emit_event(db_path, f"rtdb.{node}.created", {"key": key})
                return obj
            return {}

        return obj

    @api.patch("/{node}/{key}")
    def api_patch_node_key(
        node: str,
        key: str,
        payload: dict = Body(default_factory=dict),
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ):
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        if not isinstance(payload, dict):
            raise HTTPException(status_code=400, detail="JSON object required")
        return _rtdb_patch(node, str(key), payload, tenant_id, location_id)

    @api.delete("/{node}/{key}")
    def api_delete_node_key(
        node: str,
        key: str,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        node = _norm_node(node)
        key = str(key)
        _rtdb_delete(node, key, tenant_id, location_id)
        _emit_event(db_path, f"rtdb.{node}.deleted", {"key": key})
        return {"ok": True}

    # Register /api routes now
    app.include_router(api)

    @app.post("/gallery-admin/login")
    async def gallery_admin_login(request: Request):
        payload = await _read_payload_any(request)
        raw_key = ""
        if isinstance(payload, dict):
            raw_key = str(payload.get("api_key") or payload.get("apiKey") or "").strip()
        if not raw_key:
            raise HTTPException(status_code=400, detail="api_key required")
        _auth(raw_key)  # validates against server auth mode/key logic
        token, exp = _gallery_session_issue()
        from fastapi.responses import JSONResponse
        r = JSONResponse({"ok": True, "expires_at": int(exp)})
        r.set_cookie(
            key=_GALLERY_COOKIE,
            value=token,
            httponly=True,
            secure=True,
            samesite="lax",
            max_age=int(_GALLERY_TTL_SEC),
            path="/",
        )
        return r

    @app.post("/gallery-admin/logout")
    def gallery_admin_logout(request: Request):
        try:
            tok = str(request.cookies.get(_GALLERY_COOKIE) or "").strip()
            if tok:
                _gallery_sessions.pop(tok, None)
        except Exception:
            pass
        from fastapi.responses import JSONResponse
        r = JSONResponse({"ok": True})
        r.delete_cookie(_GALLERY_COOKIE, path="/")
        return r

    @app.get("/gallery-admin/me")
    def gallery_admin_me(request: Request):
        return {"ok": bool(_gallery_session_check(request))}

    @app.get("/gallery-admin")
    def gallery_admin_page():
        html = """<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width,initial-scale=1" />
  <title>Global Gallery Admin</title>
  <style>
    :root {
      --bg:#f3f6fb; --card:#ffffff; --line:#dbe3ee; --text:#111827; --muted:#586173;
      --brand:#0f766e; --danger:#b91c1c; --accent:#0b1220;
    }
    * { box-sizing: border-box; }
    body { margin:0; font-family: Segoe UI, Arial, sans-serif; background: var(--bg); color: var(--text); }
    .wrap { max-width: 1440px; margin: 0 auto; padding: 16px; }
    .top {
      background: linear-gradient(140deg, #0b1220 0%, #0f766e 100%);
      color:#fff; border-radius: 14px; padding:14px; margin-bottom:12px;
    }
    .top h1 { margin: 0 0 4px 0; font-size: 20px; }
    .top p { margin: 0; font-size: 13px; opacity: .95; }
    .row { display:flex; gap:8px; align-items:center; flex-wrap:wrap; }
    .grid-layout { display:grid; grid-template-columns: 300px 1fr; gap:12px; }
    .card { background:var(--card); border:1px solid var(--line); border-radius:12px; padding:12px; }
    .title { font-weight:700; margin-bottom:8px; }
    input, select, button {
      border-radius:9px; border:1px solid var(--line); padding:8px 10px; font-size: 14px; background:#fff; color:var(--text);
    }
    input[type=file] { width: 100%; }
    button { cursor:pointer; background:var(--accent); color:#fff; border:0; }
    button.alt { background:#475569; }
    button.ok { background:var(--brand); }
    button.danger { background:var(--danger); }
    .cats { max-height: 360px; overflow:auto; border:1px solid var(--line); border-radius:10px; background:#f8fafc; }
    .cat-item {
      display:flex; justify-content:space-between; align-items:center; gap:8px;
      padding:8px 10px; border-bottom:1px solid #e7edf6; cursor:pointer;
    }
    .cat-item:last-child { border-bottom:0; }
    .cat-item.active { background:#e6fffb; font-weight:700; }
    .toolbar { display:flex; gap:8px; align-items:center; flex-wrap:wrap; margin-bottom:10px; }
    .drop {
      border:2px dashed #9fb3ca; border-radius:12px; padding:16px; text-align:center; background:#f8fbff; color:var(--muted);
      margin-top:8px;
    }
    .stats { color:var(--muted); font-size:12px; }
    .gallery { display:grid; grid-template-columns: repeat(auto-fill, minmax(210px, 1fr)); gap:10px; }
    .tile { background:#fff; border:1px solid var(--line); border-radius:12px; overflow:hidden; }
    .img { width:100%; height:160px; object-fit:cover; background:#e6ebf2; }
    .meta { padding:8px; font-size:12px; }
    .meta .name { font-size:13px; font-weight:700; margin-bottom:4px; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
    .meta .small { color:var(--muted); margin-bottom:6px; }
    .msg { margin:8px 0; font-size:13px; min-height:18px; }
    @media (max-width: 900px) { .grid-layout { grid-template-columns: 1fr; } }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="top">
      <h1>Global Gallery Admin</h1>
      <p>Create categories, upload images or folders, move and delete files for all customers.</p>
    </div>

    <div class="toolbar card">
      <div class="row" id="loginRow">
        <label>Admin Login</label>
        <input id="apiKey" type="password" style="min-width:320px" placeholder="Enter admin API key once" />
        <button class="ok" onclick="login()">Sign In</button>
      </div>
      <div class="row" id="loggedRow" style="display:none">
        <span class="stats">Logged in</span>
        <button class="alt" onclick="bootstrap()">Reload</button>
        <button class="danger" onclick="logout()">Logout</button>
        <span class="stats" id="statsTop"></span>
      </div>
    </div>

    <div class="grid-layout">
      <div class="card">
        <div class="title">Categories</div>
        <div class="row">
          <input id="newCat" placeholder="new category" style="flex:1" />
          <button class="ok" onclick="createCategory()">Create</button>
        </div>
        <div class="row" style="margin-top:8px">
          <button class="danger" onclick="deleteCategory()">Delete Selected</button>
          <select id="moveToCat"></select>
        </div>
        <div class="cats" id="catList" style="margin-top:8px"></div>
      </div>

      <div>
        <div class="card" style="margin-bottom:10px">
          <div class="title">Upload</div>
          <div class="row">
            <input id="filesInput" type="file" accept=".png,.jpg,.jpeg,.webp" multiple />
          </div>
          <div class="row" style="margin-top:8px">
            <input id="folderInput" type="file" webkitdirectory directory multiple />
          </div>
          <div class="drop" id="dropZone">Drop files here</div>
          <div class="row" style="margin-top:8px">
            <button class="ok" onclick="uploadSelected()">Upload Selected</button>
            <span class="stats" id="uploadInfo">0 files selected</span>
          </div>
        </div>

        <div class="card">
          <div class="toolbar">
            <div class="title" style="margin:0">Images</div>
            <input id="search" placeholder="search name..." oninput="renderGrid()" />
            <button onclick="loadItems()">Refresh</button>
            <button class="alt" onclick="moveSelected()">Move Selected</button>
            <button class="danger" onclick="deleteSelected()">Delete Selected</button>
          </div>
          <div class="msg" id="msg"></div>
          <div id="gallery" class="gallery"></div>
        </div>
      </div>
    </div>
  </div>

<script>
let categories = [];
let items = [];
let currentCategory = "all";
let selectedFiles = [];
let checked = new Set();

async function apiFetch(url, options={}){
  const opt = Object.assign({}, options || {});
  opt.credentials = "include";
  if(opt.body && !(opt.body instanceof FormData)){
    opt.headers = Object.assign({"Content-Type":"application/json"}, opt.headers || {});
  }
  return fetch(url, opt);
}
function setMsg(t, ok=false){
  const m = document.getElementById("msg");
  m.textContent = t || "";
  m.style.color = ok ? "#065f46" : "#b91c1c";
}
function esc(s){
  return String(s||"").replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
async function login(){
  const key = document.getElementById("apiKey").value || "";
  if(!key.trim()){ setMsg("Enter API key."); return; }
  const r = await apiFetch("/gallery-admin/login", {
    method:"POST",
    body: JSON.stringify({api_key:key})
  });
  if(!r.ok){ setMsg("Login failed: " + r.status); return; }
  document.getElementById("apiKey").value = "";
  await bootstrap();
}
async function logout(){
  await apiFetch("/gallery-admin/logout", {method:"POST"});
  document.getElementById("loginRow").style.display = "";
  document.getElementById("loggedRow").style.display = "none";
  setMsg("Logged out.", true);
}
async function authCheck(){
  const r = await apiFetch("/gallery-admin/me");
  if(!r.ok) return false;
  const j = await r.json();
  return !!(j && j.ok);
}
function humanSize(n){
  let x = Number(n||0);
  if(x < 1024) return `${x} B`;
  if(x < 1024*1024) return `${(x/1024).toFixed(1)} KB`;
  return `${(x/(1024*1024)).toFixed(1)} MB`;
}

async function loadCategories(){
  const r = await apiFetch("/api/gallery/categories");
  if(!r.ok){ throw new Error("categories load failed: "+r.status); }
  const j = await r.json();
  categories = Array.isArray(j.items) ? j.items : [];
  if(!categories.find(x => x.name === currentCategory)){ currentCategory = "all"; }

  const catList = document.getElementById("catList");
  catList.innerHTML = "";
  categories.forEach(c => {
    const row = document.createElement("div");
    row.className = "cat-item" + (c.name === currentCategory ? " active" : "");
    row.innerHTML = `<span>${esc(c.name)}</span><span class="stats">${Number(c.count||0)}</span>`;
    row.onclick = () => { currentCategory = c.name; renderCategories(); loadItems(); };
    catList.appendChild(row);
  });
  renderCategories();
}

function renderCategories(){
  const catList = document.getElementById("catList");
  [...catList.children].forEach((el, idx) => {
    const c = categories[idx];
    el.classList.toggle("active", c && c.name === currentCategory);
  });
  const moveSel = document.getElementById("moveToCat");
  moveSel.innerHTML = categories.map(c => `<option value="${esc(c.name)}">${esc(c.name)}</option>`).join("");
  moveSel.value = categories.find(c=>c.name==="all") ? "all" : (categories[0]?.name || "");
}

async function createCategory(){
  const raw = document.getElementById("newCat").value || "";
  if(!raw.trim()){ setMsg("Enter category name."); return; }
  const fd = new FormData();
  fd.append("name", raw);
  const r = await apiFetch("/api/gallery/categories", {method:"POST", body:fd});
  if(!r.ok){ setMsg("Create category failed: "+r.status); return; }
  document.getElementById("newCat").value = "";
  await loadCategories();
  setMsg("Category created.", true);
}

async function deleteCategory(){
  if(currentCategory === "all"){ setMsg("Cannot delete category 'all'."); return; }
  const moveTo = document.getElementById("moveToCat").value || "all";
  if(currentCategory === moveTo){ setMsg("Choose different move target."); return; }
  if(!confirm(`Delete category '${currentCategory}' and move files to '${moveTo}'?`)) return;
  const r = await apiFetch(`/api/gallery/categories?name=${encodeURIComponent(currentCategory)}&move_to=${encodeURIComponent(moveTo)}`, {
    method:"DELETE"
  });
  if(!r.ok){ setMsg("Delete category failed: "+r.status); return; }
  currentCategory = "all";
  await loadCategories();
  await loadItems();
  setMsg("Category deleted and files moved.", true);
}

async function loadItems(){
  const r = await apiFetch(`/api/gallery/list?category=${encodeURIComponent(currentCategory)}`);
  if(!r.ok){ setMsg("Load images failed: "+r.status); return; }
  const j = await r.json();
  items = Array.isArray(j.items) ? j.items : [];
  checked = new Set();
  renderGrid();
  document.getElementById("statsTop").textContent = `${items.length} images in '${currentCategory}'`;
}

function renderGrid(){
  const q = (document.getElementById("search").value || "").toLowerCase().trim();
  const list = q ? items.filter(it => `${it.name} ${it.category}`.toLowerCase().includes(q)) : items;
  const root = document.getElementById("gallery");
  root.innerHTML = "";
  list.forEach(it => {
    const id = btoa(it.rel_path).replace(/=/g,"_");
    const tile = document.createElement("div");
    tile.className = "tile";
    tile.innerHTML = `
      <img class="img" src="${it.url}" loading="lazy" />
      <div class="meta">
        <div class="row"><input type="checkbox" id="ck_${id}" onchange="toggleCheck('${esc(it.rel_path)}', this.checked)" /></div>
        <div class="name" title="${esc(it.name)}">${esc(it.name)}</div>
        <div class="small">${esc(it.category)} | ${humanSize(it.size)}</div>
        <div class="row">
          <input id="mv_${id}" value="${esc(it.category)}" style="flex:1" />
          <button class="alt" onclick="moveItem('${encodeURIComponent(it.rel_path)}','mv_${id}')">Move</button>
          <button class="danger" onclick="deleteItem('${encodeURIComponent(it.rel_path)}')">Delete</button>
        </div>
      </div>`;
    root.appendChild(tile);
  });
}

async function moveItem(rel, inputId){
  const nc = document.getElementById(inputId).value || "all";
  const fd = new FormData();
  fd.append("rel_path", decodeURIComponent(rel));
  fd.append("new_category", nc);
  const r = await apiFetch("/api/gallery/move", {method:"POST", body:fd});
  if(!r.ok){ setMsg("Move failed: "+r.status); return; }
  await loadCategories();
  await loadItems();
  setMsg("Image moved.", true);
}

async function deleteItem(rel){
  if(!confirm("Delete this image?")) return;
  const r = await apiFetch(`/api/gallery/item?rel_path=${rel}`, {method:"DELETE"});
  if(!r.ok){ setMsg("Delete failed: "+r.status); return; }
  await loadCategories();
  await loadItems();
  setMsg("Image deleted.", true);
}

function toggleCheck(rel, on){
  if(on) checked.add(rel); else checked.delete(rel);
}

async function deleteSelected(){
  const arr = Array.from(checked.values());
  if(!arr.length){ setMsg("No items selected."); return; }
  if(!confirm(`Delete ${arr.length} selected images?`)) return;
  const r = await apiFetch("/api/gallery/delete_many", {
    method:"POST",
    body: JSON.stringify({rel_paths: arr})
  });
  if(!r.ok){ setMsg("Delete selected failed: " + r.status); return; }
  await loadCategories();
  await loadItems();
  setMsg("Selected images deleted.", true);
}

async function moveSelected(){
  const arr = Array.from(checked.values());
  if(!arr.length){ setMsg("No items selected."); return; }
  const nc = prompt("Move selected to category:", currentCategory || "all");
  if(nc === null) return;
  const r = await apiFetch("/api/gallery/move_many", {
    method:"POST",
    body: JSON.stringify({rel_paths: arr, new_category: nc})
  });
  if(!r.ok){ setMsg("Move selected failed: " + r.status); return; }
  await loadCategories();
  await loadItems();
  setMsg("Selected images moved.", true);
}

function pickFilesFromInput(input){
  const arr = Array.from((input.files || [])).filter(f => /\\.(png|jpg|jpeg|webp)$/i.test(f.name));
  selectedFiles = arr;
  document.getElementById("uploadInfo").textContent = `${selectedFiles.length} files selected`;
}

async function uploadSelected(){
  if(!selectedFiles.length){ setMsg("No files selected."); return; }
  let ok = 0, fail = 0;
  for(const f of selectedFiles){
    const fd = new FormData();
    fd.append("file", f);
    fd.append("category", currentCategory || "all");
    try{
      const r = await apiFetch("/api/menu/upload_image", {method:"POST", body:fd});
      if(r.ok) ok += 1; else fail += 1;
    }catch(_){ fail += 1; }
  }
  await loadCategories();
  await loadItems();
  setMsg(`Upload complete. OK=${ok}, Fail=${fail}`, fail===0);
}

function setupDrop(){
  const dz = document.getElementById("dropZone");
  dz.addEventListener("dragover", e => { e.preventDefault(); dz.style.background="#ecfeff"; });
  dz.addEventListener("dragleave", () => { dz.style.background="#f8fbff"; });
  dz.addEventListener("drop", e => {
    e.preventDefault();
    dz.style.background="#f8fbff";
    const files = Array.from(e.dataTransfer.files || []).filter(f => /\\.(png|jpg|jpeg|webp)$/i.test(f.name));
    selectedFiles = files;
    document.getElementById("uploadInfo").textContent = `${selectedFiles.length} files selected`;
  });
}

async function bootstrap(){
  try{
    const ok = await authCheck();
    document.getElementById("loginRow").style.display = ok ? "none" : "";
    document.getElementById("loggedRow").style.display = ok ? "" : "none";
    if(!ok){
      setMsg("Please sign in.");
      return;
    }
    await loadCategories();
    await loadItems();
    setMsg("Ready.", true);
  }catch(e){
    setMsg(String(e && e.message || e));
  }
}

document.getElementById("filesInput").addEventListener("change", e => pickFilesFromInput(e.target));
document.getElementById("folderInput").addEventListener("change", e => pickFilesFromInput(e.target));
setupDrop();
bootstrap();
</script>
</body></html>"""
        from fastapi.responses import HTMLResponse
        return HTMLResponse(content=html)

    # ---- Health ----
    @app.get("/health")
    def health(request: Request) -> dict:
        meta = _request_base(request)
        return {
            "ok": True,
            "ts": _now(),
            "lan_ip": meta["lan_ip"],
            "canonical_base_local": meta["canonical_local"],
            "canonical_base_lan": meta["canonical_lan"],
            "request_base": meta["request_base"],
            "request_scheme": meta["request_scheme"],
            "request_host": meta["request_host"],
            "request_port": meta["request_port"],
            "db": os.path.abspath(db_path),
            "data_dir": str(dirs["DATA_DIR"]),
            "static_dir": str(dirs["STATIC_DIR"]),
            "menu_img_dir": str(dirs["MENU_IMG_DIR"]),
            "global_gallery_dir": str(dirs["GLOBAL_GALLERY_DIR"]),
            "local_server_dir": str(dirs["LOCAL_SERVER_DIR"]),
            "pdf_in_dir": str(dirs["PDF_IN_DIR"]),
            "pdf_done_dir": str(dirs["PDF_DONE_DIR"]),
            "persistence": dict(getattr(app.state, "persistence_info", {}) or {}),
            "env_hints": {
                "render": str(os.environ.get("RENDER", "")).strip().lower() == "true",
                "has_POS_HUB_DATA_DIR": bool(str(os.environ.get("POS_HUB_DATA_DIR", "")).strip()),
                "has_POS_HUB_DB_PATH": bool(str(os.environ.get("POS_HUB_DB_PATH", "")).strip()),
            },
        }

    @app.get("/.well-known/jwks.json")
    def jwks() -> dict:
        alg = _jwt_alg()
        if alg != "RS256":
            return {"keys": [], "alg": alg, "warning": "JWKS available only when POS_HUB_JWT_ALG=RS256"}
        return {"keys": [_jwt_public_jwk()]}

    @app.get("/.well-known/auth-meta")
    def auth_meta() -> dict:
        out = {
            "issuer": _jwt_iss(),
            "audience": _jwt_aud(),
            "alg": _jwt_alg(),
            "access_ttl_sec": _jwt_access_ttl_sec(),
            "refresh_ttl_sec": _jwt_refresh_ttl_sec(),
        }
        if _jwt_alg() == "RS256":
            out["jwks_uri"] = "/.well-known/jwks.json"
            out["kid"] = _jwt_kid()
        return out

    @app.get("/debug/auth")
    def debug_auth(request: Request) -> dict:
        got = request.headers.get("x-api-key")
        got_norm = _norm_key(got)
        exp_norm = _norm_key(api_key)

        return {
            "has_x_api_key_header": got is not None,
            "received_len": len(got_norm),
            "received_mask": _mask_key(got_norm),
            "expected_len": len(exp_norm),
            "expected_mask": _mask_key(exp_norm),
            "strip_compare_ok": got_norm == exp_norm,
            "header_keys": sorted(list(request.headers.keys())),
        }

    # ---- Events ----
    @app.get("/events")
    def events(after: int = 0, limit: int = 200, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        con = _connect(db_path)
        try:
            rows = con.execute(
                "SELECT seq, ts, type, payload_json FROM events WHERE seq > ? ORDER BY seq ASC LIMIT ?",
                (after, min(max(limit, 1), 1000)),
            ).fetchall()
            out = []
            for r in rows:
                out.append(
                    {
                        "seq": int(r["seq"]),
                        "ts": r["ts"],
                        "type": r["type"],
                        "payload": json.loads(r["payload_json"] or "{}"),
                    }
                )
            return {"events": out, "last_seq": out[-1]["seq"] if out else after}
        finally:
            con.close()

    @app.websocket("/ws")
    async def ws_endpoint(ws: WebSocket):
        key = ws.query_params.get("key")
        if key != api_key:
            await ws.close(code=4401)
            return
        await ws.accept()
        with ws_lock:
            ws_clients.add(ws)
        try:
            while True:
                await ws.receive_text()
        except WebSocketDisconnect:
            pass
        finally:
            with ws_lock:
                ws_clients.discard(ws)

    # ---- KV (root; kept for backward compatibility) ----
    @app.get("/kv/{key}")
    def kv_get(
        key: str,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        key_scoped = _scoped_kv_key((key or "").strip(), tenant_id, location_id)
        con = _connect(db_path)
        try:
            row = con.execute("SELECT key, value, updated_at FROM pos_kv WHERE key=?", (key_scoped,)).fetchone()
            if not row and (str(tenant_id or "").strip() or str(location_id or "").strip()):
                row = con.execute("SELECT key, value, updated_at FROM pos_kv WHERE key=?", ((key or "").strip(),)).fetchone()
            if row:
                return {"key": (key or "").strip(), "value": row["value"], "updated_at": row["updated_at"]}
        finally:
            con.close()

        fb = _kv_get_with_fallback(key, tenant_id, location_id)
        if fb not in ({}, None):
            return {"key": (key or "").strip(), "value": _json_dumps(fb), "updated_at": _now()}
        raise HTTPException(status_code=404, detail="Key not found")

    @app.post("/kv")
    def kv_set(body: KVSet, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(body.tenant_id, body.location_id)
        key_db = _scoped_kv_key(body.key, body.tenant_id, body.location_id)
        con = _connect(db_path)
        try:
            con.execute(
                "INSERT INTO pos_kv(key,value,updated_at) VALUES(?,?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
                (key_db, body.value, _now()),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(
            db_path,
            "kv.updated",
            {
                "key": body.key,
                "tenant_id": (body.tenant_id or "").strip(),
                "location_id": (body.location_id or "").strip(),
            },
        )
        try:
            import anyio
            anyio.from_thread.run(
                _broadcast,
                {
                    "type": "kv.updated",
                    "seq": seq,
                    "key": body.key,
                    "tenant_id": (body.tenant_id or "").strip(),
                    "location_id": (body.location_id or "").strip(),
                },
            )
        except Exception:
            pass
        return {"ok": True, "seq": seq}

    # ---- Menu helper endpoints (root) ----
    def _next_id_payload() -> dict:
        con = _connect(db_path)
        try:
            return {"next_id": _menu_next_id(con)}
        finally:
            con.close()

    def _next_an_payload() -> dict:
        con = _connect(db_path)
        try:
            return {"next_article_number": _menu_next_article_number(con)}
        finally:
            con.close()

    @app.get("/menu/next_id")
    def menu_next_id(x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return _next_id_payload()

    @app.get("/menu/next-id")
    def menu_next_id_alias(x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return _next_id_payload()

    @app.get("/menu/next_article_number")
    def menu_next_article_number(x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return _next_an_payload()

    @app.get("/menu/next-article-number")
    def menu_next_article_number_alias(x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        return _next_an_payload()

    # ---- Menu (root) ----
    @app.get("/menu")
    def menu_list(
        request: Request,
        since: Optional[str] = None,
        main_category: Optional[str] = None,
        sub_category: Optional[str] = None,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        active_only: bool = False,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)
        return _menu_list_impl(request, since, main_category, sub_category, active_only, tenant_id, location_id)

    # ---- Zutaten / Ingredients helper ----
    @app.get("/ingredients")
    def ingredients(
        sub_category: str = "__INGREDIENTS__",
        active_only: bool = True,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        con = _connect(db_path)
        try:
            sql = "SELECT name FROM menu_items WHERE sub_category=?"
            params: list[Any] = [sub_category]
            if active_only:
                sql += " AND is_active=1"
            rows = con.execute(sql, tuple(params)).fetchall()
            vals = []
            for r in rows:
                s = (r["name"] or "").strip()
                if s:
                    vals.append(s)
            vals = sorted(set(vals), key=str.lower)
            return {"items": vals, "count": len(vals)}
        finally:
            con.close()

    @app.get("/ingredients-catalog")
    def ingredients_catalog_root(
        main_category: Optional[str] = None,
        active_only: bool = True,
        q: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        rows = _catalog_rows("ingredients_catalog", main_category, active_only, q)
        return {"items": rows, "count": len(rows)}

    @app.get("/sauces-catalog")
    def sauces_catalog_root(
        main_category: Optional[str] = None,
        active_only: bool = True,
        q: Optional[str] = None,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        rows = _catalog_rows("sauces_catalog", main_category, active_only, q)
        return {"items": rows, "count": len(rows)}

    # ---- Delivery Orders ----
    @app.post("/orders/delivery")
    def create_delivery_order(body: CreateDeliveryOrder, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(body.tenant_id, body.location_id)

        created_at = _now()
        updated_at = created_at
        ordernumber = body.ordernumber or str(uuid.uuid4())[:8]

        con = _connect(db_path)
        try:
            cur = con.cursor()
            cur.execute(
                """
                INSERT INTO lieferung_daily(
                    tenant_id, location_id,
                    store_id, register_id, tish, zeit, gesamtepreis, ordernumber,
                    telefonnummber, adresse, name, hausnummer, PLZ, stadt,
                    distance, driver, side, status, created_at, updated_at, finished_at
                ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    (body.tenant_id or "").strip(),
                    (body.location_id or "").strip(),
                    body.store_id,
                    body.register_id,
                    body.tish or "",
                    int(time.time()),
                    int(round((body.gesamtepreis or 0) * 100)),
                    ordernumber,
                    body.telefonnummber or "",
                    body.adresse or "",
                    body.name or "",
                    body.hausnummer or "",
                    body.PLZ or "",
                    body.stadt or "",
                    body.distance or "",
                    "",
                    body.side or "Android",
                    body.status or "In the Kitchen",
                    created_at,
                    updated_at,
                    None,
                ),
            )
            lieferung_id = int(cur.lastrowid)

            for it in body.items:
                item_payload = it.model_dump(by_alias=True, exclude_none=True)

                # Canonical rule:
                # - extras => extra ingredients only
                # - sauces are only in sauceOnItem / extraSauces
                extra_ingredients = item_payload.get("extraIngredients")
                if extra_ingredients is None and isinstance(item_payload.get("extras"), list):
                    extra_ingredients = item_payload.get("extras")
                if not isinstance(extra_ingredients, list):
                    extra_ingredients = []

                sauce_on_item = item_payload.get("sauceOnItem")
                if not isinstance(sauce_on_item, list):
                    sauce_on_item = []

                extra_sauces = item_payload.get("extraSauces")
                if not isinstance(extra_sauces, list):
                    extra_sauces = []

                item_payload["extraIngredients"] = extra_ingredients
                item_payload["extras"] = extra_ingredients  # legacy mirror for old clients
                item_payload["sauceOnItem"] = sauce_on_item
                item_payload["extraSauces"] = extra_sauces

                cur.execute(
                    "INSERT INTO lieferung_daily_items(lieferung_id,item_json) VALUES(?,?)",
                    (lieferung_id, json.dumps(item_payload, ensure_ascii=False)),
                )

            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "order.created", {"id": lieferung_id, "ordernumber": ordernumber})
        try:
            import anyio
            anyio.from_thread.run(
                _broadcast,
                {"type": "order.created", "seq": seq, "id": lieferung_id, "ordernumber": ordernumber},
            )
        except Exception:
            pass

        return {"ok": True, "id": lieferung_id, "ordernumber": ordernumber, "seq": seq}

    @app.get("/orders/delivery")
    def list_delivery_orders(
        status: Optional[str] = None,
        tenant_id: Optional[str] = None,
        location_id: Optional[str] = None,
        include_items: bool = False,
        x_api_key: Optional[str] = Header(default=None),
        x_device_id: Optional[str] = Header(default=None),
        x_is_main_pc: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        _enforce_tenant_access(tenant_id, location_id)

        # Main-PC delivery inbox guard (online best-practice):
        # - If client sends X-Is-Main-PC/X-Device-Id headers, enforce one main device per location.
        # - If headers are missing, keep legacy behavior for older clients.
        has_role_headers = bool(str(x_is_main_pc or "").strip()) or bool(str(x_device_id or "").strip())
        if has_role_headers:
            is_main = _to_bool(x_is_main_pc)
            device = str(x_device_id or "").strip()
            if not is_main:
                return {
                    "orders": [],
                    "main_pc_only": True,
                    "reason": "Only Main PC can receive online delivery inbox.",
                }
            if not device:
                raise HTTPException(status_code=400, detail="X-Device-Id required when X-Is-Main-PC is used.")

            lock = _get_delivery_main_device(db_path, location_id)
            lock_dev = str((lock or {}).get("device_id") or "").strip()
            if not lock_dev:
                lock = _set_delivery_main_device(db_path, location_id, device)
            elif lock_dev != device:
                raise HTTPException(
                    status_code=409,
                    detail=(
                        f"Main PC already assigned for location "
                        f"'{str(location_id or '').strip() or '__default__'}'."
                    ),
                )

        con = _connect(db_path)
        try:
            where = []
            params: list[Any] = []
            if status:
                where.append("status=?")
                params.append(status)
            if tenant_id is not None and str(tenant_id).strip() != "":
                where.append("tenant_id=?")
                params.append(str(tenant_id).strip())
            if location_id is not None and str(location_id).strip() != "":
                where.append("location_id=?")
                params.append(str(location_id).strip())
            sql = "SELECT * FROM lieferung_daily"
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY created_at DESC"
            rows = con.execute(sql, tuple(params)).fetchall()

            out = []
            for r in rows:
                o = dict(r)
                o["ID"] = int(o["ID"])
                try:
                    o["gesamtepreis_eur"] = (int(o.get("gesamtepreis") or 0) / 100.0)
                except Exception:
                    o["gesamtepreis_eur"] = 0.0

                if include_items:
                    items_rows = con.execute(
                        "SELECT item_json FROM lieferung_daily_items WHERE lieferung_id=? ORDER BY id ASC",
                        (o["ID"],),
                    ).fetchall()
                    items = []
                    for ir in items_rows:
                        try:
                            items.append(json.loads(ir["item_json"]))
                        except Exception:
                            pass
                    o["items"] = items
                out.append(o)

            resp = {"orders": out}
            if has_role_headers:
                resp["main_pc_only"] = True
                resp["location_id"] = str(location_id or "").strip()
                resp["main_device_id"] = str(x_device_id or "").strip()
            return resp
        finally:
            con.close()

    @app.put("/orders/delivery/{lieferung_id}")
    def update_delivery_order(
        lieferung_id: int,
        body: UpdateDeliveryOrder,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)

        updates: dict[str, Any] = {}
        if body.status is not None:
            updates["status"] = body.status
            if body.status in ("Delivered", "Canceled", "Completed") and not body.finished_at:
                updates["finished_at"] = _now()

        if body.driver is not None:
            updates["driver"] = body.driver

        if body.gesamtepreis is not None:
            updates["gesamtepreis"] = int(round(float(body.gesamtepreis) * 100))

        updates["updated_at"] = body.updated_at or _now()

        if not updates:
            return {"ok": True, "seq": None}

        set_sql = ", ".join([f"{k}=?" for k in updates.keys()])
        params = list(updates.values()) + [lieferung_id]

        con = _connect(db_path)
        try:
            cur = con.cursor()
            cur.execute(f"UPDATE lieferung_daily SET {set_sql} WHERE ID=?", params)
            if cur.rowcount == 0:
                raise HTTPException(status_code=404, detail="Order not found")
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "order.updated", {"id": lieferung_id, "fields": list(updates.keys())})
        try:
            import anyio
            anyio.from_thread.run(
                _broadcast,
                {"type": "order.updated", "seq": seq, "id": lieferung_id, "fields": list(updates.keys())},
            )
        except Exception:
            pass

        return {"ok": True, "seq": seq}

    # ==========================================================
    # Multi-tenant Auth (JWT + Refresh + per-tenant API keys)
    # ==========================================================
    _auth_rate_lock = threading.Lock()
    _auth_rate_hits: dict[str, list[float]] = {}

    def _rate_limit_guard(bucket: str, max_hits: int = 12, window_sec: int = 60) -> None:
        nowf = time.time()
        key = str(bucket or "global").strip() or "global"
        with _auth_rate_lock:
            arr = list(_auth_rate_hits.get(key, []))
            arr = [x for x in arr if (nowf - x) <= float(window_sec)]
            if len(arr) >= int(max_hits):
                raise HTTPException(status_code=429, detail="Too many requests")
            arr.append(nowf)
            _auth_rate_hits[key] = arr

    def _scopes_list(v: Any) -> list[str]:
        if isinstance(v, list):
            return [str(x).strip() for x in v if str(x).strip()]
        if isinstance(v, str) and v.strip():
            return [x.strip() for x in v.split(",") if x.strip()]
        return []

    @app.post("/auth/clients/create")
    @api.post("/auth/clients/create")
    def auth_client_create(body: AuthClientCreateRequest, x_api_key: Optional[str] = Header(default=None)) -> dict:
        auth_obj = _auth(x_api_key)
        if str(auth_obj.get("kind") or "") not in {"legacy_api_key"}:
            raise HTTPException(status_code=403, detail="Insufficient privilege")
        tenant_id = str(body.tenant_id or "").strip()
        client_id = str(body.client_id or "").strip()
        if not tenant_id or not client_id:
            raise HTTPException(status_code=400, detail="tenant_id and client_id required")
        raw_secret = str(body.secret or "").strip() or f"cs_{secrets.token_urlsafe(24)}"
        secret_hash = hashlib.sha256(raw_secret.encode("utf-8")).hexdigest()
        scopes = [str(x).strip() for x in (body.scopes or []) if str(x).strip()]
        con = _connect(db_path)
        try:
            con.execute(
                """
                INSERT INTO auth_clients(tenant_id, client_id, client_secret_hash, subject, scopes_json, location_id, active, created_at, updated_at)
                VALUES(?,?,?,?,?,?,?,?,?)
                ON CONFLICT(tenant_id, client_id) DO UPDATE SET
                  client_secret_hash=excluded.client_secret_hash,
                  subject=excluded.subject,
                  scopes_json=excluded.scopes_json,
                  location_id=excluded.location_id,
                  active=1,
                  updated_at=excluded.updated_at
                """,
                (
                    tenant_id,
                    client_id,
                    secret_hash,
                    str(body.subject or "").strip() or client_id,
                    json.dumps(scopes, ensure_ascii=False),
                    str(body.location_id or "").strip(),
                    1,
                    _now(),
                    _now(),
                ),
            )
            con.commit()
        finally:
            con.close()
        return {
            "ok": True,
            "tenant_id": tenant_id,
            "client_id": client_id,
            "client_secret": raw_secret,
            "scope": scopes,
            "location_id": str(body.location_id or "").strip(),
        }

    @app.post("/auth/login")
    @api.post("/auth/login")
    def auth_login(body: AuthLoginRequest) -> dict:
        _rate_limit_guard(f"login:{body.tenant_id}:{body.client_id}", max_hits=10, window_sec=60)
        tenant_id = str(body.tenant_id or "").strip()
        client_id = str(body.client_id or "").strip()
        secret = str(body.client_secret or "")
        if not tenant_id or not client_id or not secret:
            raise HTTPException(status_code=400, detail="tenant_id, client_id, client_secret required")

        con = _connect(db_path)
        try:
            row = con.execute(
                """
                SELECT tenant_id, client_id, client_secret_hash, subject, scopes_json, location_id, active
                FROM auth_clients
                WHERE tenant_id=? AND client_id=?
                LIMIT 1
                """,
                (tenant_id, client_id),
            ).fetchone()
            if not row or int(row["active"] or 0) != 1:
                raise HTTPException(status_code=401, detail="Invalid credentials")
            secret_hash = hashlib.sha256(secret.encode("utf-8")).hexdigest()
            if not hmac.compare_digest(str(row["client_secret_hash"] or ""), secret_hash):
                raise HTTPException(status_code=401, detail="Invalid credentials")

            scopes = _scopes_list(json.loads(row["scopes_json"] or "[]") if str(row["scopes_json"] or "").strip() else [])
            subject = str(row["subject"] or "").strip() or client_id
            location_id = str(body.location_id or row["location_id"] or "").strip()

            access_token, access_claims = _jwt_issue_access_token(
                tenant_id=tenant_id,
                subject=subject,
                client_id=client_id,
                scopes=scopes,
                location_id=location_id,
            )
            refresh_raw = secrets.token_urlsafe(48)
            refresh_exp = _jwt_now() + _jwt_refresh_ttl_sec()
            _save_refresh_token(
                token_raw=refresh_raw,
                tenant_id=tenant_id,
                client_id=client_id,
                subject=subject,
                location_id=location_id,
                scopes=scopes,
                jti=str(access_claims.get("jti") or ""),
                exp_ts=refresh_exp,
            )
            return {
                "token_type": "bearer",
                "access_token": access_token,
                "access_expires_in": _jwt_access_ttl_sec(),
                "refresh_token": refresh_raw,
                "refresh_expires_in": _jwt_refresh_ttl_sec(),
                "tenant_id": tenant_id,
                "client_id": client_id,
                "location_id": location_id,
                "scope": scopes,
                "iss": _jwt_iss(),
                "aud": _jwt_aud(),
            }
        finally:
            con.close()

    @app.post("/auth/refresh")
    @api.post("/auth/refresh")
    def auth_refresh(body: AuthRefreshRequest) -> dict:
        _rate_limit_guard("refresh", max_hits=30, window_sec=60)
        old_raw = str(body.refresh_token or "").strip()
        if not old_raw:
            raise HTTPException(status_code=400, detail="refresh_token required")

        old = _revoke_refresh_token(old_raw)
        if not old:
            raise HTTPException(status_code=401, detail="Invalid refresh token")
        if old.get("revoked_at") is not None:
            raise HTTPException(status_code=401, detail="Refresh token already used/revoked")
        if int(old.get("expires_at") or 0) <= _jwt_now():
            raise HTTPException(status_code=401, detail="Refresh token expired")

        tenant_id = str(old.get("tenant_id") or "").strip()
        client_id = str(old.get("client_id") or "").strip()
        subject = str(old.get("subject") or "").strip() or client_id
        location_id = str(old.get("location_id") or "").strip()
        scopes = _scopes_list(old.get("scope"))

        access_token, access_claims = _jwt_issue_access_token(
            tenant_id=tenant_id,
            subject=subject,
            client_id=client_id,
            scopes=scopes,
            location_id=location_id,
        )
        new_refresh = secrets.token_urlsafe(48)
        new_hash = hashlib.sha256(new_refresh.encode("utf-8")).hexdigest()
        _save_refresh_token(
            token_raw=new_refresh,
            tenant_id=tenant_id,
            client_id=client_id,
            subject=subject,
            location_id=location_id,
            scopes=scopes,
            jti=str(access_claims.get("jti") or ""),
            exp_ts=_jwt_now() + _jwt_refresh_ttl_sec(),
            rotated_from_hash=str(old.get("token_hash") or ""),
        )
        # Mark previous token rotation linkage.
        con = _connect(db_path)
        try:
            con.execute(
                "UPDATE auth_refresh_tokens SET replaced_by_hash=? WHERE token_hash=?",
                (new_hash, str(old.get("token_hash") or "")),
            )
            con.commit()
        finally:
            con.close()
        return {
            "token_type": "bearer",
            "access_token": access_token,
            "access_expires_in": _jwt_access_ttl_sec(),
            "refresh_token": new_refresh,
            "refresh_expires_in": _jwt_refresh_ttl_sec(),
            "tenant_id": tenant_id,
            "client_id": client_id,
            "location_id": location_id,
            "scope": scopes,
            "iss": _jwt_iss(),
            "aud": _jwt_aud(),
        }

    @app.post("/auth/revoke")
    @api.post("/auth/revoke")
    def auth_revoke(body: AuthRevokeRequest, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        tok = str(body.refresh_token or "").strip()
        if not tok:
            raise HTTPException(status_code=400, detail="refresh_token required")
        old = _revoke_refresh_token(tok)
        return {"ok": bool(old)}

    @app.post("/auth/api-keys/create")
    @api.post("/auth/api-keys/create")
    def auth_api_key_create(body: ApiKeyCreateRequest, x_api_key: Optional[str] = Header(default=None)) -> dict:
        auth_obj = _auth(x_api_key)
        # Only legacy/static key may create/revoke API keys (operator/admin task).
        if str(auth_obj.get("kind") or "") not in {"legacy_api_key"}:
            raise HTTPException(status_code=403, detail="Insufficient privilege")
        tenant_id = str(body.tenant_id or "").strip()
        if not tenant_id:
            raise HTTPException(status_code=400, detail="tenant_id required")
        raw = f"pk_{secrets.token_urlsafe(32)}"
        kh = _api_key_hash(raw)
        pref = raw[:10]
        ex_days = int(body.expires_in_days or 0)
        expires_at = None
        if ex_days > 0:
            expires_at = _jwt_now() + (ex_days * 24 * 3600)
        con = _connect(db_path)
        try:
            con.execute(
                """
                INSERT INTO auth_api_keys(tenant_id, location_id, key_hash, key_prefix, name, scopes_json, active, created_at, expires_at, revoked_at)
                VALUES(?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    tenant_id,
                    str(body.location_id or "").strip(),
                    kh,
                    pref,
                    str(body.name or "default").strip() or "default",
                    json.dumps([str(x).strip() for x in (body.scopes or []) if str(x).strip()], ensure_ascii=False),
                    1,
                    _now(),
                    expires_at,
                    None,
                ),
            )
            key_id = int(con.execute("SELECT last_insert_rowid() AS i").fetchone()["i"])
            con.commit()
        finally:
            con.close()
        return {"ok": True, "key_id": key_id, "tenant_id": tenant_id, "api_key": raw, "key_prefix": pref, "expires_at": expires_at}

    @app.get("/auth/api-keys")
    @api.get("/auth/api-keys")
    def auth_api_keys_list(tenant_id: str, x_api_key: Optional[str] = Header(default=None)) -> dict:
        auth_obj = _auth(x_api_key)
        if str(auth_obj.get("kind") or "") not in {"legacy_api_key"}:
            raise HTTPException(status_code=403, detail="Insufficient privilege")
        con = _connect(db_path)
        try:
            rows = con.execute(
                """
                SELECT id, tenant_id, location_id, key_prefix, name, scopes_json, active, created_at, expires_at, revoked_at
                FROM auth_api_keys
                WHERE tenant_id=?
                ORDER BY id DESC
                """,
                (str(tenant_id or "").strip(),),
            ).fetchall()
            out = []
            for r in rows:
                out.append({
                    "id": int(r["id"]),
                    "tenant_id": str(r["tenant_id"] or ""),
                    "location_id": str(r["location_id"] or ""),
                    "key_prefix": str(r["key_prefix"] or ""),
                    "name": str(r["name"] or ""),
                    "scopes": _scopes_list(json.loads(r["scopes_json"] or "[]") if str(r["scopes_json"] or "").strip() else []),
                    "active": bool(int(r["active"] or 0)),
                    "created_at": str(r["created_at"] or ""),
                    "expires_at": r["expires_at"],
                    "revoked_at": r["revoked_at"],
                })
            return {"items": out, "count": len(out)}
        finally:
            con.close()

    @app.post("/auth/api-keys/revoke")
    @api.post("/auth/api-keys/revoke")
    def auth_api_key_revoke(body: ApiKeyRevokeRequest, x_api_key: Optional[str] = Header(default=None)) -> dict:
        auth_obj = _auth(x_api_key)
        if str(auth_obj.get("kind") or "") not in {"legacy_api_key"}:
            raise HTTPException(status_code=403, detail="Insufficient privilege")
        con = _connect(db_path)
        try:
            cur = con.cursor()
            cur.execute(
                "UPDATE auth_api_keys SET active=0, revoked_at=? WHERE id=?",
                (_jwt_now(), int(body.key_id)),
            )
            con.commit()
            return {"ok": bool(int(cur.rowcount or 0) > 0)}
        finally:
            con.close()

    # ==========================================================
    # PIN / Employees (SQLite, no Firebase)  (kept from your version)
    # ==========================================================
    def _try_dpapi_decrypt_name(s: str) -> str:
        raw = (s or "").strip()
        if not raw:
            return ""
        if not raw.startswith("enc:"):
            return raw
        try:
            import win32crypt  # pywin32
            blob = base64.b64decode(raw.split("enc:", 1)[1])
            dec = win32crypt.CryptUnprotectData(blob, None, None, None, 0)[1]
            out = dec.decode("utf-8", "ignore").strip()
            return out or "Mitarbeiter"
        except Exception:
            return "Mitarbeiter"

    def _iter_employee_sources() -> list[str]:
        paths = [db_path]
        try:
            # Common local layout: online_OrderData.db + online_Einstellung.db in same folder.
            paths.append(str((Path(db_path).resolve().parent / "online_Einstellung.db").resolve()))
        except Exception:
            pass
        try:
            paths.append(str((_default_data_dir() / "online_Einstellung.db").resolve()))
        except Exception:
            pass
        try:
            # Fallback to app-root Data folder (important when POS_HUB_DATA_DIR points elsewhere).
            paths.append(str((_app_root() / "Data" / "online_Einstellung.db").resolve()))
        except Exception:
            pass
        try:
            # CWD fallback for development runs.
            paths.append(str((Path.cwd() / "Data" / "online_Einstellung.db").resolve()))
        except Exception:
            pass


        out = []
        for p in paths:
            if p and p not in out and os.path.exists(p):
                out.append(p)
        return out

    def _table_exists(con: sqlite3.Connection, name: str) -> bool:
        r = con.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=? LIMIT 1", (name,)).fetchone()
        return bool(r)

    def _bytes_from_any(v) -> Optional[bytes]:
        if v is None:
            return None
        if isinstance(v, (bytes, bytearray)):
            return bytes(v)
        s = str(v).strip()
        if not s:
            return None
        try:
            return base64.b64decode(s)
        except Exception:
            pass
        try:
            return bytes.fromhex(s)
        except Exception:
            return None

    def _verify_pin_row(pin: str, row: sqlite3.Row) -> bool:
        typed = str(pin or "").strip()
        if not typed:
            return False

        _arabic_digits = str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789")

        def _norm_pin_text(s: str) -> str:
            return str(s or "").strip().translate(_arabic_digits)

        def _pin_candidates(s: str) -> list[str]:
            src = _norm_pin_text(s)
            out: list[str] = []

            def _add(v: str):
                v = _norm_pin_text(v)
                if v and v not in out:
                    out.append(v)

            _add(src)
            digits = "".join(ch for ch in src if ch.isdigit())
            _add(digits)
            if len(digits) >= 4:
                _add(digits[-4:])
            if len(digits) >= 6:
                _add(digits[-6:])

            # Allow "EMP_ID + PIN" inputs like "4177+0456", "4177 0456", "41770456"
            for sep in ("+", "-", " ", "/", "|", ":", ";", ","):
                if sep in src:
                    parts = [p for p in src.split(sep) if p]
                    if parts:
                        _add(parts[-1])
                        p_digits = "".join(ch for ch in parts[-1] if ch.isdigit())
                        _add(p_digits)
                        if len(p_digits) >= 4:
                            _add(p_digits[-4:])
            return out

        candidates = _pin_candidates(typed)
        if not candidates:
            return False

        for k in ("password", "pin", "pin_plain"):
            if k in row.keys():
                stored_plain = _norm_pin_text(str(row[k] or "").strip())
                for cand in candidates:
                    if stored_plain == cand:
                        return True

        method = ""
        for k in ("method", "hash_method", "pw_method"):
            if k in row.keys():
                method = str(row[k] or "").strip()
                break

        salt = None
        for k in ("salt", "pw_salt", "password_salt"):
            if k in row.keys():
                salt = _bytes_from_any(row[k])
                break

        hsh = None
        for k in ("hash", "pw_hash", "password_hash"):
            if k in row.keys():
                hsh = _bytes_from_any(row[k])
                break

        if salt and hsh:
            iters_candidates = [200_000, 150_000, 120_000, 100_000, 80_000, 50_000, 20_000, 10_000]
            try:
                parts = method.split("_")
                for part in parts:
                    if part.isdigit():
                        m_it = int(part)
                        if m_it > 0 and m_it not in iters_candidates:
                            iters_candidates.insert(0, m_it)
                        else:
                            iters_candidates.remove(m_it)
                            iters_candidates.insert(0, m_it)
                        break
            except Exception:
                pass

            dklen = len(hsh)
            try:
                for raw_cand in candidates:
                    for iters in iters_candidates:
                        cand = hashlib.pbkdf2_hmac("sha256", raw_cand.encode("utf-8"), salt, iters, dklen=dklen)
                        if hmac.compare_digest(cand, hsh):
                            return True
                return False
            except Exception:
                return False

        return False

    def _find_employee_by_pin(pin: str) -> Optional[dict]:
        tables = ["Employes", "employees", "employes", "mitarbeiter", "Mitarbeiter"]

        for p in _iter_employee_sources():
            try:
                con = _connect(p)
                try:
                    for t in tables:
                        if not _table_exists(con, t):
                            continue
                        rows = con.execute(f"SELECT * FROM {t}").fetchall()
                        for r in rows:
                            if _verify_pin_row(pin, r):
                                eid = None
                                for k in ("id", "ID", "employe_id", "employee_id"):
                                    if k in r.keys():
                                        eid = r[k]
                                        break

                                name_raw = ""
                                for k in ("name", "Name", "employe_name", "employee_name"):
                                    if k in r.keys():
                                        name_raw = str(r[k] or "").strip()
                                        break

                                role = ""
                                for k in ("role", "Role", "employee_role", "employe_role"):
                                    if k in r.keys():
                                        role = str(r[k] or "").strip()
                                        break

                                return {
                                    "id": eid,
                                    "employee_id": eid,
                                    "name": name_raw,
                                    "employee_name": name_raw,
                                    "employee_name_display": _try_dpapi_decrypt_name(name_raw),
                                    "role": role,
                                }
                finally:
                    con.close()
            except Exception:
                continue

        return None

    def _extract_employee_fields(r: sqlite3.Row) -> dict:
        # make key lookup case-insensitive
        keymap = {k.lower(): k for k in r.keys()}

        def get_ci(*names, default=None):
            for n in names:
                kk = keymap.get(n.lower())
                if kk is not None:
                    return r[kk]
            return default

        eid = get_ci("id", "employe_id", "employee_id", "ID")
        name_raw = str(get_ci("name", "employe_name", "employee_name", "Name", default="") or "").strip()
        role = str(get_ci("role", "employee_role", "employe_role", "Role", default="") or "").strip()

        is_active = True
        v = get_ci("is_active", "active", "enabled", default=None)
        if v is not None:
            try:
                is_active = bool(int(v or 0))
            except Exception:
                is_active = bool(v)

        # decrypt name if your code does that
        name = _try_dpapi_decrypt_name(name_raw)

        return {
            "id": eid,
            "name": name,
            "role": role,
            "is_active": is_active,
        }

    def _list_employees_basic(active_only: bool = True) -> list[dict]:
        tables = ["Employes", "employees", "employes", "mitarbeiter", "Mitarbeiter"]
        items: list[dict] = []
        seen = set()
        skipped_inactive = 0

        for p in _iter_employee_sources():
            try:
                con = _connect(p)
                try:
                    for t in tables:
                        if not _table_exists(con, t):
                            continue
                        rows = con.execute(f"SELECT * FROM {t}").fetchall()
                        for r in rows:
                            e = _extract_employee_fields(r)

                            # normalize id
                            eid = e.get("id")
                            if eid is None:
                                continue
                            try:
                                eid_int = int(eid)
                            except Exception:
                                # keep non-int ids but still de-dupe
                                eid_int = str(eid)

                            if active_only and not e.get("is_active", True):
                                skipped_inactive += 1
                                continue

                            dedupe_key = (str(p), str(t), str(eid_int))
                            if dedupe_key in seen:
                                continue
                            seen.add(dedupe_key)

                            items.append({
                                "id": eid_int,
                                "name": e.get("name") or "Mitarbeiter",
                                "employe_name": e.get("name") or "Mitarbeiter",
                                "role": e.get("role") or "",
                            })
                finally:
                    con.close()
            except Exception:
                continue

        # final de-dupe across sources by id+name+role
        uniq = {}
        for it in items:
            k = (str(it["id"]), (it["name"] or "").strip().lower(), (it["role"] or "").strip().lower())
            uniq[k] = it

        out = list(uniq.values())
        out.sort(key=lambda x: (str(x.get("role") or "").lower(), str(x.get("name") or "").lower()))

        # Backward-compatible behavior:
        # many legacy Employes rows have is_active=0 although they are valid staff.
        # If active_only removed everything, return the collected rows without active filtering.
        if active_only and not out and skipped_inactive > 0:
            return _list_employees_basic(active_only=False)
        return out

    def _employees_from_kv_fallback() -> list[dict]:
        con = _connect(db_path)
        try:
            row = con.execute("SELECT value FROM pos_kv WHERE key=? LIMIT 1", ("employees_public",)).fetchone()
        finally:
            con.close()
        if not row:
            return []
        try:
            data = json.loads(row["value"] or "{}")
        except Exception:
            return []
        src = data.get("items") if isinstance(data, dict) else None
        if not isinstance(src, list):
            return []
        out: list[dict] = []
        for it in src:
            if not isinstance(it, dict):
                continue
            eid = it.get("id")
            try:
                eid = int(eid)
            except Exception:
                if eid is None:
                    continue
            nm = (it.get("name") or it.get("employe_name") or it.get("employee_name") or "Mitarbeiter")
            out.append({
                "id": eid,
                "name": nm,
                "employe_name": nm,
                "role": it.get("role") or "",
            })
        return out

    @app.post("/auth/pin")
    @api.post("/auth/pin")
    async def auth_pin(request: Request, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)

        payload = await _read_payload_any(request)
        if not isinstance(payload, dict):
            payload = {}

        def _pick(*keys: str) -> str:
            for k in keys:
                v = payload.get(k)
                if v is not None and str(v).strip():
                    return str(v).strip()
            return ""

        # doc contract: {"pin":"1234"}
        # keep very tolerant for legacy Android clients:
        raw_code = _pick(
            "pin", "PIN", "Pin",
            "password", "Password", "pass", "pw",
            "code", "Code", "employee_code", "employeeCode", "employee_pin", "employeePin",
        )

        # fallback from query string if body was empty
        if not raw_code:
            try:
                q = request.query_params
                raw_code = (
                    (q.get("pin") or "").strip()
                    or (q.get("password") or "").strip()
                    or (q.get("code") or "").strip()
                )
            except Exception:
                raw_code = ""

        # fallback from raw body for legacy clients sending plain text or urlencoded strings
        if not raw_code:
            try:
                rb = (await request.body() or b"").decode("utf-8", "ignore").strip()
            except Exception:
                rb = ""
            if rb:
                # plain value: "1234"
                raw_code = rb.strip("\"' \t\r\n")
                # urlencoded-like: "pin=1234" / "password=1234&x=.."
                m = re.search(r"(?:^|[&\\s])(pin|password|code|employee_pin|employeeCode)=([^&\\s]+)", rb, re.I)
                if m:
                    raw_code = (m.group(2) or "").strip()

        emp = _find_employee_by_pin(raw_code)
        if not emp:
            return {"ok": False}
        # extra aliases for legacy Android parsers
        try:
            emp.setdefault("employe_id", emp.get("employee_id") or emp.get("id"))
            emp.setdefault("employe_name", emp.get("employee_name_display") or emp.get("employee_name") or emp.get("name"))
        except Exception:
            pass
        seq = _emit_event(db_path, "auth.pin", {"employee_id": emp.get("id"), "role": emp.get("role")})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "auth.pin", "seq": seq, "employee_id": emp.get("id")})
        except Exception:
            pass
        return {"ok": True, "employee": emp}

    # New: Employee list for Android (safe fields only)


    # Optional backward-compat alias (root)
    @app.get("/employees")
    def employees_list(
            active_only: bool = True,
            x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        items = _list_employees_basic(active_only=bool(active_only))
        if not items:
            items = _employees_from_kv_fallback()
        return {"items": items, "count": len(items)}

    # ==========================================================
    # Vouchers / Gutscheine
    # ==========================================================
    @app.get("/vouchers")
    def vouchers_list(
        include_encrypted: int = 0,
        active_only: bool = True,
        q: str = "",
        limit: int = 500,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        con = _connect(db_path)
        try:
            where = []
            params: list[Any] = []
            if active_only:
                where.append("is_active=1")
            if q:
                where.append("(voucher_id LIKE ?)")
                params.append(f"%{q.strip()}%")

            sql = (
                "SELECT voucher_id, amount_cents, created_at, updated_at, is_active"
                + (", encrypted" if include_encrypted else "")
                + " FROM vouchers"
            )
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY updated_at DESC LIMIT ?"
            params.append(min(max(int(limit), 1), 2000))

            rows = con.execute(sql, tuple(params)).fetchall()
            items = []
            for r in rows:
                it = {
                    "voucher_id": r["voucher_id"],
                    "amount_cents": int(r["amount_cents"] or 0),
                    "created_at": r["created_at"],
                    "updated_at": r["updated_at"],
                    "is_active": int(r["is_active"] or 0),
                }
                if include_encrypted:
                    it["encrypted"] = r["encrypted"]
                items.append(it)
            return {"items": items}
        finally:
            con.close()

    @app.get("/vouchers/{voucher_id}")
    def vouchers_get(voucher_id: str, include_encrypted: int = 1, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        vid = (voucher_id or "").strip()
        if not vid:
            raise HTTPException(status_code=400, detail="voucher_id required")

        con = _connect(db_path)
        try:
            r = con.execute(
                "SELECT voucher_id, amount_cents, created_at, updated_at, is_active, encrypted FROM vouchers WHERE voucher_id=?",
                (vid,),
            ).fetchone()
            if not r:
                raise HTTPException(status_code=404, detail="Voucher not found")
            out = {
                "voucher_id": r["voucher_id"],
                "amount_cents": int(r["amount_cents"] or 0),
                "created_at": r["created_at"],
                "updated_at": r["updated_at"],
                "is_active": int(r["is_active"] or 0),
            }
            if int(include_encrypted) == 1:
                out["encrypted"] = r["encrypted"]
            return out
        finally:
            con.close()

    @app.get("/vouchers/{voucher_id}/tx")
    def vouchers_tx(voucher_id: str, limit: int = 200, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        vid = (voucher_id or "").strip()
        con = _connect(db_path)
        try:
            rows = con.execute(
                """
                SELECT ts, delta_cents, invoice_number, note, employee_id, employee_name, employee_role
                FROM voucher_tx
                WHERE voucher_id=?
                ORDER BY id DESC
                LIMIT ?
                """,
                (vid, min(max(int(limit), 1), 2000)),
            ).fetchall()
            out = []
            for r in rows:
                out.append(
                    {
                        "ts": r["ts"],
                        "delta_cents": int(r["delta_cents"] or 0),
                        "invoice_number": r["invoice_number"] or "",
                        "note": r["note"] or "",
                        "employee_id": r["employee_id"] or "",
                        "employee_name": r["employee_name"] or "",
                        "employee_role": r["employee_role"] or "",
                    }
                )
            return {"items": out}
        finally:
            con.close()

    @app.post("/vouchers/upsert")
    def vouchers_upsert(body: VoucherUpsert, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)

        vid = (body.voucher_id or "").strip()
        enc = (body.encrypted or "").strip()
        if not vid or not enc:
            raise HTTPException(status_code=400, detail="voucher_id + encrypted required")

        now = _now()
        emp = body.employee or {}
        emp_id = str(emp.get("id") or emp.get("employee_id") or "")
        emp_name = str(emp.get("employee_name_display") or emp.get("employee_name") or emp.get("name") or "")
        emp_role = str(emp.get("role") or "")

        con = _connect(db_path)
        try:
            cur = con.cursor()
            prev = cur.execute("SELECT amount_cents, created_at FROM vouchers WHERE voucher_id=?", (vid,)).fetchone()
            if prev:
                old_amount = int(prev["amount_cents"] or 0)
                created_at = prev["created_at"] or now
                cur.execute(
                    """
                    UPDATE vouchers
                    SET encrypted=?, amount_cents=?, updated_at=?, is_active=1
                    WHERE voucher_id=?
                    """,
                    (enc, int(body.amount_cents or 0), now, vid),
                )
            else:
                old_amount = 0
                created_at = now
                cur.execute(
                    """
                    INSERT INTO vouchers(voucher_id, encrypted, amount_cents, created_at, updated_at, is_active)
                    VALUES(?,?,?,?,?,1)
                    """,
                    (vid, enc, int(body.amount_cents or 0), created_at, now),
                )

            new_amount = int(body.amount_cents or 0)
            delta = new_amount - old_amount
            if delta != 0:
                cur.execute(
                    """
                    INSERT INTO voucher_tx(voucher_id, ts, delta_cents, invoice_number, note, employee_id, employee_name, employee_role)
                    VALUES(?,?,?,?,?,?,?,?)
                    """,
                    (
                        vid,
                        now,
                        int(delta),
                        (body.invoice_number or "").strip(),
                        (body.note or "").strip(),
                        emp_id,
                        emp_name,
                        emp_role,
                    ),
                )

            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "voucher.upsert", {"voucher_id": vid, "amount_cents": int(body.amount_cents or 0)})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "voucher.upsert", "seq": seq, "voucher_id": vid})
        except Exception:
            pass

        return {"ok": True, "voucher_id": vid, "amount_cents": int(body.amount_cents or 0), "updated_at": now, "seq": seq}

    @app.post("/vouchers/delete")
    def vouchers_delete(body: VoucherDelete, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        vid = (body.voucher_id or "").strip()
        if not vid:
            raise HTTPException(status_code=400, detail="voucher_id required")

        now = _now()
        emp = body.employee or {}
        emp_id = str(emp.get("id") or emp.get("employee_id") or "")
        emp_name = str(emp.get("employee_name_display") or emp.get("employee_name") or emp.get("name") or "")
        emp_role = str(emp.get("role") or "")

        con = _connect(db_path)
        try:
            cur = con.cursor()
            cur.execute("UPDATE vouchers SET is_active=0, updated_at=? WHERE voucher_id=?", (now, vid))
            if cur.rowcount == 0:
                raise HTTPException(status_code=404, detail="Voucher not found")
            cur.execute(
                """
                INSERT INTO voucher_tx(voucher_id, ts, delta_cents, invoice_number, note, employee_id, employee_name, employee_role)
                VALUES(?,?,?,?,?,?,?,?)
                """,
                (vid, now, 0, "", "deleted", emp_id, emp_name, emp_role),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "voucher.delete", {"voucher_id": vid})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "voucher.delete", "seq": seq, "voucher_id": vid})
        except Exception:
            pass

        return {"ok": True, "voucher_id": vid, "seq": seq}

    # ==========================================================
    # Reservations
    # ==========================================================
    def _normalize_reservation_status(s: Optional[str]) -> str:
        raw = (s or "").strip().lower()
        if raw in ("booked", "waiting", "arrived", "cancelled"):
            return raw
        return "booked"

    @app.get("/reservations/list")
    @api.get("/reservations/list")
    def reservations_list(
        q: str = "",
        active_only: bool = True,
        limit: int = 1000,
        x_api_key: Optional[str] = Header(default=None),
    ) -> dict:
        _auth(x_api_key)
        con = _connect(db_path)
        try:
            where = []
            params: list[Any] = []
            if active_only:
                where.append("is_active=1")
            if q:
                where.append(
                    "(reservation_id LIKE ? OR guest_name LIKE ? OR IFNULL(phone,'') LIKE ? OR IFNULL(reservation_date,'') LIKE ?)"
                )
                like = f"%{q.strip()}%"
                params.extend([like, like, like, like])

            sql = (
                "SELECT reservation_id, guest_name, phone, reservation_date, reservation_time, guests_count, "
                "table_no, status, notes, source, created_at, updated_at, is_active "
                "FROM reservations"
            )
            if where:
                sql += " WHERE " + " AND ".join(where)
            sql += " ORDER BY reservation_date ASC, reservation_time ASC, updated_at DESC LIMIT ?"
            params.append(min(max(int(limit), 1), 5000))

            rows = con.execute(sql, tuple(params)).fetchall()
            items = []
            for r in rows:
                items.append({
                    "reservation_id": r["reservation_id"],
                    "guest_name": r["guest_name"] or "",
                    "phone": r["phone"] or "",
                    "reservation_date": r["reservation_date"] or "",
                    "reservation_time": r["reservation_time"] or "",
                    "guests_count": int(r["guests_count"] or 1),
                    "table_no": r["table_no"] or "",
                    "status": _normalize_reservation_status(r["status"]),
                    "notes": r["notes"] or "",
                    "source": r["source"] or "online",
                    "created_at": r["created_at"] or "",
                    "updated_at": r["updated_at"] or "",
                    "is_active": int(r["is_active"] or 0),
                })
            return {"items": items, "count": len(items)}
        finally:
            con.close()

    @app.post("/reservations/upsert")
    @api.post("/reservations/upsert")
    def reservations_upsert(body: ReservationUpsert, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)

        guest_name = (body.guest_name or "").strip()
        if not guest_name:
            raise HTTPException(status_code=400, detail="guest_name required")

        rid = (body.reservation_id or "").strip()
        if not rid:
            rid = f"RSV-{datetime.now().strftime('%Y%m%d%H%M%S')}-{str(uuid.uuid4())[:6].upper()}"

        now = _now()
        status = _normalize_reservation_status(body.status)
        date_val = (body.reservation_date or "").strip()
        time_val = (body.reservation_time or "").strip()

        con = _connect(db_path)
        try:
            cur = con.cursor()
            exists = cur.execute("SELECT created_at FROM reservations WHERE reservation_id=?", (rid,)).fetchone()
            created_at = (exists["created_at"] if exists else now) or now
            cur.execute(
                """
                INSERT INTO reservations(
                    reservation_id, guest_name, phone, reservation_date, reservation_time, guests_count,
                    table_no, status, notes, source, created_at, updated_at, is_active
                ) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,1)
                ON CONFLICT(reservation_id) DO UPDATE SET
                    guest_name=excluded.guest_name,
                    phone=excluded.phone,
                    reservation_date=excluded.reservation_date,
                    reservation_time=excluded.reservation_time,
                    guests_count=excluded.guests_count,
                    table_no=excluded.table_no,
                    status=excluded.status,
                    notes=excluded.notes,
                    source=excluded.source,
                    updated_at=excluded.updated_at,
                    is_active=1
                """,
                (
                    rid,
                    guest_name,
                    (body.phone or "").strip(),
                    date_val,
                    time_val,
                    max(1, int(body.guests_count or 1)),
                    (body.table_no or "").strip(),
                    status,
                    (body.notes or "").strip(),
                    (body.source or "online").strip() or "online",
                    created_at,
                    (body.updated_at or now),
                ),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "reservation.upsert", {"reservation_id": rid, "status": status})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "reservation.upsert", "seq": seq, "reservation_id": rid})
        except Exception:
            pass
        return {"ok": True, "reservation_id": rid, "status": status, "updated_at": now, "seq": seq}

    @app.post("/reservations/delete")
    @api.post("/reservations/delete")
    def reservations_delete(body: ReservationDelete, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        rid = (body.reservation_id or "").strip()
        if not rid:
            raise HTTPException(status_code=400, detail="reservation_id required")

        con = _connect(db_path)
        try:
            cur = con.cursor()
            cur.execute("UPDATE reservations SET is_active=0, updated_at=? WHERE reservation_id=?", (_now(), rid))
            if cur.rowcount == 0:
                raise HTTPException(status_code=404, detail="Reservation not found")
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "reservation.delete", {"reservation_id": rid})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "reservation.delete", "seq": seq, "reservation_id": rid})
        except Exception:
            pass
        return {"ok": True, "reservation_id": rid, "seq": seq}

    # ==========================================================
    # Optional: Customer bridge endpoint
    # ==========================================================
    @app.post("/customers/upsert")
    def customers_upsert(body: CustomerUpsert, x_api_key: Optional[str] = Header(default=None)) -> dict:
        _auth(x_api_key)
        phone = "".join([c for c in str(body.phone or "") if c.isdigit()])
        if phone.startswith("0"):
            phone = phone[1:]
        if not phone:
            raise HTTPException(status_code=400, detail="phone required")

        con = _connect(db_path)
        try:
            con.execute(
                """
                INSERT INTO customers(phone, name, email, updated_at)
                VALUES(?,?,?,?)
                ON CONFLICT(phone) DO UPDATE SET
                    name=excluded.name,
                    email=excluded.email,
                    updated_at=excluded.updated_at
                """,
                (phone, (body.name or "").strip(), (body.email or "").strip(), _now()),
            )
            con.commit()
        finally:
            con.close()

        seq = _emit_event(db_path, "customer.upsert", {"phone": phone})
        try:
            import anyio
            anyio.from_thread.run(_broadcast, {"type": "customer.upsert", "seq": seq, "phone": phone})
        except Exception:
            pass
        return {"ok": True, "seq": seq, "phone": phone}

    return app


# Default ASGI app (works with `uvicorn pos_hub_server:app`)
DB = str(_default_db_path().resolve())
KEY = _default_api_key()
if not KEY:
    raise RuntimeError(
        "POS Hub API key is missing. Set POS_HUB_API_KEY/POS_HUB_KEY "
        "or ensure poshub_runtime.json contains api_key."
    )
_PUBLIC_SCHEME = str(os.environ.get("POS_HUB_PUBLIC_SCHEME", "https")).strip().lower() or "https"
try:
    _PUBLIC_PORT = int(
        os.environ.get("PORT")
        or os.environ.get("POS_HUB_PUBLIC_PORT")
        or 8766
    )
except Exception:
    _PUBLIC_PORT = 8766
app = create_app(db_path=DB, api_key=KEY, public_scheme=_PUBLIC_SCHEME, public_port=_PUBLIC_PORT)


# -------------------------------------------------------------------
# Optional local run:
#   python this_file.py
# Reads poshub_runtime.json to detect HTTPS config and uses SSL if available.
# -------------------------------------------------------------------
if __name__ == "__main__":
    import uvicorn

    def _load_runtime_ssl():
        """Try to read cert/key paths from poshub_runtime.json."""
        try:
            cfg_path = _app_root() / "poshub_runtime.json"
            if cfg_path.exists():
                import json as _json
                cfg = _json.loads(cfg_path.read_text(encoding="utf-8"))
                if bool(cfg.get("https_enabled")):
                    cert = str(cfg.get("cert") or "").strip()
                    key_file = str(cfg.get("key") or "").strip()
                    if cert and key_file and Path(cert).exists() and Path(key_file).exists():
                        return cert, key_file
        except Exception:
            pass
        return None, None

    _cert, _key = _load_runtime_ssl()
    if _cert and _key:
        uvicorn.run(app, host="0.0.0.0", port=_PUBLIC_PORT, ssl_certfile=_cert, ssl_keyfile=_key, log_level="info")
    else:
        uvicorn.run(app, host="0.0.0.0", port=_PUBLIC_PORT, log_level="info")
