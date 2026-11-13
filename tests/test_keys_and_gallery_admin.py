"""Key handling and gallery admin (privacy fixes A1 + A3).

- The master key comes only from the environment on Render; the repository
  carries none and the server never invents one there.
- The gallery admin has no built-in password: without
  POS_HUB_GALLERY_ADMIN_PASSWORD the service does not start.
- Till keys (POS_HUB_CLIENT_KEYS) may read and upload, never manage the gallery
  and are not accepted anywhere else.
- An owner created by an older version is replaced once and all sessions end.
"""

from __future__ import annotations

import importlib
import io
import sqlite3
import sys
from pathlib import Path

import pytest
from fastapi.testclient import TestClient

MASTER = "master-key-for-tests-0123456789abcdef"
TILL = "till-key-for-tests-0123456789abcdef"
OWNER_PWD = "owner-password-for-tests"
ROOT = Path(__file__).resolve().parents[1]


def _clean_env(monkeypatch, data_dir: Path):
    for name in ("POS_HUB_API_KEY", "POS_HUB_KEY", "POS_HUB_JWT_SECRET", "JWT_SECRET", "RENDER",
                 "POS_HUB_REQUIRE_ENV_KEY", "POS_HUB_CLIENT_KEYS", "POS_HUB_GALLERY_ADMIN_PASSWORD",
                 "POS_HUB_GALLERY_ADMIN_USER", "POS_HUB_GALLERY_ADMIN_FORCE_RESET",
                 "POS_HUB_GALLERY_SESSION_SECRET", "PEXELS_API_KEY", "PIXABAY_API_KEY", "BACKUP_ENABLED",
                 "POS_HUB_IMAGE_TENANT_SCOPE", "POS_HUB_TRUSTED_PROXY_HOPS"):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("POS_HUB_DATA_DIR", str(data_dir))
    monkeypatch.setenv("POS_HUB_PUBLIC_SCHEME", "http")
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))


def _import_server():
    sys.modules.pop("pos_hub_server", None)
    return importlib.import_module("pos_hub_server")


@pytest.fixture()
def env(tmp_path, monkeypatch):
    data_dir = tmp_path / "data"
    data_dir.mkdir()
    _clean_env(monkeypatch, data_dir)
    yield monkeypatch, data_dir
    sys.modules.pop("pos_hub_server", None)


@pytest.fixture()
def server(env):
    monkeypatch, data_dir = env
    monkeypatch.setenv("POS_HUB_API_KEY", MASTER)
    monkeypatch.setenv("POS_HUB_CLIENT_KEYS", f" {TILL} , other-till-key-0123456789 ")
    monkeypatch.setenv("POS_HUB_GALLERY_ADMIN_PASSWORD", OWNER_PWD)
    module = _import_server()
    return module, TestClient(module.app), data_dir


# ── A1: key source ──────────────────────────────────────────────────────────

def test_runtime_file_is_not_in_the_repository():
    tracked = (ROOT / ".gitignore").read_text(encoding="utf-8-sig").splitlines()
    assert "poshub_runtime.json" in [line.strip() for line in tracked]
    assert not (ROOT / "poshub_runtime.json").exists()


def test_on_render_the_key_must_come_from_the_environment(env):
    monkeypatch, _ = env
    monkeypatch.setenv("RENDER", "true")
    monkeypatch.setenv("POS_HUB_GALLERY_ADMIN_PASSWORD", OWNER_PWD)
    with pytest.raises(RuntimeError, match="API key is missing"):
        _import_server()
    # and nothing was invented and saved next to the code
    assert not (ROOT / "poshub_runtime.json").exists()


def test_forced_env_key_mode_behaves_like_render(env):
    monkeypatch, _ = env
    monkeypatch.setenv("POS_HUB_REQUIRE_ENV_KEY", "1")
    monkeypatch.setenv("POS_HUB_GALLERY_ADMIN_PASSWORD", OWNER_PWD)
    with pytest.raises(RuntimeError, match="API key is missing"):
        _import_server()


def test_signing_secret_has_no_built_in_fallback(server, monkeypatch):
    module, _client, _ = server
    assert module._jwt_secret() == MASTER
    monkeypatch.setenv("POS_HUB_JWT_SECRET", "explicit-signing-secret")
    assert module._jwt_secret() == "explicit-signing-secret"
    monkeypatch.delenv("POS_HUB_JWT_SECRET")
    monkeypatch.delenv("POS_HUB_API_KEY")
    monkeypatch.setattr(module, "KEY", "")
    with pytest.raises(RuntimeError, match="No signing secret"):
        module._jwt_secret()


# ── A3: gallery admin password ──────────────────────────────────────────────

def test_service_does_not_start_without_gallery_password(env):
    monkeypatch, _ = env
    monkeypatch.setenv("POS_HUB_API_KEY", MASTER)
    with pytest.raises(RuntimeError, match="POS_HUB_GALLERY_ADMIN_PASSWORD"):
        _import_server()


def test_service_does_not_start_with_a_short_gallery_password(env):
    monkeypatch, _ = env
    monkeypatch.setenv("POS_HUB_API_KEY", MASTER)
    monkeypatch.setenv("POS_HUB_GALLERY_ADMIN_PASSWORD", "short")
    with pytest.raises(RuntimeError, match="at least 12"):
        _import_server()


def _login(client, **body):
    return client.post("/gallery-admin/login", json=body)


def test_owner_logs_in_with_the_configured_password_only(server):
    _module, client, _ = server
    assert _login(client, username="admin", password=OWNER_PWD).status_code == 200
    assert _login(client, username="admin", password=MASTER).status_code == 401


def test_recovery_login_only_with_the_master_key(server):
    _module, client, _ = server
    assert _login(client, api_key=MASTER).status_code == 200
    assert _login(client, api_key=TILL).status_code == 401


def test_owner_from_an_older_version_is_replaced_once_and_sessions_end(env):
    monkeypatch, data_dir = env
    monkeypatch.setenv("POS_HUB_API_KEY", MASTER)
    monkeypatch.setenv("POS_HUB_GALLERY_ADMIN_PASSWORD", OWNER_PWD)
    module = _import_server()
    client = TestClient(module.app)
    db = Path(module.DB)

    # Simulate the state an older version left behind: owner with another
    # password, a second account whose password is the API key, no marker.
    old_hash = module.hashlib.pbkdf2_hmac("sha256", b"old-weak-owner-password", b"0123456789abcdef", 200_000).hex()
    key_hash = module.hashlib.pbkdf2_hmac("sha256", MASTER.encode(), b"fedcba9876543210", 200_000).hex()
    con = sqlite3.connect(db)
    con.execute("UPDATE gallery_admin_users SET pwd_hash=?, pwd_salt=? WHERE username='admin'",
                (old_hash, b"0123456789abcdef".hex()))
    con.execute(
        "INSERT INTO gallery_admin_users(username,display_name,role,pwd_hash,pwd_salt,active,created_at,updated_at) "
        "VALUES('ops','Ops','admin',?,?,1,'t','t')",
        (key_hash, b"fedcba9876543210".hex()),
    )
    con.execute("DELETE FROM gallery_admin_meta WHERE key='owner_password_v2'")
    con.commit()
    con.close()
    old_session = _login(client, username="admin", password="old-weak-owner-password")
    assert old_session.status_code == 200
    old_token = old_session.json()["session_token"]

    module = _import_server()  # restart
    client = TestClient(module.app)
    assert _login(client, username="admin", password="old-weak-owner-password").status_code == 401
    assert _login(client, username="admin", password=OWNER_PWD).status_code == 200
    assert _login(client, username="ops", password=MASTER).status_code == 401
    resp = client.get("/api/gallery/users", headers={"X-Gallery-Session": old_token})
    assert resp.status_code == 401

    # A second restart changes nothing any more.
    con = sqlite3.connect(db)
    marker = con.execute("SELECT value FROM gallery_admin_meta WHERE key='owner_password_v2'").fetchone()
    con.close()
    assert marker and marker[0]


# ── till keys ───────────────────────────────────────────────────────────────

def _png(tag: bytes = b"x") -> bytes:
    return b"\x89PNG\r\n\x1a\n" + tag * 64


def test_till_key_reads_uploads_and_searches(server):
    _module, client, _ = server
    h = {"X-Api-Key": TILL}
    up = client.post("/api/menu/upload_image", headers=h, data={"category": "pizza"},
                     files={"file": ("dish.png", io.BytesIO(_png()), "image/png")})
    assert up.status_code == 200, up.text
    assert client.get("/api/gallery/list", headers=h).status_code == 200
    assert client.get("/api/gallery/categories", headers=h).status_code == 200
    assert client.get("/api/images/search", headers=h, params={"q": "pizza"}).status_code == 200


@pytest.mark.parametrize(
    "method,path,kwargs",
    [
        ("post", "/api/gallery/categories", {"data": {"name": "neu"}}),
        ("delete", "/api/gallery/categories", {"params": {"name": "pizza"}}),
        ("post", "/api/gallery/rename", {"data": {"rel_path": "pizza/a.png", "new_name": "b"}}),
        ("delete", "/api/gallery/item", {"params": {"rel_path": "pizza/a.png"}}),
        ("post", "/api/gallery/delete_many", {"json": {"rel_paths": ["pizza/a.png"]}}),
        ("get", "/api/gallery/users", {}),
        ("post", "/api/gallery/users", {"json": {"username": "x", "password": "x" * 16}}),
        ("put", "/api/gallery/brand", {"json": {"company_name": "x"}}),
    ],
)
def test_till_key_cannot_manage_the_gallery(server, method, path, kwargs):
    _module, client, _ = server
    resp = getattr(client, method)(path, headers={"X-Api-Key": TILL}, **kwargs)
    assert resp.status_code == 403, (path, resp.status_code, resp.text)


def test_till_key_is_not_accepted_outside_the_gallery(server):
    _module, client, _ = server
    assert client.get("/api/menu", headers={"X-Api-Key": TILL}).status_code == 401
    assert client.get("/api/menu", headers={"X-Api-Key": MASTER}).status_code == 200


def test_master_key_still_manages_the_gallery(server):
    _module, client, _ = server
    resp = client.post("/api/gallery/categories", headers={"X-Api-Key": MASTER}, data={"name": "neu"})
    assert resp.status_code == 200, resp.text
    assert client.get("/api/gallery/users", headers={"X-Api-Key": MASTER}).status_code == 200
