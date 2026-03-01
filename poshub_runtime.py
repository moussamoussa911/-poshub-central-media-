# poshub_runtime.py
from __future__ import annotations
import json
import os
import secrets
import sys
from pathlib import Path


def app_root() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


class PosHubRuntimeSelector:
    """
    Reads/writes `poshub_runtime.json` and resolves which endpoint clients should use.
    Supported modes: local, lan, online.
    """

    def __init__(self, path: Path | None = None):
        self.path = path or (app_root() / "poshub_runtime.json")

    def load(self) -> dict:
        if not self.path.exists():
            return {}
        try:
            return json.loads(self.path.read_text(encoding="utf-8"))
        except Exception:
            return {}

    def save(self, cfg: dict) -> None:
        try:
            self.path.write_text(json.dumps(cfg, indent=2), encoding="utf-8")
        except Exception:
            pass

    @staticmethod
    def _normalize_url(url: str) -> str:
        return (url or "").strip().rstrip("/")

    @staticmethod
    def _force_scheme(url: str, scheme: str) -> str:
        u = (url or "").strip()
        if not u:
            return u
        if "://" not in u:
            return f"{scheme}://{u.lstrip('/')}"
        try:
            proto, rest = u.split("://", 1)
            return f"{scheme}://{rest}"
        except Exception:
            return u

    def set_mode(self, mode: str, online_url: str = "") -> dict:
        mode = (mode or "local").strip().lower()
        if mode not in {"local", "lan", "online"}:
            mode = "local"

        cfg = self.load()
        cfg["server_mode"] = mode
        if online_url.strip():
            cfg["online_url"] = self._normalize_url(online_url)
        self.save(cfg)
        return cfg

    def resolve_base_url(self, cfg: dict, default_url: str) -> str:
        mode = (cfg.get("server_mode") or "").strip().lower()

        if mode == "online":
            return self._normalize_url(
                cfg.get("online_url")
                or cfg.get("base_url_online")
                or cfg.get("remote_url")
                or default_url
            )

        if mode == "lan":
            return self._normalize_url(
                cfg.get("https_url_lan")
                or cfg.get("http_url_lan")
                or cfg.get("base_url_lan")
                or default_url
            )

        # local/default (backward compatible)
        https_enabled_raw = cfg.get("https_enabled")
        if https_enabled_raw is None:
            guess = str(
                cfg.get("https_url_local")
                or cfg.get("base_url_local")
                or cfg.get("base_url")
                or ""
            ).strip().lower()
            https_enabled = guess.startswith("https://")
        else:
            https_enabled = bool(https_enabled_raw)
        if https_enabled:
            candidate = cfg.get("https_url_local") or cfg.get("base_url_local") or cfg.get("base_url")
            candidate = self._force_scheme(str(candidate or ""), "https")
        else:
            candidate = cfg.get("http_url_local") or cfg.get("base_url_local") or cfg.get("base_url")
            candidate = self._force_scheme(str(candidate or ""), "http")
        return self._normalize_url(candidate or default_url)


def _env_api_key() -> str:
    return (
        os.environ.get("POS_HUB_API_KEY", "").strip()
        or os.environ.get("POS_HUB_KEY", "").strip()
    )


def _generate_api_key() -> str:
    # Per-install unique key for local secure API access.
    return f"phk_{secrets.token_urlsafe(24)}"


def _resolve_or_create_api_key(selector: PosHubRuntimeSelector, cfg: dict, default_key: str = "") -> str:
    key = (
        str((cfg or {}).get("api_key") or "").strip()
        or _env_api_key()
        or str(default_key or "").strip()
    )
    if key:
        return key

    key = _generate_api_key()
    cfg = dict(cfg or {})
    cfg["api_key"] = key
    selector.save(cfg)
    return key


def load_poshub_runtime(default_url: str = "https://127.0.0.1:8766", default_key: str = "") -> dict:
    selector = PosHubRuntimeSelector()
    cfg = selector.load()
    if not cfg:
        api_key = _resolve_or_create_api_key(selector, {}, default_key)
        return {
            "base_url": default_url,
            "api_key": api_key,
            "verify_ssl": True,
            "server_mode": "local",
            "online_url": "",
            "base_url_online": "",
            "sync_online_enabled": False,
            "verify_ssl_online": True,
        }

    try:
        base_url = selector.resolve_base_url(cfg, default_url)
        api_key = _resolve_or_create_api_key(selector, cfg, default_key)
        sync_enabled = bool(cfg.get("sync_online_enabled", cfg.get("hybrid_online_enabled", False)))

        mode = (cfg.get("server_mode") or "local").strip().lower()
        if mode == "online":
            verify_ssl = bool(cfg.get("verify_ssl_online", cfg.get("verify_ssl", True)))
        else:
            https_enabled = bool(cfg.get("https_enabled"))
            verify_ssl = bool(cfg.get("verify_ssl", not https_enabled))

        return {
            "base_url": base_url or default_url,
            "api_key": api_key,
            "verify_ssl": verify_ssl,
            "server_mode": mode or "local",
            "online_url": selector._normalize_url(cfg.get("online_url") or ""),
            "base_url_online": selector._normalize_url(cfg.get("base_url_online") or cfg.get("online_url") or ""),
            "sync_online_enabled": sync_enabled,
            "hybrid_online_enabled": sync_enabled,
            "verify_ssl_online": bool(cfg.get("verify_ssl_online", cfg.get("verify_ssl", True))),
        }
    except Exception:
        api_key = _resolve_or_create_api_key(selector, {}, default_key)
        return {
            "base_url": default_url,
            "api_key": api_key,
            "verify_ssl": True,
            "server_mode": "local",
            "online_url": "",
            "base_url_online": "",
            "sync_online_enabled": False,
            "verify_ssl_online": True,
        }
