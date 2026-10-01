"""Photo search proxy and private customer photos (POS Paket 2).

The POS asks this server for Pexels/Pixabay photos (/api/images/search) and
stores a restaurant's own photos with its X-Image-Owner token. Without that
header (gallery admin, Media Center, older tills) the gallery behaves as
before.
"""

from __future__ import annotations

import importlib
import io
import sys
from pathlib import Path

import pytest
from fastapi.testclient import TestClient

KEY = "test-central-media-key-0123456789"
OWNER_A = "A" * 40
OWNER_B = "b" * 40
PIXABAY_SECRET = "pixabay-secret-value-for-tests"


@pytest.fixture()
def server(tmp_path, monkeypatch):
    data_dir = tmp_path / "data"
    data_dir.mkdir()
    monkeypatch.setenv("POS_HUB_DATA_DIR", str(data_dir))
    monkeypatch.setenv("POS_HUB_API_KEY", KEY)
    monkeypatch.setenv("POS_HUB_PUBLIC_SCHEME", "http")
    for name in ("PEXELS_API_KEY", "PIXABAY_API_KEY", "RENDER", "POS_HUB_TRUSTED_PROXY_HOPS",
                 "POS_HUB_IMAGE_TENANT_SCOPE", "BACKUP_ENABLED"):
        monkeypatch.delenv(name, raising=False)
    root = str(Path(__file__).resolve().parents[1])
    if root not in sys.path:
        sys.path.insert(0, root)
    sys.modules.pop("pos_hub_server", None)
    module = importlib.import_module("pos_hub_server")
    for store in (module._STOCK_CACHE, module._STOCK_RATE, module._STOCK_OUTBOUND, module._STOCK_CALLER_UNCACHED):
        store.clear()
    client = TestClient(module.app)
    yield module, client, data_dir
    sys.modules.pop("pos_hub_server", None)


def _headers(owner: str | None = None) -> dict:
    out = {"X-Api-Key": KEY}
    if owner is not None:
        out["X-Image-Owner"] = owner
    return out


def _png(tag: bytes = b"x") -> bytes:
    # Not decoded by the server; a PNG signature plus a distinct payload.
    return b"\x89PNG\r\n\x1a\n" + tag * 64


def _upload(client, owner=None, category="pizza", tag=b"x"):
    return client.post(
        "/api/menu/upload_image",
        headers=_headers(owner),
        data={"category": category},
        files={"file": ("dish.png", io.BytesIO(_png(tag)), "image/png")},
    )


def _list(client, owner=None, category="all"):
    resp = client.get("/api/gallery/list", headers=_headers(owner), params={"category": category, "page_size": 500})
    assert resp.status_code == 200, resp.text
    return resp.json()


# ── photo search ────────────────────────────────────────────────────────────

def test_search_without_provider_keys_says_not_configured(server):
    _module, client, _data = server
    resp = client.get("/api/images/search", headers=_headers(), params={"q": "pizza"})
    assert resp.status_code == 200
    body = resp.json()
    assert body["configured"] is False and body["items"] == []
    assert body["provider_links"]["pixabay"] == "https://pixabay.com"


def test_search_needs_the_api_key(server):
    _module, client, _data = server
    resp = client.get("/api/images/search", params={"q": "pizza"})
    assert resp.status_code == 401


def test_search_rejects_too_short_queries(server):
    _module, client, _data = server
    resp = client.get("/api/images/search", headers=_headers(), params={"q": "p"})
    assert resp.status_code == 422


class _FakeResponse:
    def __init__(self, payload, status=200):
        self._payload = payload
        self.status_code = status

    def json(self):
        return self._payload

    def close(self):
        pass


def _pixabay_payload():
    return {
        "hits": [
            {
                "id": 123,
                "webformatURL": "https://cdn.pixabay.com/photo/pizza_640.jpg",
                "largeImageURL": "https://cdn.pixabay.com/photo/pizza_1280.jpg",
                "imageWidth": 1280,
                "imageHeight": 853,
                "pageURL": "https://pixabay.com/photos/pizza-123/",
                "user": "chef_anna",
                "user_id": 42,
            },
            {"id": 124, "webformatURL": "http://insecure.example/x.jpg", "largeImageURL": "http://insecure.example/y.jpg"},
        ]
    }


def test_search_maps_pixabay_and_never_leaks_the_key(server, monkeypatch):
    module, client, _data = server
    monkeypatch.setenv("PIXABAY_API_KEY", PIXABAY_SECRET)
    calls = []

    def fake_get(url, *, params, headers, timeout):
        calls.append((url, dict(params)))
        return _FakeResponse(_pixabay_payload())

    monkeypatch.setattr(module, "_stock_http_get", fake_get)
    resp = client.get("/api/images/search", headers=_headers(), params={"q": "Pizza Margherita"})
    assert resp.status_code == 200, resp.text
    body = resp.json()
    assert body["ok"] is True and body["providers"] == ["pixabay"]
    assert [it["id"] for it in body["items"]] == ["pixabay:123"]  # http-only hit dropped
    item = body["items"][0]
    assert item["image_url"].startswith("https://cdn.pixabay.com/")
    assert item["photographer_url"] == "https://pixabay.com/users/chef_anna-42/"
    assert item["license"] and item["attribution"]
    assert PIXABAY_SECRET not in resp.text
    assert calls and calls[0][0] == "https://pixabay.com/api/" and calls[0][1]["safesearch"] == "true"

    # The same search again comes from the 24 h cache: no second outbound call.
    again = client.get("/api/images/search", headers=_headers(), params={"q": "pizza margherita"})
    assert again.status_code == 200 and len(calls) == 1


def test_search_provider_failure_is_a_short_message_without_details(server, monkeypatch):
    module, client, _data = server
    monkeypatch.setenv("PIXABAY_API_KEY", PIXABAY_SECRET)

    def boom(url, *, params, headers, timeout):
        raise ConnectionError(f"failed for {url}?key={params.get('key')}")

    monkeypatch.setattr(module, "_stock_http_get", boom)
    resp = client.get("/api/images/search", headers=_headers(), params={"q": "salat"})
    assert resp.status_code == 200
    body = resp.json()
    assert body["ok"] is False and body["errors"] == {"pixabay": "keine Verbindung"}
    assert PIXABAY_SECRET not in resp.text


def test_search_is_rate_limited_per_caller(server, monkeypatch):
    module, client, _data = server
    monkeypatch.setattr(module, "_STOCK_RATE_LIMIT", 3)
    for _ in range(3):
        assert client.get("/api/images/search", headers=_headers(), params={"q": "pasta"}).status_code == 200
    blocked = client.get("/api/images/search", headers=_headers(), params={"q": "pasta"})
    assert blocked.status_code == 429 and blocked.headers.get("Retry-After")


def test_trusted_proxy_hops_uses_the_proxy_written_address(server, monkeypatch):
    module, client, _data = server
    monkeypatch.setattr(module, "_STOCK_RATE_LIMIT", 1)
    monkeypatch.setenv("POS_HUB_TRUSTED_PROXY_HOPS", "1")
    first = client.get("/api/images/search", headers={**_headers(), "X-Forwarded-For": "1.1.1.1, 9.9.9.9"},
                       params={"q": "suppe"})
    assert first.status_code == 200
    # A forged left entry does not open a new bucket: the right one decides.
    forged = client.get("/api/images/search", headers={**_headers(), "X-Forwarded-For": "2.2.2.2, 9.9.9.9"},
                        params={"q": "suppe"})
    assert forged.status_code == 429


# ── private customer photos ─────────────────────────────────────────────────

def test_upload_without_owner_header_still_goes_to_the_shared_gallery(server):
    _module, client, data = server
    resp = _upload(client, owner=None, category="pizza")
    assert resp.status_code == 200, resp.text
    body = resp.json()
    assert body["image_url_rel"].startswith("/static/global_gallery/pizza/")
    assert "scope" not in body
    assert list((data / "static" / "global_gallery" / "pizza").glob("*.png"))


def test_upload_with_owner_header_goes_into_the_restaurants_own_folder(server):
    module, client, data = server
    resp = _upload(client, owner=OWNER_A, category="pizza", tag=b"a")
    assert resp.status_code == 200, resp.text
    body = resp.json()
    scope = module._image_pipeline.owner_scope_folder(OWNER_A)
    assert body["scope"] == scope
    assert body["image_url_rel"].startswith(f"/static/menu_images/{scope}/")
    assert not list((data / "static" / "global_gallery").rglob("*.png"))
    stored = list((data / "static" / "menu_images" / scope).glob("*.png"))
    assert len(stored) == 1 and not any(p.name.startswith(".") for p in stored)
    # The stored file is served under the returned URL.
    served = client.get(body["image_url_rel"])
    assert served.status_code == 200 and served.content == _png(b"a")


def test_malformed_owner_header_is_rejected(server):
    _module, client, _data = server
    assert _upload(client, owner="too-short").status_code == 400
    resp = client.get("/api/gallery/list", headers=_headers("bad header!"))
    assert resp.status_code == 400


def test_each_restaurant_sees_shared_photos_and_only_its_own(server):
    _module, client, _data = server
    assert _upload(client, owner=None, category="pizza", tag=b"g").status_code == 200
    assert _upload(client, owner=OWNER_A, tag=b"a").status_code == 200
    assert _upload(client, owner=OWNER_B, tag=b"b").status_code == 200

    seen_a = _list(client, owner=OWNER_A)["items"]
    owners_a = sorted(it["owner"] for it in seen_a)
    assert owners_a == ["global", "own"]
    own_a = [it for it in seen_a if it["owner"] == "own"][0]
    assert own_a["category"] == "Meine Bilder"
    assert own_a["url"].endswith(own_a["rel_path"].split("/", 1)[1]) or "/static/menu_images/" in own_a["url"]

    seen_b = _list(client, owner=OWNER_B)["items"]
    own_b = [it for it in seen_b if it["owner"] == "own"]
    assert len(own_b) == 1 and own_b[0]["rel_path"] != own_a["rel_path"]

    # Without the header (gallery admin, older tills): shared gallery only,
    # response unchanged (no "owner" field).
    plain = _list(client, owner=None)["items"]
    assert len(plain) == 1 and "owner" not in plain[0]
    assert plain[0]["rel_path"].startswith("pizza/")


def test_own_category_filter_lists_only_own_photos(server):
    _module, client, _data = server
    _upload(client, owner=None, category="pizza", tag=b"g")
    _upload(client, owner=OWNER_A, tag=b"a")
    mine = _list(client, owner=OWNER_A, category="Meine Bilder")["items"]
    assert [it["owner"] for it in mine] == ["own"]
    shared = _list(client, owner=OWNER_A, category="pizza")["items"]
    assert [it["owner"] for it in shared] == ["global"]
