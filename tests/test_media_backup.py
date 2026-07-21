from __future__ import annotations

import io
import sqlite3
import tarfile
from datetime import datetime, timezone
from pathlib import Path

import pytest

import backup_crypto
import media_backup


SECRET = "central-media-unit-test-secret-0123456789abcdef"


class _Paginator:
    def __init__(self, client: "_S3") -> None:
        self.client = client

    def paginate(self, *, Bucket: str, Prefix: str):
        return [{"Contents": [
            {"Key": key, "LastModified": row["modified"]}
            for key, row in self.client.objects.items()
            if key.startswith(Prefix)
        ]}]


class _S3:
    def __init__(self) -> None:
        self.objects = {}
        self.extra_args = {}

    def upload_file(self, filename: str, bucket: str, key: str, ExtraArgs: dict) -> None:
        self.extra_args = ExtraArgs
        self.objects[key] = {
            "payload": Path(filename).read_bytes(),
            "modified": datetime.now(timezone.utc),
        }

    def download_file(self, bucket: str, key: str, filename: str) -> None:
        Path(filename).write_bytes(self.objects[key]["payload"])

    def get_paginator(self, name: str) -> _Paginator:
        assert name == "list_objects_v2"
        return _Paginator(self)

    def delete_object(self, *, Bucket: str, Key: str) -> None:
        self.objects.pop(Key, None)


def _db(path: Path, value: str) -> None:
    con = sqlite3.connect(path)
    try:
        con.execute("CREATE TABLE proof(value TEXT NOT NULL)")
        con.execute("INSERT INTO proof(value) VALUES (?)", (value,))
        con.commit()
    finally:
        con.close()


def _env(monkeypatch) -> None:
    monkeypatch.setenv("BACKUP_ENCRYPTION_KEY", SECRET)
    monkeypatch.setenv("BACKUP_S3_BUCKET", "test")
    monkeypatch.setenv("BACKUP_S3_ACCESS_KEY", "access")
    monkeypatch.setenv("BACKUP_S3_SECRET_KEY", "secret")
    monkeypatch.setenv("BACKUP_S3_ENDPOINT", "https://s3.eu-central-003.backblazeb2.com")
    monkeypatch.setenv("BACKUP_S3_REGION", "eu-central-003")
    monkeypatch.setenv("BACKUP_REQUIRE_EU_REGION", "1")


def test_encrypted_database_and_media_roundtrip(tmp_path: Path, monkeypatch) -> None:
    source = tmp_path / "source"
    source.mkdir()
    source_db = source / "poshub.db"
    _db(source_db, "before-frankfurt")
    image = source / "static" / "global_gallery" / "pizza" / "one.jpg"
    image.parent.mkdir(parents=True)
    image.write_bytes(b"fake-image-data")
    fake = _S3()
    _env(monkeypatch)
    monkeypatch.setattr(media_backup, "_s3_client", lambda env: fake)

    assert media_backup.run_once(
        data_dir=source,
        db_path=source_db,
        now=datetime(2026, 7, 21, 19, 0, tzinfo=timezone.utc),
    )
    payload = next(iter(fake.objects.values()))["payload"]
    assert payload.startswith(backup_crypto.MAGIC)
    assert b"fake-image-data" not in payload
    assert fake.extra_args["ServerSideEncryption"] == "AES256"

    target = tmp_path / "target"
    (target / "static" / "global_gallery").mkdir(parents=True)
    monkeypatch.setenv("BACKUP_RESTORE_LATEST", "1")
    assert media_backup.restore_latest_if_requested(data_dir=target, db_path=target / "poshub.db")
    assert (target / "static" / "global_gallery" / "pizza" / "one.jpg").read_bytes() == b"fake-image-data"
    con = sqlite3.connect(target / "poshub.db")
    try:
        assert con.execute("SELECT value FROM proof").fetchone()[0] == "before-frankfurt"
    finally:
        con.close()


def test_restore_rejects_path_traversal(tmp_path: Path) -> None:
    archive = tmp_path / "unsafe.tar.gz"
    with tarfile.open(archive, "w:gz") as handle:
        member = tarfile.TarInfo("../outside.txt")
        member.size = 3
        handle.addfile(member, io.BytesIO(b"bad"))
    with pytest.raises(RuntimeError, match="unsafe path"):
        media_backup._safe_extract(archive, tmp_path / "out")
    assert not (tmp_path / "outside.txt").exists()
