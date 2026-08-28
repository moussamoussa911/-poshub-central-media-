from __future__ import annotations

import io
import sqlite3
import tarfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

import backup_crypto
import media_backup


SECRET = "central-media-unit-test-secret-0123456789abcdef"


class _Paginator:
    def __init__(self, client: "_S3", name: str) -> None:
        self.client = client
        self.name = name

    def paginate(self, *, Bucket: str, Prefix: str):
        if self.name in self.client.list_errors:
            raise RuntimeError(f"{self.name} unavailable")
        if self.name == "list_objects_v2":
            return [{"Contents": [
                {
                    "Key": key,
                    "LastModified": row["modified"],
                    "Size": len(row["payload"]),
                }
                for key, row in self.client.objects.items()
                if key.startswith(Prefix)
            ]}]
        assert self.name == "list_object_versions"
        return [{
            "Versions": [row for row in self.client.versions if row["Key"].startswith(Prefix)],
            "DeleteMarkers": [row for row in self.client.delete_markers if row["Key"].startswith(Prefix)],
        }]


class _S3:
    def __init__(self) -> None:
        self.objects = {}
        self.extra_args = {}
        self.versions = []
        self.delete_markers = []
        self.deleted = []
        self.uploads = 0
        self.delete_errors = []
        self.list_errors = set()

    def upload_file(self, filename: str, bucket: str, key: str, ExtraArgs: dict) -> None:
        self.extra_args = ExtraArgs
        self.uploads += 1
        payload = Path(filename).read_bytes()
        modified = datetime.now(timezone.utc)
        version_id = f"v{len(self.versions) + 1}"
        self.objects[key] = {
            "payload": payload,
            "modified": modified,
            "version_id": version_id,
        }
        self.versions.append({
            "Key": key,
            "VersionId": version_id,
            "LastModified": modified,
            "Size": len(payload),
        })

    def download_file(self, bucket: str, key: str, filename: str) -> None:
        Path(filename).write_bytes(self.objects[key]["payload"])

    def get_paginator(self, name: str) -> _Paginator:
        return _Paginator(self, name)

    def delete_objects(self, *, Bucket: str, Delete: dict) -> dict:
        if self.delete_errors:
            return {"Errors": list(self.delete_errors)}
        for target in Delete["Objects"]:
            assert target.get("VersionId")
            pair = (target["Key"], target["VersionId"])
            self.deleted.append(pair)
            self.versions = [
                row for row in self.versions
                if (row["Key"], row["VersionId"]) != pair
            ]
            self.delete_markers = [
                row for row in self.delete_markers
                if (row["Key"], row["VersionId"]) != pair
            ]
            current = self.objects.get(target["Key"])
            if current and current.get("version_id") == target["VersionId"]:
                self.objects.pop(target["Key"], None)
        return {"Errors": []}


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
    original_replace = media_backup.os.replace

    def same_filesystem_replace(source_path, target_path):
        assert Path(source_path).parent == Path(target_path).parent
        return original_replace(source_path, target_path)

    monkeypatch.setattr(media_backup.os, "replace", same_filesystem_replace)
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


def test_prune_permanently_deletes_only_expired_central_media_versions(monkeypatch) -> None:
    _env(monkeypatch)
    monkeypatch.setenv("BACKUP_RETENTION_DAYS", "7")
    monkeypatch.setenv("BACKUP_MIN_RECOVERY_POINTS", "1")
    now = datetime(2026, 8, 28, 12, 0, tzinfo=timezone.utc)
    old_key = "central-media/2026/08/01/central-media_old.tar.gz.enc"
    fresh_key = "central-media/2026/08/27/central-media_fresh.tar.gz.enc"
    fake = _S3()
    fake.versions = [
        {"Key": old_key, "VersionId": "old-v1", "LastModified": now - timedelta(days=20), "Size": 313},
        {"Key": fresh_key, "VersionId": "fresh-v1", "LastModified": now - timedelta(days=1), "Size": 314},
        {"Key": "payments/other.enc", "VersionId": "other-v1", "LastModified": now - timedelta(days=30), "Size": 999},
    ]
    fake.delete_markers = [
        {"Key": old_key, "VersionId": "old-marker", "LastModified": now - timedelta(days=19)},
    ]
    fake.objects[fresh_key] = {
        "payload": b"fresh",
        "modified": now - timedelta(days=1),
        "version_id": "fresh-v1",
    }

    count, deleted_bytes = media_backup._prune(
        media_backup._s3_env(), s3=fake, now=now
    )

    assert count == 2
    assert deleted_bytes == 313
    assert (old_key, "old-v1") in fake.deleted
    assert (old_key, "old-marker") in fake.deleted
    assert (fresh_key, "fresh-v1") not in fake.deleted
    assert all(key.startswith("central-media/") for key, _ in fake.deleted)


def test_prune_always_protects_the_newest_recoverable_backup(monkeypatch) -> None:
    _env(monkeypatch)
    monkeypatch.setenv("BACKUP_RETENTION_DAYS", "7")
    now = datetime(2026, 8, 28, 12, 0, tzinfo=timezone.utc)
    only_key = "central-media/2026/07/01/central-media_only.tar.gz.enc"
    fake = _S3()
    fake.versions = [
        {"Key": only_key, "VersionId": "only-v1", "LastModified": now - timedelta(days=40), "Size": 313},
    ]
    fake.objects[only_key] = {
        "payload": b"only",
        "modified": now - timedelta(days=40),
        "version_id": "only-v1",
    }

    assert media_backup._prune(media_backup._s3_env(), s3=fake, now=now) == (0, 0)
    assert fake.deleted == []


def test_prune_preserves_seven_recovery_points_after_a_long_outage(monkeypatch) -> None:
    _env(monkeypatch)
    monkeypatch.setenv("BACKUP_RETENTION_DAYS", "7")
    monkeypatch.setenv("BACKUP_MIN_RECOVERY_POINTS", "7")
    now = datetime(2026, 8, 28, 12, 0, tzinfo=timezone.utc)
    fake = _S3()
    fake.versions = [
        {
            "Key": f"central-media/2026/08/{day:02d}/central-media_{day:02d}.tar.gz.enc",
            "VersionId": f"v{day}",
            "LastModified": now - timedelta(days=20 - day),
            "Size": 313,
        }
        for day in range(1, 9)
    ]
    fake.objects = {
        row["Key"]: {
            "payload": b"backup",
            "modified": row["LastModified"],
            "version_id": row["VersionId"],
        }
        for row in fake.versions
    }

    count, deleted_bytes = media_backup._prune(
        media_backup._s3_env(), s3=fake, now=now
    )

    assert count == 1
    assert deleted_bytes == 313
    assert len(fake.versions) == 7


def test_recent_backup_skips_duplicate_restart_upload(tmp_path: Path, monkeypatch) -> None:
    source = tmp_path / "source"
    source.mkdir()
    source_db = source / "poshub.db"
    _db(source_db, "recent")
    now = datetime.now(timezone.utc)
    key = "central-media/2026/08/28/central-media_recent.tar.gz.enc"
    fake = _S3()
    fake.objects[key] = {
        "payload": b"encrypted",
        "modified": now - timedelta(hours=1),
        "version_id": "recent-v1",
    }
    fake.versions = [
        {"Key": key, "VersionId": "recent-v1", "LastModified": now - timedelta(hours=1), "Size": 9},
    ]
    _env(monkeypatch)
    monkeypatch.setattr(media_backup, "_s3_client", lambda env: fake)

    assert media_backup.run_once(data_dir=source, db_path=source_db, now=now)
    assert fake.uploads == 0


def test_prune_failure_does_not_block_a_new_upload(tmp_path: Path, monkeypatch) -> None:
    source = tmp_path / "source"
    source.mkdir()
    source_db = source / "poshub.db"
    _db(source_db, "still-upload")
    fake = _S3()
    fake.versions = [
        {
            "Key": "central-media/2026/07/01/central-media_old.tar.gz.enc",
            "VersionId": "old-v1",
            "LastModified": datetime(2026, 7, 1, tzinfo=timezone.utc),
            "Size": 313,
        }
    ]
    fake.delete_errors = [{"Code": "AccessDenied", "Message": "denied"}]
    _env(monkeypatch)
    monkeypatch.setenv("BACKUP_MIN_RECOVERY_POINTS", "0")
    monkeypatch.setattr(media_backup, "_s3_client", lambda env: fake)

    assert media_backup.run_once(
        data_dir=source,
        db_path=source_db,
        now=datetime(2026, 8, 28, tzinfo=timezone.utc),
    )
    assert fake.uploads == 1


def test_freshness_list_failure_does_not_block_a_new_upload(tmp_path: Path, monkeypatch) -> None:
    source = tmp_path / "source"
    source.mkdir()
    source_db = source / "poshub.db"
    _db(source_db, "list-failure")
    fake = _S3()
    fake.list_errors = {"list_object_versions", "list_objects_v2"}
    _env(monkeypatch)
    monkeypatch.setattr(media_backup, "_s3_client", lambda env: fake)

    assert media_backup.run_once(
        data_dir=source,
        db_path=source_db,
        now=datetime(2026, 8, 28, tzinfo=timezone.utc),
    )
    assert fake.uploads == 1


def test_next_scheduler_delay_preserves_daily_cadence_after_restart(monkeypatch) -> None:
    now = datetime(2026, 8, 28, 12, 0, tzinfo=timezone.utc)
    recent_key = "central-media/2026/08/27/central-media_recent.tar.gz.enc"
    fake = _S3()
    fake.objects[recent_key] = {
        "payload": b"recent",
        "modified": now - timedelta(hours=19),
        "version_id": "recent-v1",
    }
    _env(monkeypatch)
    monkeypatch.setattr(media_backup, "_s3_client", lambda env: fake)

    assert media_backup._next_scheduler_delay(24 * 3600, now=now) == pytest.approx(5 * 3600)
