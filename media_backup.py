"""Encrypted off-site backup for the central media database and files."""
from __future__ import annotations

import hashlib
import os
import re
import shutil
import sqlite3
import tarfile
import tempfile
import threading
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path, PurePosixPath
from typing import Optional

import backup_crypto


_PREFIX = "central-media"
_started = False
_lock = threading.Lock()


def _log(message: str) -> None:
    print(f"[central-media-backup] {message}", flush=True)


def _flag(name: str, default: str = "0") -> bool:
    return os.environ.get(name, default).strip().lower() in ("1", "true", "yes", "on")


def _secret() -> str:
    value = os.environ.get("BACKUP_ENCRYPTION_KEY", "").strip()
    if len(value.encode("utf-8")) < 32:
        raise RuntimeError("BACKUP_ENCRYPTION_KEY with at least 32 characters is required")
    return value


def _s3_env() -> Optional[dict]:
    values = {
        "bucket": os.environ.get("BACKUP_S3_BUCKET", "").strip(),
        "access": os.environ.get("BACKUP_S3_ACCESS_KEY", "").strip(),
        "secret": os.environ.get("BACKUP_S3_SECRET_KEY", "").strip(),
        "endpoint": os.environ.get("BACKUP_S3_ENDPOINT", "").strip(),
        "region": os.environ.get("BACKUP_S3_REGION", "").strip(),
    }
    if not (values["bucket"] and values["access"] and values["secret"]):
        return None
    if str(values["endpoint"]).lower().startswith("http://"):
        raise RuntimeError("BACKUP_S3_ENDPOINT must use HTTPS")
    if not values["region"] and values["endpoint"]:
        match = re.search(r"s3\.([a-z0-9-]+)\.backblazeb2\.com", values["endpoint"], re.I)
        if match:
            values["region"] = match.group(1)
    if _flag("BACKUP_REQUIRE_EU_REGION", "1") and not str(values["region"]).lower().startswith("eu-"):
        raise RuntimeError("EU backup guard rejected the configured object-storage region")
    return values


def _s3_client(env: dict):
    import boto3  # type: ignore
    from botocore.config import Config  # type: ignore

    endpoint = str(env.get("endpoint") or "")
    if endpoint and not endpoint.startswith("http"):
        endpoint = "https://" + endpoint
    return boto3.client(
        "s3",
        aws_access_key_id=env["access"],
        aws_secret_access_key=env["secret"],
        endpoint_url=endpoint or None,
        region_name=env.get("region") or None,
        config=Config(signature_version="s3v4", s3={"addressing_style": "path"}),
    )


def _verify_db(path: Path) -> None:
    con = sqlite3.connect(f"file:{path.as_posix()}?mode=ro", uri=True, timeout=30.0)
    try:
        row = con.execute("PRAGMA quick_check").fetchone()
        if not row or str(row[0]).lower() != "ok":
            raise RuntimeError(f"SQLite quick_check failed: {row!r}")
    finally:
        con.close()


def _install_verified_db(source: Path, target: Path) -> None:
    """Stage on the persistent disk before the atomic replacement."""
    target.parent.mkdir(parents=True, exist_ok=True)
    handle, staged_name = tempfile.mkstemp(
        prefix=f".{target.name}.restore-",
        suffix=".tmp",
        dir=str(target.parent),
    )
    os.close(handle)
    staged = Path(staged_name)
    try:
        shutil.copyfile(source, staged)
        _verify_db(staged)
        os.replace(staged, target)
    finally:
        staged.unlink(missing_ok=True)


def _snapshot_db(source: Path, destination: Path) -> None:
    src = sqlite3.connect(str(source), timeout=30.0)
    try:
        dst = sqlite3.connect(str(destination), timeout=30.0)
        try:
            src.backup(dst)
        finally:
            dst.close()
    finally:
        src.close()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _backup_version_rows(s3, env: dict) -> list[dict]:
    """Return every data version/delete marker owned by central-media."""
    rows: list[dict] = []
    paginator = s3.get_paginator("list_object_versions")
    for page in paginator.paginate(Bucket=env["bucket"], Prefix=f"{_PREFIX}/"):
        for obj in page.get("Versions", []) or []:
            key = str(obj.get("Key") or "")
            version_id = str(obj.get("VersionId") or "")
            if not key.startswith(f"{_PREFIX}/") or not key.endswith(".tar.gz.enc") or not version_id:
                continue
            rows.append(
                {
                    "Key": key,
                    "VersionId": version_id,
                    "LastModified": obj["LastModified"],
                    "Size": int(obj.get("Size") or 0),
                    "DeleteMarker": False,
                    "IsLatest": bool(obj.get("IsLatest")),
                }
            )
        for obj in page.get("DeleteMarkers", []) or []:
            key = str(obj.get("Key") or "")
            version_id = str(obj.get("VersionId") or "")
            if not key.startswith(f"{_PREFIX}/") or not key.endswith(".tar.gz.enc") or not version_id:
                continue
            rows.append(
                {
                    "Key": key,
                    "VersionId": version_id,
                    "LastModified": obj["LastModified"],
                    "Size": 0,
                    "DeleteMarker": True,
                    "IsLatest": bool(obj.get("IsLatest")),
                }
            )
    return rows


def _visible_backup_rows(s3, env: dict) -> list[dict]:
    rows: list[dict] = []
    paginator = s3.get_paginator("list_objects_v2")
    for page in paginator.paginate(Bucket=env["bucket"], Prefix=f"{_PREFIX}/"):
        for obj in page.get("Contents", []) or []:
            key = str(obj.get("Key") or "")
            if not key.startswith(f"{_PREFIX}/") or not key.endswith(".tar.gz.enc"):
                continue
            rows.append(
                {
                    "Key": key,
                    "LastModified": obj["LastModified"],
                    "Size": int(obj.get("Size") or 0),
                }
            )
    return rows


def _latest_visible_backup_at(s3, env: dict) -> Optional[datetime]:
    rows = _visible_backup_rows(s3, env)
    return max((row["LastModified"] for row in rows), default=None)


def _has_recent_backup(s3, env: dict, *, now: datetime) -> bool:
    hours = max(0.0, float(os.environ.get("BACKUP_MIN_INTERVAL_HOURS", "20") or "20"))
    if hours <= 0:
        return False
    latest = _latest_visible_backup_at(s3, env)
    return bool(latest is not None and latest >= now - timedelta(hours=hours))


def _try_prune(env: dict, *, s3, now: datetime, phase: str) -> Optional[tuple[int, int]]:
    """Log cleanup failures without turning them into an upload outage."""
    try:
        return _prune(env, s3=s3, now=now)
    except Exception as exc:
        _log(f"{phase} prune failed: {exc}")
        return None


def run_once(*, data_dir: Path | str, db_path: Path | str, now: Optional[datetime] = None) -> bool:
    """Snapshot SQLite plus /static, encrypt it, and upload it to EU storage."""
    try:
        data_dir = Path(data_dir).resolve()
        db_path = Path(db_path).resolve()
        if not db_path.exists():
            _log(f"database missing at {db_path}")
            return False
        env = _s3_env()
        if not env:
            _log("S3 environment is not configured")
            return False
        secret = _secret()
        now = now or datetime.now(timezone.utc)
        s3 = _s3_client(env)
        # Prune first so a full B2 cap can recover instead of blocking the
        # upload that previously had to succeed before cleanup could run.
        _try_prune(env, s3=s3, now=now, phase="pre-upload")
        try:
            if _has_recent_backup(s3, env, now=now):
                _log("recent encrypted snapshot already exists; skipping duplicate startup backup")
                return True
        except Exception as exc:
            # Listing is only a duplicate guard. A temporary list failure or
            # a restricted key must never prevent creation of a new backup.
            _log(f"could not check latest backup; proceeding with upload: {exc}")
        name = f"central-media_{now:%Y%m%dT%H%M%SZ}.tar.gz"
        with tempfile.TemporaryDirectory(prefix="central_media_backup_") as td:
            root = Path(td)
            snapshot = root / "poshub.db"
            archive_path = root / name
            encrypted_path = root / f"{name}.enc"
            _snapshot_db(db_path, snapshot)
            _verify_db(snapshot)
            with tarfile.open(archive_path, "w:gz") as archive:
                archive.add(snapshot, arcname="poshub.db", recursive=False)
                static_dir = data_dir / "static"
                if static_dir.exists():
                    archive.add(static_dir, arcname="static", recursive=True)
            backup_crypto.encrypt_file(archive_path, encrypted_path, secret)
            key = f"{_PREFIX}/{now:%Y/%m/%d}/{encrypted_path.name}"
            size_bytes = encrypted_path.stat().st_size
            s3.upload_file(
                str(encrypted_path),
                env["bucket"],
                key,
                ExtraArgs={
                    "ContentType": "application/octet-stream",
                    "ServerSideEncryption": "AES256",
                    "Metadata": {
                        "m3-backup-format": "central-media-aesgcm-v1",
                        "ciphertext-sha256": _sha256(encrypted_path),
                    },
                },
            )
        _try_prune(env, s3=s3, now=now, phase="post-upload")
        _log(f"uploaded encrypted database and media snapshot to {key} ({size_bytes} bytes)")
        return True
    except Exception as exc:
        _log(f"backup failed: {exc}")
        return False


def _prune(
    env: dict,
    *,
    s3=None,
    now: Optional[datetime] = None,
) -> tuple[int, int]:
    """Permanently delete expired B2 versions, never unversioned objects."""
    retention = max(1, int(os.environ.get("BACKUP_RETENTION_DAYS", "7") or "7"))
    cutoff = (now or datetime.now(timezone.utc)) - timedelta(days=retention)
    s3 = s3 or _s3_client(env)
    rows = _backup_version_rows(s3, env)

    recoverable = [row for row in rows if not row["DeleteMarker"]]
    visible = _visible_backup_rows(s3, env)
    minimum_points = max(
        1,
        int(os.environ.get("BACKUP_MIN_RECOVERY_POINTS", "7") or "7"),
    )
    protected: set[tuple[str, str]] = set()
    for visible_row in sorted(
        visible,
        key=lambda row: row["LastModified"],
        reverse=True,
    )[:minimum_points]:
        candidates = [row for row in recoverable if row["Key"] == visible_row["Key"]]
        if not candidates:
            continue
        current = max(
            candidates,
            key=lambda row: (bool(row.get("IsLatest")), row["LastModified"]),
        )
        protected.add((current["Key"], current["VersionId"]))

    expired = [
        row
        for row in rows
        if row["LastModified"] < cutoff
        and (row["Key"], row["VersionId"]) not in protected
    ]
    # Remove data versions before their delete markers. All removals include a
    # VersionId, which is required to release storage in versioned B2 buckets.
    expired.sort(key=lambda row: (bool(row["DeleteMarker"]), row["LastModified"]))
    deleted_bytes = sum(int(row.get("Size") or 0) for row in expired)
    for offset in range(0, len(expired), 1000):
        batch = expired[offset : offset + 1000]
        response = s3.delete_objects(
            Bucket=env["bucket"],
            Delete={
                "Objects": [
                    {"Key": row["Key"], "VersionId": row["VersionId"]}
                    for row in batch
                ],
                "Quiet": True,
            },
        )
        errors = (response or {}).get("Errors", []) or []
        if errors:
            raise RuntimeError(f"permanent B2 prune rejected {len(errors)} object version(s)")
    if expired:
        _log(f"permanently pruned {len(expired)} version(s), {deleted_bytes} bytes")
    return len(expired), deleted_bytes


def _latest_key(env: dict) -> str:
    candidates = []
    paginator = _s3_client(env).get_paginator("list_objects_v2")
    for page in paginator.paginate(Bucket=env["bucket"], Prefix=f"{_PREFIX}/"):
        for obj in page.get("Contents", []) or []:
            key = str(obj.get("Key") or "")
            if key.endswith(".tar.gz.enc"):
                candidates.append((obj["LastModified"], key))
    if not candidates:
        raise RuntimeError("no encrypted central-media backup exists")
    return max(candidates, key=lambda item: item[0])[1]


def _safe_extract(archive_path: Path, destination: Path) -> None:
    max_bytes = max(1, int(os.environ.get("BACKUP_RESTORE_MAX_BYTES", str(10 * 1024**3))))
    total = 0
    with tarfile.open(archive_path, "r:gz") as archive:
        for member in archive.getmembers():
            name = PurePosixPath(member.name)
            if name.is_absolute() or ".." in name.parts:
                raise RuntimeError("backup archive contains an unsafe path")
            if not (member.name == "poshub.db" or member.name == "static" or member.name.startswith("static/")):
                raise RuntimeError("backup archive contains an unexpected path")
            if member.issym() or member.islnk() or member.isdev():
                raise RuntimeError("backup archive contains an unsafe member type")
            target = destination.joinpath(*name.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if not member.isfile():
                raise RuntimeError("backup archive contains an unsupported member type")
            total += int(member.size or 0)
            if total > max_bytes:
                raise RuntimeError("backup archive exceeds the restore size limit")
            target.parent.mkdir(parents=True, exist_ok=True)
            source = archive.extractfile(member)
            if source is None:
                raise RuntimeError("backup archive member cannot be read")
            with source, target.open("wb") as output:
                shutil.copyfileobj(source, output, length=1024 * 1024)


def restore_latest_if_requested(*, data_dir: Path | str, db_path: Path | str) -> bool:
    """Restore only into a new empty service disk during the EU migration."""
    if not _flag("BACKUP_RESTORE_LATEST"):
        return False
    data_dir = Path(data_dir).resolve()
    db_path = Path(db_path).resolve()
    static_dir = data_dir / "static"
    if (db_path.exists() and db_path.stat().st_size) or (
        static_dir.exists() and any(path.is_file() for path in static_dir.rglob("*"))
    ):
        _log("restore skipped because the target disk already contains data")
        return False
    env = _s3_env()
    if not env:
        raise RuntimeError("S3 configuration is required for migration restore")
    key = os.environ.get("BACKUP_RESTORE_S3_KEY", "").strip() or _latest_key(env)
    with tempfile.TemporaryDirectory(prefix="central_media_restore_") as td:
        root = Path(td)
        encrypted = root / "backup.tar.gz.enc"
        archive = root / "backup.tar.gz"
        extracted = root / "extracted"
        extracted.mkdir()
        _s3_client(env).download_file(env["bucket"], key, str(encrypted))
        backup_crypto.decrypt_file(encrypted, archive, _secret())
        _safe_extract(archive, extracted)
        restored_db = extracted / "poshub.db"
        _verify_db(restored_db)
        restored_static = extracted / "static"
        data_dir.mkdir(parents=True, exist_ok=True)
        if restored_static.exists():
            shutil.copytree(restored_static, static_dir, dirs_exist_ok=True)
        _install_verified_db(restored_db, db_path)
    _log(f"restored and verified {key}")
    return True


def _loop(data_dir: Path, db_path: Path, interval_seconds: float, delay_seconds: float) -> None:
    time.sleep(delay_seconds)
    while True:
        run_once(data_dir=data_dir, db_path=db_path)
        time.sleep(_next_scheduler_delay(interval_seconds))


def _next_scheduler_delay(interval_seconds: float, *, now: Optional[datetime] = None) -> float:
    """Keep the daily cadence even when a restart initially skips a backup."""
    retry_seconds = min(interval_seconds, 15 * 60.0)
    try:
        env = _s3_env()
        if not env:
            return retry_seconds
        latest = _latest_visible_backup_at(_s3_client(env), env)
        if latest is None:
            return retry_seconds
        due_at = latest + timedelta(seconds=interval_seconds)
        remaining = (due_at - (now or datetime.now(timezone.utc))).total_seconds()
        if remaining <= 0:
            return retry_seconds
        return max(60.0, min(interval_seconds, remaining))
    except Exception as exc:
        _log(f"could not calculate next backup time: {exc}")
        return retry_seconds


def start_scheduler(*, data_dir: Path | str, db_path: Path | str) -> None:
    global _started
    try:
        if not _flag("BACKUP_ENABLED", "1") or not _s3_env():
            _log("scheduler idle: S3 environment is not configured or backups are disabled")
            return
        _secret()
        with _lock:
            if _started:
                return
            interval = max(1.0, float(os.environ.get("BACKUP_INTERVAL_HOURS", "24") or "24")) * 3600
            delay = min(3600.0, max(5.0, float(os.environ.get("BACKUP_INITIAL_DELAY_SECONDS", "60") or "60")))
            threading.Thread(
                target=_loop,
                args=(Path(data_dir), Path(db_path), interval, delay),
                name="central-media-backup",
                daemon=True,
            ).start()
            _started = True
            _log(f"scheduler started: first backup in {delay:.0f}s")
    except Exception as exc:
        _log(f"scheduler not started: {exc}")
