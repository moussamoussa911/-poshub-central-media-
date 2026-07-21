"""Streaming authenticated encryption for central-media backups."""
from __future__ import annotations

import hashlib
import os
import struct
import tempfile
from pathlib import Path

from cryptography.hazmat.primitives.ciphers.aead import AESGCM


MAGIC = b"M3DBBK1\n"
_CHUNK_SIZE = 1024 * 1024
_MAX_RECORD_SIZE = _CHUNK_SIZE + 16


def _key(secret: str) -> bytes:
    raw = str(secret or "").strip().encode("utf-8")
    if len(raw) < 32:
        raise ValueError("BACKUP_ENCRYPTION_KEY must contain at least 32 characters")
    return hashlib.sha256(b"m3-render-backup-v1\0" + raw).digest()


def _aad(record_type: bytes, index: int) -> bytes:
    return MAGIC + record_type + struct.pack(">Q", int(index))


def encrypt_file(source: Path, destination: Path, secret: str) -> None:
    source = Path(source)
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    cipher = AESGCM(_key(secret))
    fd, tmp_name = tempfile.mkstemp(prefix=f".{destination.name}.", dir=str(destination.parent))
    try:
        with os.fdopen(fd, "wb") as out, source.open("rb") as inp:
            out.write(MAGIC)
            index = 0
            while True:
                chunk = inp.read(_CHUNK_SIZE)
                if not chunk:
                    break
                nonce = os.urandom(12)
                encrypted = cipher.encrypt(nonce, chunk, _aad(b"D", index))
                out.write(b"D" + nonce + struct.pack(">I", len(encrypted)) + encrypted)
                index += 1
            nonce = os.urandom(12)
            final = cipher.encrypt(nonce, b"", _aad(b"F", index))
            out.write(b"F" + nonce + struct.pack(">I", len(final)) + final)
            out.flush()
            os.fsync(out.fileno())
        os.replace(tmp_name, destination)
    except Exception:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


def decrypt_file(source: Path, destination: Path, secret: str) -> None:
    source = Path(source)
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    cipher = AESGCM(_key(secret))
    fd, tmp_name = tempfile.mkstemp(prefix=f".{destination.name}.", dir=str(destination.parent))
    try:
        with source.open("rb") as inp, os.fdopen(fd, "wb") as out:
            if inp.read(len(MAGIC)) != MAGIC:
                raise ValueError("backup is not an M3 encrypted backup")
            index = 0
            while True:
                record_type = inp.read(1)
                if record_type not in (b"D", b"F"):
                    raise ValueError("backup is truncated or has an invalid record type")
                nonce = inp.read(12)
                raw_length = inp.read(4)
                if len(nonce) != 12 or len(raw_length) != 4:
                    raise ValueError("backup is truncated")
                length = struct.unpack(">I", raw_length)[0]
                if length < 16 or length > _MAX_RECORD_SIZE:
                    raise ValueError("backup contains an invalid record length")
                encrypted = inp.read(length)
                if len(encrypted) != length:
                    raise ValueError("backup is truncated")
                plain = cipher.decrypt(nonce, encrypted, _aad(record_type, index))
                if record_type == b"F":
                    if plain or inp.read(1):
                        raise ValueError("backup contains data after its final record")
                    break
                out.write(plain)
                index += 1
            out.flush()
            os.fsync(out.fileno())
        os.replace(tmp_name, destination)
    except Exception:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise
