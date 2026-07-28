"""Sign and independently verify RLVerify run artifacts."""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)


def _canonical(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _load_or_create_key(path: Path) -> Ed25519PrivateKey:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        return serialization.load_pem_private_key(path.read_bytes(), password=None)
    except FileNotFoundError:
        key = Ed25519PrivateKey.generate()
        encoded = key.private_bytes(
            serialization.Encoding.PEM,
            serialization.PrivateFormat.PKCS8,
            serialization.NoEncryption(),
        )
        try:
            fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        except FileExistsError:
            return serialization.load_pem_private_key(
                path.read_bytes(), password=None)
        with os.fdopen(fd, "wb") as fh:
            fh.write(encoded)
        return key


def write_signed_manifest(
    run_dir: str | os.PathLike,
    record: dict,
    *,
    record_path: str | os.PathLike | None = None,
) -> str:
    """Hash input/record/certificate and sign those hashes with Ed25519."""
    root = Path(run_dir)
    input_path = root / "input.json"
    trusted = record.get("trusted_recheck") or {}
    certificate_path = Path(trusted["source_artifact"]) \
        if trusted.get("source_artifact") else None
    exact_record = _canonical(record)
    signed = {
        "schema": "rlverify-integrity-v1",
        "input_sha256": (
            _sha256_bytes(input_path.read_bytes()) if input_path.exists() else None
        ),
        "input_payload_sha256": trusted.get("input_sha256"),
        "record_sha256": _sha256_bytes(exact_record),
        "certificate_sha256": (
            _sha256_bytes(certificate_path.read_bytes())
            if certificate_path is not None and certificate_path.exists()
            else None
        ),
        "input_path": str(input_path),
        "record_path": str(record_path) if record_path else None,
        "certificate_path": str(certificate_path) if certificate_path else None,
    }
    configured = os.environ.get("RLVERIFY_SIGNING_KEY", "").strip()
    key_path = Path(configured) if configured else root / ".integrity-signing-key.pem"
    private_key = _load_or_create_key(key_path)
    public_raw = private_key.public_key().public_bytes(
        serialization.Encoding.Raw,
        serialization.PublicFormat.Raw,
    )
    signature = private_key.sign(_canonical(signed))
    manifest = {
        "signed": signed,
        "signature_algorithm": "Ed25519",
        "signature": base64.b64encode(signature).decode(),
        "public_key": base64.b64encode(public_raw).decode(),
        "public_key_sha256": _sha256_bytes(public_raw),
    }
    path = root / "integrity.json"
    path.write_text(json.dumps(manifest, indent=2) + "\n")
    return str(path)


def verify_manifest(
    manifest_path: str | os.PathLike,
    *,
    record_path: str | os.PathLike | None = None,
    input_path: str | os.PathLike | None = None,
    certificate_path: str | os.PathLike | None = None,
) -> dict:
    """Verify the signature and, when present, every referenced artifact hash."""
    manifest = json.loads(Path(manifest_path).read_text())
    signed = manifest["signed"]
    public = Ed25519PublicKey.from_public_bytes(
        base64.b64decode(manifest["public_key"]))
    try:
        public.verify(base64.b64decode(manifest["signature"]), _canonical(signed))
    except InvalidSignature as exc:
        raise ValueError("integrity manifest signature is invalid") from exc

    resolved = {
        "input": input_path or signed.get("input_path"),
        "record": record_path or signed.get("record_path"),
        "certificate": certificate_path or signed.get("certificate_path"),
    }
    expected = {
        "input": signed.get("input_sha256"),
        "record": signed.get("record_sha256"),
        "certificate": signed.get("certificate_sha256"),
    }
    checked: dict[str, bool] = {}
    for kind, raw_path in resolved.items():
        if not raw_path or not expected[kind]:
            continue
        path = Path(raw_path)
        if kind == "record":
            value = _canonical(json.loads(path.read_text()))
        else:
            value = path.read_bytes()
        checked[kind] = _sha256_bytes(value) == expected[kind]
        if not checked[kind]:
            raise ValueError(f"{kind} artifact hash does not match the manifest")
    return {
        "signature_valid": True,
        "artifacts": checked,
        "public_key_sha256": manifest["public_key_sha256"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verify an RLVerify signed integrity manifest")
    parser.add_argument("manifest")
    parser.add_argument("--record")
    parser.add_argument("--input")
    parser.add_argument("--certificate")
    args = parser.parse_args(argv)
    try:
        result = verify_manifest(
            args.manifest,
            record_path=args.record,
            input_path=args.input,
            certificate_path=args.certificate,
        )
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"INVALID: {exc}")
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
