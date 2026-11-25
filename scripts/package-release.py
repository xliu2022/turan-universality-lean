#!/usr/bin/env python3
"""Create and verify a source release ZIP, including available replay certificates.

Run from a verified checkout. The output must be outside the project directory.
This does not publish or submit anything. SHA256SUMS covers the release archive
contents, including optional replay data; it is not a Git-tracked-file manifest.
"""
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import zipfile

root = Path(__file__).resolve().parents[1]
if len(sys.argv) != 2:
    raise SystemExit("usage: python3 scripts/package-release.py /absolute/output.zip")
output = Path(sys.argv[1]).resolve()
if output.is_relative_to(root) or output.exists():
    raise SystemExit("Choose a new output ZIP outside the project directory")
excluded = {".git", ".lake", ".verification-work", "__pycache__"}


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def files():
    result = []
    for directory, subdirs, names in os.walk(root, followlinks=False):
        subdirs[:] = sorted(n for n in subdirs if n not in excluded)
        for n in subdirs:
            if (Path(directory) / n).is_symlink():
                raise RuntimeError(f"Unexpected release-directory symlink: {n}")
        for name in sorted(names):
            path = Path(directory) / name
            if path.is_symlink():
                raise RuntimeError(f"Unexpected release-file symlink: {path}")
            if path.is_file():
                result.append(path)
    return sorted(result)


# Bind the compressed replay copies to the independently checked raw exports.
compressed_record = root / "verification/combined/compressed-exports.json"
if compressed_record.exists():
    for row in json.loads(compressed_record.read_text()):
        path = root / row["file"]
        if not path.exists():
            continue  # Optional generated certificates are ignored by Git.
        if sha256(path) != row["sha256"]:
            raise RuntimeError(f"Compressed certificate changed: {path}")
        with gzip.open(path, "rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != row["uncompressed_sha256"]:
            raise RuntimeError(f"Certificate bytes do not match checked export: {path}")

now = datetime.now(timezone.utc)
base_files = [p for p in files() if p.name not in {"RELEASE.json", "SHA256SUMS"}]
release = {
    "project": "Turing Universality in Hypergraph Turán Theory",
    "scope": ["Theorem 1.1", "Theorem 1.2", "Theorem 1.3"],
    "created_utc": now.isoformat(),
    "file_count": len(base_files) + 2,
    "source_project_modules": 419,
    "comparator_config": "comparator.json",
    "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
    "mathlib_revision": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
    "verification": "verification/combined/RESULTS.json",
    "manifest": "SHA256SUMS",
    "manifest_scope": "Every regular release file except SHA256SUMS itself",
    "generated_replay_certificates_included": (root / "proof-exports/solution.ndjson.gz").is_file(),
    "excluded_generated_directories": sorted(excluded),
    "external_dependencies": "Lean and pinned Mathlib dependencies are fetched, not vendored",
    "published_or_submitted": False,
}
(root / "RELEASE.json").write_text(json.dumps(release, indent=2, ensure_ascii=False) + "\n")
package_files = [p for p in files() if p.name != "SHA256SUMS"]
hashes = {p.relative_to(root).as_posix(): sha256(p) for p in package_files}
(root / "SHA256SUMS").write_text("".join(f"{digest}  {name}\n" for name, digest in hashes.items()))
package_files = files()
assert len(package_files) == release["file_count"]
expected = {p.relative_to(root).as_posix(): sha256(p) for p in package_files}
prefix = "turan-universality-lean/"
output.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(output, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in package_files:
        relative = path.relative_to(root).as_posix()
        info = zipfile.ZipInfo(prefix + relative, now.timetuple()[:6])
        info.create_system = 3
        mode = 0o755 if os.access(path, os.X_OK) else 0o644
        info.external_attr = (stat.S_IFREG | mode) << 16
        info.compress_type = zipfile.ZIP_STORED if path.suffix == ".gz" else zipfile.ZIP_DEFLATED
        with path.open("rb") as source, archive.open(info, "w") as target:
            while chunk := source.read(1024 * 1024):
                target.write(chunk)

# A complete streamed read also exercises ZIP CRC checking. Compare every file.
with zipfile.ZipFile(output) as archive:
    names = archive.namelist()
    assert len(names) == len(set(names)) == len(expected)
    assert set(names) == {prefix + n for n in expected}
    for name, digest in expected.items():
        with archive.open(prefix + name) as stream:
            actual = hashlib.file_digest(stream, "sha256").hexdigest()
        if actual != digest:
            raise RuntimeError(f"ZIP content hash mismatch: {name}")
print(json.dumps({
    "archive": str(output), "bytes": output.stat().st_size,
    "sha256": sha256(output), "file_count": len(expected),
    "uncompressed_bytes": sum(p.stat().st_size for p in package_files),
    "zip_crc_and_every_file_sha256_verified": True,
    "checked_replay_certificates_preserved": True,
}, indent=2))
