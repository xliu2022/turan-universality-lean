#!/usr/bin/env bash
set -euo pipefail

# Required-kernel CI check: judge the selected Solution against its Challenge using the pinned
# toolchain's Comparator, Lean kernel and NanoDa. Keep Comparator's bwrap
# sandbox enabled. This local CI check is not the full Palomar verifier.
#
# Adapted from PalomarRegistry/PalomarTemplate at
# 2891de4c48955af824969a263d31b25e7a9a1406 (Apache-2.0).
# Its exact original is preserved at
# verification/template/verify-comparator-original.sh.
#
# The adjustment follows PalomarRegistry/PalomarSubmission at
# 14aa8d6b3c2f14a8540605e37144560b9a00e7e7:
# scripts/verify_submission.py excludes con-ron from mandatory Comparator
# kernels, then runs it separately as advisory. A recognized support/capacity
# decline does not erase Lean/NanoDa acceptance; actual rejection or an unknown
# error remains blocking. The official workflow owns its sandbox, controls,
# authenticated checker updates and capacity classification. We do not replace
# those with a blanket continue-on-error or claim an official verification.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

if [ "$#" -gt 1 ]; then
  echo "usage: $0 [comparator.json]" >&2
  exit 2
fi
config_source=${1:-comparator.json}

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy registers only the mandatory independent kernel, matching the
# official workflow's mandatory phase. Con-ron is not a submitter toggle.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - "$config_source" "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake exe cache get
lake comparator --config "$config"
