#!/usr/bin/env python3
"""Export selected theorems with the primitives required by lake comparator.

The extra targets are copied from Lean 4.35.0-rc2's
Lake/CLI/Check.lean: builtinTargets, primitiveTargets, and standard axioms.
This helper does not replace sandboxed Comparator verification. It prepares
an NDJSON file for direct independent-kernel checks or --*-from-export audits.
"""

import argparse
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lake", default="lake", help="the pinned toolchain's lake executable")
parser.add_argument("output", type=Path)
parser.add_argument("module")
parser.add_argument("theorems", nargs="+")
args = parser.parse_args()

primitives = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
    "Nat", "String", "String.mk", "Char", "optParam", "autoParam",
    "semiOutParam", "outParam",
]
axioms = ["propext", "Quot.sound", "Classical.choice"]
quotients = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
targets = list(dict.fromkeys(quotients + args.theorems + axioms + primitives))
command = [args.lake, "env", "leanexport", args.module, "--"] + targets
args.output.parent.mkdir(parents=True, exist_ok=True)
started = time.monotonic()
with args.output.open("wb") as output:
    result = subprocess.run(command, stdout=output, check=False)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
print(json.dumps({
    "command": command,
    "exit_code": result.returncode,
    "elapsed_seconds": round(time.monotonic() - started, 3),
    "user_seconds": round(usage.ru_utime, 3),
    "system_seconds": round(usage.ru_stime, 3),
    "maximum_rss_kib": usage.ru_maxrss,
    "output": str(args.output),
    "output_bytes": args.output.stat().st_size,
}), file=sys.stderr)
raise SystemExit(result.returncode if result.returncode >= 0 else 128 - result.returncode)
