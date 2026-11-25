#!/usr/bin/env python3
"""Run a command once; retain its log, exit status, resources and source hashes.

Usage: python3 scripts/record-command.py LABEL COMMAND [ARG ...]
Heavy Lean commands share TURAN_BUILD_LOCK (or a local default lock).
Existing records are never overwritten. This records failures faithfully;
it does not reinterpret exit codes or change the supplied command.
"""
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
label, *command = sys.argv[1:]
if not label or not command or Path(label).name != label:
    raise SystemExit("usage: record-command.py LABEL COMMAND [ARG ...]")
evidence = root / "verification" / "combined"
evidence.mkdir(parents=True, exist_ok=True)
log = evidence / (label + ".log")
record = evidence / (label + ".json")
snapshot = evidence / (label + "-sources.json")
if any(p.exists() for p in [log, record, snapshot]):
    raise SystemExit("Refusing to overwrite an existing verification attempt")
env = os.environ.copy()
env["LEAN_NUM_THREADS"] = "2"
lock_path = Path(env.get("TURAN_BUILD_LOCK", root / ".verification-work" / "build.lock"))
lock_path.parent.mkdir(parents=True, exist_ok=True)
timeout = int(env.get("TURAN_COMMAND_TIMEOUT", "1200"))
sources = {}
for p in sorted(root.rglob("*.lean")):
    if any(part in {".lake", ".git", ".verification-work"} for part in p.relative_to(root).parts):
        continue
    sources[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
for name in ["comparator.json", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
    sources[name] = hashlib.sha256((root / name).read_bytes()).hexdigest()
snapshot.write_text(json.dumps(sources, indent=2) + "\n")
result = {"command": command, "cwd": str(root), "lean_num_threads": 2,
          "source_snapshot": str(snapshot.relative_to(root)),
          "source_snapshot_sha256": hashlib.sha256(snapshot.read_bytes()).hexdigest(),
          "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "timeout_seconds": timeout}
with lock_path.open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    started = time.monotonic()
    with log.open("x") as out:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=out,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            result["exit_code"] = process.wait(timeout=timeout)
            result["timed_out"] = False
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            result.update(exit_code=None, timed_out=True,
                          whole_owned_process_group_killed_on_timeout=True)
    result["elapsed_seconds"] = round(time.monotonic() - started, 3)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result.update(user_seconds=round(usage.ru_utime, 3), system_seconds=round(usage.ru_stime, 3),
              maximum_rss_kib=usage.ru_maxrss,
              finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              log=str(log.relative_to(root)), log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
record.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2), flush=True)
print("\n".join(log.read_text(errors="replace").splitlines()[-30:]), flush=True)
raise SystemExit(result["exit_code"] if result["exit_code"] is not None else 124)
