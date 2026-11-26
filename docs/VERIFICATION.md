# Verification of the combined Theorems 1.1–1.3 entry

## Palomar mechanical verification

On 25 November 2026 Palomar's submission verifier recorded a pass for commit
`971e68d2122c3901a73a6187ce96ffc97d0f0729` with `comparator.json`. Comparator
matched all three theorems and checked their axiom dependencies. Lean and NanoDa
accepted the Solution export. The advisory con-ron replay also accepted it,
with exit code 0. The mechanical report was issued at 10:06:46 UTC.
[Official run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45563382429)
and [mechanical report](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45563382429/artifacts/15011212386).

## Local preparation on 25 November 2026

The table records the earlier checks used to prepare the distribution archive.
The machine timestamps in the local records use UTC.
[Local results](../verification/combined/RESULTS.json).

| Check | Result | Evidence |
| --- | --- | --- |
| Full `lake build` with the merged roots | Passed | `build-01.json` and log |
| Recursive statement and definition comparison for all three targets | Passed before kernel launch | `comparator-from-exports-01.log`, pinned control flow below |
| Comparator permitted-axiom validation | Passed before kernel launch | Same comparison run |
| Direct Lean default kernel replay | Passed, exit 0 | `leanchecker-01.json` and log |
| Direct NanoDa replay | Passed, exit 0; 33,221 declarations, zero typechecker errors | `nanoda-01.json` and log |
| Ordinary and full-import axiom audits | All three theorems use exactly the standard three axioms | `axiom-audit-public-01` and `axiom-audit-full-01` records |
| Solution import separation | No Challenge import in either actual module environment | `public-import-closure.json`, `full-import-closure.json` |
| Complete exported declaration inventory | Passed for both files and all three theorem roots | `export-inventory.json` |
| Source policy, copied proof preservation and upstream metadata schema | Passed | `source-and-metadata.json`, `source-policy.log` |
| Whole sandboxed Comparator command | Failed at sandbox startup, exit 1 | `sandbox-default-01.json` and log |
| Whole pre-export Comparator command | Comparison passed, then sandboxed kernel startup failed, exit 1 | `comparator-from-exports-01.json` and log |

All evidence filenames in this table are under `verification/combined/`.
The build reported 9,355 Lake jobs, including cache replays. It reused exact
matching dependencies and unchanged proof-module caches; this is not a claim
that 9,355 modules were freshly compiled. The merged Challenge and Solution,
the project aggregate and `Structural.Main` were built in this run.

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
The only three deliberate statement holes are in `Challenge.lean`; they do
not occur in the Solution import closure or Solution proof export.

## Why the comparison passed although its command exited 1

The pinned toolchain is Lean `v4.35.0-rc2`, commit
`11acb17ec6b07a8f9e9173e6845197929540936b`. In that toolchain's
`Lake/CLI/Check.lean`, `verifyMatch` first executes `compareAt` and
`checkAxioms` through `IO.ofExcept`. It calls `runKernels` only after both have
succeeded. The relevant exact excerpt is preserved in
`verification/combined/comparator-control-flow.txt`, and the full source
file's SHA-256 is in `RESULTS.json`.

The actual log reaches `Running nanoda kernel on solution`, followed by the
same Lean-kernel stage. Each launch fails because `bubblewrap` cannot create
a `NETLINK_ROUTE` socket. Thus the successful comparison and axiom validation
are an inference from the observed stage and the exact pinned control flow;
the overall command remains recorded as **exit 1**. No comparison exemption
was added and the sandbox was not disabled.

The separate direct Lean and NanoDa runs both accepted the exact same
Solution export. Those direct runs establish their stated local kernel
results, but they do not turn a failed sandboxed run into a successful one.
NanoDa reported one nonfatal pretty-printer message, `Unable to print axioms`,
with **zero typechecker errors** and exit 0. Its direct configuration sets
`unpermitted_axiom_hard_error` to `true`.

## Complete export evidence included in the archive

| Export | Uncompressed bytes | Declarations |
| --- | ---: | ---: |
| Challenge | 44,596,260 | 11,439 |
| Solution | 236,462,714 | 33,221 |

`proof-exports/challenge.ndjson.gz` and `proof-exports/solution.ndjson.gz`
contain the exact checked exports, compressed without changing their bytes.
Their compressed and uncompressed hashes are in
`verification/combined/compressed-exports.json`. These are optional replay
data, not required to build the source. The directory is ignored by Git so
publishing the source project does not require uploading generated exports.

Uncompressed SHA-256:

```text
Challenge  2a68126023363447140d50874526b5ab94a09df569df9f9d74d935737480a301
Solution   2660318da2afd01adbbf4bab64bf77c2c8474e805b87229b25a61db48241b796
```

The inventory parses every JSON record and interned name, level and
expression, checks references and unique declarations, and finds each of
the three targets exactly once as a theorem in each export. It also binds
the files to successful exporter completion records and byte counts.
Solution contains exactly the three allowed axioms, and neither `sorryAx`
nor `Lean.ofReduceBool` occurs as an interned name, declaration or constant
expression. It contains no unsafe or partial declaration.

The export format has no special end-of-file footer. Completeness is based
on the successful exporter completion, stable file hashes and byte counts,
complete last record, reference closure and presence of all requested roots.
The inventory is structural validation, not a substitute for kernel checking.
Raw expression digests retain binder and instance-proof syntax; unequal
digests do not imply that two theorem types are definitionally unequal.
The Comparator decides the required comparison.

## Reproduce the local checks

Start with the pinned toolchain and dependencies described in `README.md`.
The normal protected route is:

```sh
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
bash scripts/verify-comparator.sh
```

For local replay of the included certificates:

```sh
mkdir -p .verification-work
gzip -dc proof-exports/challenge.ndjson.gz > .verification-work/challenge.ndjson
gzip -dc proof-exports/solution.ndjson.gz > .verification-work/solution.ndjson
lake env leanchecker --from-export .verification-work/solution.ndjson
```

Prepare NanoDa's strict local configuration and run it:

```sh
python3 - <<'PY'
import json
from pathlib import Path
config = {
    "export_file_path": str(Path(".verification-work/solution.ndjson").resolve()),
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "unpermitted_axiom_hard_error": True,
    "num_threads": 2,
    "nat_extension": True,
    "string_extension": True,
    "print_success_message": True,
}
Path(".verification-work/nanoda.json").write_text(json.dumps(config, indent=2) + "\n")
PY
lake env nanoda_bin .verification-work/nanoda.json
```

The official Comparator supports comparison of independently produced
exports without changing its sandbox policy:

```sh
lake comparator --config comparator.json \
  --challenge-from-export .verification-work/challenge.ndjson \
  --solution-from-export .verification-work/solution.ndjson
```

This command compares the supplied exports and then launches its kernel
checks; it does not establish by itself that exports came from the current
source. For a fresh source-to-export reproduction, run the following after
`lake build` and then repeat the checks:

```sh
python3 scripts/export-theorems.py .verification-work/challenge.ndjson Challenge \
  TuranUniversality.Registry.main_theorem \
  TuranUniversality.Registry.numerical_main_theorem \
  TuranUniversality.Registry.structural_main_theorem
python3 scripts/export-theorems.py .verification-work/solution.ndjson Solution \
  TuranUniversality.Registry.main_theorem \
  TuranUniversality.Registry.numerical_main_theorem \
  TuranUniversality.Registry.structural_main_theorem
lake env lean verification/combined/AuditPublic.lean
lake env lean verification/combined/AuditFull.lean
```

`scripts/record-command.py LABEL COMMAND ...` can retain new logs and resource
records without overwriting old attempts. Choose a new label. The delivered
logs and snapshots describe this preparation run; regenerated files form a
new verification run and should be recorded separately.

The upstream v0.4 metadata schema is included with its provenance for offline
schema validation. The complete manuscript correspondence
and constant/model qualifications are documented separately in
`verification/merge/statement-fidelity.md`.
