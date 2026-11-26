# Turing Universality in Hypergraph Turán Theory

**Lean formalization of Theorems 1.1, 1.2 and 1.3 as one Palomar project.**

Formalization author and responsible maintainer: **Xizhi Liu**.

Public repository: [xliu2022/turan-universality-lean](https://github.com/xliu2022/turan-universality-lean).

Mathematical source: Heng Li and Xizhi Liu, *Turing universality,
computability, and incompleteness in hypergraph Turán theory*, supplied V4
manuscript dated 8 November 2026. The source is included in
`source/turan_universality_V4.tex`; its authors retain their rights.

中文使用说明：[README.zh-CN.md](README.zh-CN.md).

## Results

| Paper result | Formal theorem in `Solution.lean` | Mathematical content |
| --- | --- | --- |
| Theorem 1.1 | `TuranUniversality.Registry.main_theorem` | A primitive-recursive compiler from binary words to single forbidden 3-uniform hypergraphs. Ordinary Turán density is equal to a fixed rational threshold exactly on nonhalting inputs and strictly greater exactly on halting inputs. |
| Theorem 1.2 | `TuranUniversality.Registry.numerical_main_theorem` | A compiler jointly primitive recursive in the uniformity and input word, for every uniformity at least three; exact density scaling; input-independent finite templates with globally optimal uniform weights and free blowups. |
| Theorem 1.3 | `TuranUniversality.Registry.structural_main_theorem` | A jointly primitive-recursive structural compiler for every uniformity above one fixed threshold; one extremal profile and original-vertex edit stability in the nonhalting case; two nonempty compact separated phases, each homeomorphic to the entire inner extremal space, in the halting case. |

All three theorems are selected by **one** `comparator.json`, with
`definition_names: []`. Each theorem keeps its own existential quantifiers;
merging the entry does not add an assertion identifying their witnesses.
The proof development constructs compatible common data, as documented in
`verification/merge/statement-fidelity.md`.

The package contains all 419 project modules in the union of these three
proofs' source import closures, plus the merged statement, solution and
aggregate entry. Supporting results occur where required by those proofs.
Theorem 1.4, object-language ZFC internalization, the later independent
submissions and transcendental-density developments are outside this entry.
This is not a claim that the entire paper has been formalized.

## Statement and proof separation

`Challenge.lean` is an independent statement file with **12 Mathlib imports**,
538 lines and 21,767 bytes. It repeats the mathematical definitions needed
to read the three results. Its only three `sorry` terms are the deliberate
target-theorem placeholders required for statement comparison.

`Solution.lean` imports the three complete proof roots and does not import
`Challenge`. The proof development contains no unresolved `sorry` and does
not introduce custom axioms or use `native_decide`. The permitted axioms are
exactly `propext`, `Classical.choice` and `Quot.sound`. The current export and
axiom audits, rather than the lexical scan alone, are the evidence for this
trust boundary.

The Challenge is below Palomar's hard limits of 1,000 lines and 100 KiB. It
exceeds the 300-line readability recommendation; the combined mathematical
interface and all three full statements are deliberately kept visible.

## Build

Install [Elan](https://github.com/leanprover/elan), then run these commands
from this directory:

```sh
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
```

Pinned versions:

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- All transitive package revisions are recorded in `lake-manifest.json`.

The repository contains the complete project source, configuration, manuscript,
documentation, verification scripts and current verification evidence.
The original distribution archive also includes the exact checked Challenge and Solution exports as
`proof-exports/*.ndjson.gz`; see `docs/VERIFICATION.md` for replay commands.
These optional generated certificates are ignored by Git and are not needed
to compile or publish the source project.
Mathlib, the Lean toolchain and disposable build caches are fetched using
the pins above; they are not bundled. An initial build therefore needs
network access. The local preparation reused matching dependency and module
caches; the recorded Lake job total includes cache replays, not that many
freshly compiled project files.

## Verification

On 25 November 2026 Palomar mechanically verified Theorems 1.1–1.3 as
selected by `comparator.json` at commit `971e68d2122c3901a73a6187ce96ffc97d0f0729`.
Comparator matched all three statements and checked their axiom dependencies.
Lean, NanoDa and con-ron accepted the Solution export.
[Official verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45563382429).

During the earlier local preparation, `bubblewrap` could not open a
`NETLINK_ROUTE` socket. The local build, axiom audits and direct Lean and
NanoDa replays succeeded. [Local results](verification/combined/RESULTS.json)
and [verification history](docs/VERIFICATION.md).

The normal sandboxed local check is:

```sh
bash scripts/verify-comparator.sh
```

It keeps Comparator's sandbox enabled and registers the toolchain's NanoDa
checker for the required-kernel phase. It is a local preflight, not a Palomar
submission. `docs/VERIFICATION.md` also records supported pre-export
comparison and direct kernel replay, with their precise limitations.

## Mathematical fidelity

Read `verification/merge/statement-fidelity.md` alongside the Challenge.
The main implementation choices are:

- Finite hypergraphs use labeled finite vertex types. Turán density is
  defined by an infimum, with convergence of the ordinary normalized
  extremal numbers proved.
- Halting uses a fixed binary partial-recursive evaluator, linked in both
  directions to a finite-state two-sided-tape interpreter. No literal
  step-for-step identity with the manuscript's one-sided presentation is
  asserted.
- The exact rational-threshold formula, density scaling, effectiveness and
  structural conclusions are retained. Some encodings and sufficient
  constants differ from the manuscript. The compiler functions have genuine
  `Primrec` proofs, although some fixed witnesses are selected using
  `Classical.choice`. The package does not supply an extracted executable
  compiler or a fully evaluated numerical threshold.
- Theorem 1.3 includes the specified finite-profile rounding and edit
  stability. In the halting case, each phase is homeomorphic to the entire
  inner extremal space, and the whole outer extremal space is homeomorphic
  to the product of `Bool` with that inner space. No additional claim is
  silently inferred from the prose following that theorem in the manuscript.

The source-closure manifest records the SHA-256 of each copied proof module.
The statement-merge report records copied declaration ranges and the
independent review of the merged interface.

## Preparing a Palomar submission

Use the public repository **`xliu2022/turan-universality-lean`** and the full
40-character SHA of the pushed commit to be reviewed. The Lean project is at
the repository root; the optional project and metadata path fields can be
left blank for this layout.
The selected comparator path is simply **`comparator.json`**; it selects all
three results. `formalization.yaml` supplies the title, abstract, source
provenance, human responsibility, AI-assistance disclosure and review status.

The provided workflows are:

- `.github/workflows/lean.yml`: source and metadata checks, compilation and
  the required-kernel local Comparator preflight.
- `.github/workflows/palomar-full.yml`: a manually dispatched call to the
  pinned official Palomar full mechanical preflight. The dispatcher supplies
  the truthful authorization relationship. It does not register an entry.

The official workflow and its `pipeline_commit` are both pinned to
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. Run the full preflight from
[GitHub Actions](https://github.com/xliu2022/turan-universality-lean/actions/workflows/palomar-full.yml)
and use the exact commit of a passing run. Preflight does not register the result;
submission and registration are separate steps at
[Palomar's submission site](https://submit.palomar-registry.org/).
The release and verification records retain the publication status of the
original preparation run. The official rules remain authoritative:
[Palomar policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).

## Provenance and license

The formalization is licensed under **Apache-2.0**; see `LICENSE` and `NOTICE`.
The finite-hypergraph and ordinary extremal-density foundations adapt two
files from Xizhi Liu's `improved-sidorenko-lean` at commit
`ba6f109bf01436ca15e55fdf5d35dbea85ffd9c9`, retaining their notices. Mathlib and
other dependencies retain their own licenses.

The pre-submission review was conducted by the agents listed in
[`formalization.yaml`](formalization.yaml), which also describes AI assistance during development.
