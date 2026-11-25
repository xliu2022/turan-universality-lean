# Palomar requirements checked for the combined Theorems 1.1–1.3 project

Checked against official sources on 25 November 2026. This is a packaging review, not a Palomar verification result. References below identify the official sources consulted; changes to the service after this date may require another check.

## Submission unit and statement surface

One selected Comparator configuration produces one Palomar entry. A configuration may select several theorems or definitions, all of which receive mechanical and editorial review. Thus the three main theorem declarations may share `Challenge.lean`, `Solution.lean`, and `comparator.json`. Separate configurations would require separate submissions. The binding submission standard explicitly permits the combined arrangement. [1]

For this project the selected declarations are:

- `TuranUniversality.Registry.main_theorem` — Theorem 1.1.
- `TuranUniversality.Registry.numerical_main_theorem` — Theorem 1.2.
- `TuranUniversality.Registry.structural_main_theorem` — Theorem 1.3.

Each statement retains its original existential quantifiers. Combining entries does not by itself prove that independently quantified witnesses coincide.

## Source and dependency checks

The official preparation guide requires a pinned Lean toolchain, exactly one Lakefile, the Challenge/Solution pair, a Comparator configuration, metadata, and one conventional root license file. Commit the dependency manifest. Every regular submitted Lean source must use `module` and have at most 10,000 physical lines; `.git` and `.lake` are excluded and Lean source symlinks are refused. The Challenge has stricter limits: 1,000 lines and 100 KiB, with warnings above 300 lines or 32 KiB. These limits apply even when the statement contains several theorems. [2]

The binding standard permits only canonical Lean/Mathlib/Tau Ceti/CSLib statement dependencies; project-specific proof modules cannot occur in the Challenge import closure. Its permitted axiom set is at most `propext`, `Classical.choice`, and `Quot.sound`. Deliberate Challenge holes are allowed; Solution proofs must not depend on them. [1]

Use the current verifier rather than copying looser language from the web overview: the current implementation requires Git dependencies on public GitHub repositories at immutable commits, rejects submitted compiled artifacts, and reconstructs the protected Challenge separately from the submitted proof build. [3]

## Metadata for this package

The official metadata profile identifies the following required project facts. [4]

| Field | Package recommendation |
| --- | --- |
| `project.name` | `Turing Universality in Hypergraph Turán Theory` |
| `project.description` | Public mathematical abstract covering only Theorems 1.1–1.3 |
| `project.authors` | `[Xizhi Liu]` |
| `project.responsible_maintainers` | `[Xizhi Liu]` |
| `project.license` | `Apache-2.0`, matching the root license |
| `classification.arxiv` | `math.CO`, `math.LO` |
| `classification.msc2020` | The relevant existing combinatorics/computability codes |
| `sources` | The supplied V4 manuscript, with exact theorem locations and relationship |
| `automation.methods` | Explicit AI-assisted production disclosure |
| `review.status` | The actual completed review and verification state |

The profile accepts one to eight arXiv categories and up to eight MSC2020 codes. An ordinary substantive project does not need a `repository` block; that field identifies a pinned external substantive development only for a thin wrapper. [4]

Use `version: v0.4`. Record the source paper's authors under `sources[].authors`, while earlier formal proof developments belong under `related_formalizations`. `status.sorry_count` excludes intentional Comparator Challenge placeholders. The optional alignment table should list all three selected declarations. The upstream schema permits additional descriptive fields. [5]

Authors and responsible maintainers must be humans; AI credit belongs in automation metadata. Disclose material model/tool roles honestly. Source relationships distinguish formalization, adaptation, independent proof, and background. Avoid a source entry claiming `original-proof`: this package formalizes results already stated in the supplied manuscript. [1]

The source archive's automation account identifies GPT-6 Astra Pro in ChatGPT. Preserve that disclosure without inventing costs, elapsed labor, independent human review, or a repository URL. Keep the inherited source-fidelity explanations relevant to 1.1–1.3, particularly the binary evaluator/two-sided machine, finite labeled constructions, exact scaling, and the structural profile/stability formulation. Remove unrelated transcendence and later-theorem claims.

## Validation commands and their scope

Run from the project root after installing its pinned toolchain:

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build Challenge Solution
./scripts/verify-comparator.sh comparator.json
```

The old archive's Ruby script checked version, basic fields, the fixed license, and template placeholders. It was not a complete substitute for schema validation and is not used by this package's CI. The upstream project documents the following schema check, which the combined CI runs after installing `check-jsonschema`: [6]

```sh
check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

The current Comparator lives in Lean as `lake comparator`; the former standalone repository is archived and directs users to the integrated tool. [7] The retained project wrapper registers the toolchain's NanoDa in a temporary configuration and preserves the sandbox. Do not submit `external_kernels` in the registry configuration. Official verification requires Lean and NanoDa acceptance, then separately attempts con-ron. A recognized advisory con-ron limitation is distinct from a rejection. A reusable full mechanical preflight is predictive, and does not itself render, review, submit, or register a result. [3]

## Pins and local evidence inspected

The project and resolved Mathlib both specify `leanprover/lean4:v4.35.0-rc2`. The current official minimum is `v4.35.0-rc2`, so packaging alone does not require a toolchain upgrade. [8]

The source `lakefile.toml` pins Mathlib to `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Preserve the matching manifest. The existing official full-preflight workflow is pinned to PalomarSubmission commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; both `uses` and `pipeline_commit` name that exact revision. Its `execution_profile: palomar-standard-v1`, full mode, explicit authorization relationship, and 12-character request identifier agree with the documented reusable-workflow interface. This is an intentionally retained pin, not a claim that it is the latest upstream commit.

The local recovered toolchain contains `lake`, `leanexport`, `leanchecker`, `nanoda_bin`, and `con-ron` under `/workspace/scratch/ec525e9616f4/toolchains/lean-4.35.0-rc2-linux/bin`. These are environment paths for this preparation run, not portable project dependencies.

The separate historical reports in `verification/main`, `verification/numerical`, and `verification/structural` within the recovered original development archive (not included in this scoped package) record successful statement/axiom checks and direct Lean/NanoDa replay for earlier separate entries. They also record a historic sandbox launch failure. Neither observation is a test result for the newly merged files. The merged project must carry its own fresh evidence, and the current sandbox behavior must be tested rather than inferred from old logs.

## Publication boundary

An actual submission requires the final public GitHub repository and full pushed 40-character commit SHA. Uncommitted local files and a ZIP alone are not the registered snapshot. The repository's workflow is an explicitly dispatched preflight; it performs no registry submission. The current request prepares a downloadable package and supplies no publication URL. [2]

## Official references

1. [Palomar binding submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), especially sections 2, 2.3–2.4, and 3.
2. [How to submit](https://palomar-registry.org/how-to-submit).
3. [PalomarSubmission verifier and reusable workflow documentation](https://github.com/PalomarRegistry/PalomarSubmission).
4. [Current formalization metadata profile](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/formalization-profile.json).
5. [Upstream v0.4 metadata template](https://github.com/mathlib-initiative/formalization.yaml/blob/main/formalization.yaml).
6. [Upstream metadata schema and validation documentation](https://github.com/mathlib-initiative/formalization.yaml).
7. [Comparator upstream migration notice](https://github.com/leanprover/comparator).
8. [Current minimum toolchain policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json).
