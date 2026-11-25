# Theorems 1.1–1.3: independent statement merge

Formalization author and maintainer: **Xizhi Liu**.

This combined submission has one independent `Challenge.lean`, one proof-side
`Solution.lean`, and one `comparator.json` listing three target theorem names.
The target theorem declarations are copied verbatim from the three original
Challenges. Their corresponding completed declarations and proofs are copied
verbatim from the original Solutions. Only explanatory comments, the import
union, and placement in the merged file change.

## Scope and mathematical fidelity

The three theorems keep their own original existentially quantified thresholds
and compilers. Combining them into one project does not identify these witnesses
or strengthen the original statements to a new joint-witness theorem.

- Theorem 1.1 retains the explicit rational baseline, nonempty forbidden graph,
  ordinary density limit, primitive-recursive compiler and both halting equivalences.
- Theorem 1.2 retains the literal rank-three singleton, joint primitive recursion,
  exact scaling, globally optimal template weighting, homomorphism freeness and
  freeness of every finite blowup.
- Theorem 1.3 retains the inner density dichotomy, fixed rank threshold,
  input-independent pattern, exact finite floor/ceiling counts, edge-edit stability,
  nonempty compact phases, phase separators and both homeomorphism conclusions.

Theorem 1.4 and separate extensions are outside this submission.

## Shared declarations

`Challenge12.lean` supplies the canonical shared declarations. In particular,
the original graph equality, graph enumeration and finite/decidable instances
are retained as written; none is replaced by an alternative classical instance.
The table below gives each shared declaration and all original source ranges.
Those ranges refer to the unchanged source snapshot identified by SHA-256 below.
Source files are abbreviated **C1** = `Challenge.lean`, **C2** = `Challenge12.lean`,
**C3** = `TuranUniversality/Palomar/Challenge13.lean`.

| Declaration in `TuranUniversality` | Canonical C2 lines | Other original lines | Source-text agreement |
| --- | --- | --- | --- |
| `RGraph` | 36–38 | C1:40–42; C3:44–46 | Identical |
| `RGraph.IsEmbedding` | 42–45 | C1:46–49; C3:48–51 | Identical |
| `RGraph.ext` | 51–55 | C3:57–61 | Identical |
| `RGraph [DecidableEq instance]` | 57–59 | C3:63–65 | Identical |
| `RGraph.IsHom` | 61–62 | C3:169–170 | Identical |
| `FiniteGraph` | 78–78 | C3:73–73 | Identical |
| `familyFree` | 80–82 | C3:75–77 | Identical |
| `ProbabilityWeights` | 93–94 | C3:242–243 | Identical |
| `extremalNumber` | 100–103 | C1:55–58; C3:82–85 | Identical |
| `extremalDensity` | 106–107 | C1:61–62; C3:87–88 | Identical |
| `turanDensity` | 111–112 | C1:66–67; C3:90–91 | Identical |
| `RGraph.IsEmbedding [Decidable instance]` | 118–120 | C3:67–69 | Identical |
| `RGraph.enumerate` | 129–132 | C3:99–102 | Identical |
| `RGraph.mem_enumerate` | 134–138 | C3:104–108 | Identical |
| `RGraph [Fintype instance]` | 140–140 | C3:110–110 | Identical |
| `familyFree [Decidable instance]` | 144–146 | C3:114–116 | Identical |
| `familyExtremalNumber` | 149–152 | C3:120–123 | Identical |
| `familyExtremalDensity` | 154–155 | C3:125–126 | Identical |
| `familyTuranDensity` | 157–158 | C3:128–129 | Identical |
| `Weighted.rationalThreshold` | 167–173 | C1:76–82 | Identical |
| `Effective.Triple` | 180–180 | C1:89–89; C3:135–135 | Identical |
| `Effective.GraphCode` | 184–184 | C1:93–93; C3:136–136 | Identical |
| `Effective.tripleSet` | 187–187 | C1:96–96; C3:137–137 | Identical |
| `Effective.decodeGraph` | 192–197 | C1:101–106; C3:139–142 | Same data; uniformity-proof syntax differs in C3 |
| `Effective.decodeGraphCode` | 199–199 | C3:144–144 | Identical |
| `Effective.Uniform.Code` | 204–204 | C3:148–148 | Identical |
| `Effective.Uniform.decode` | 206–211 | C3:150–153 | Same data; uniformity-proof syntax differs in C3 |
| `Effective.Uniform.decodeFinite` | 213–213 | C3:155–155 | Identical |
| `Effective.Uniform.decodeFamily` | 215–217 | C3:157–159 | Identical |
| `Computation.BinaryWord` | 227–227 | C1:115–115; C3:304–304 | Identical |
| `Computation.binaryValue` | 231–232 | C1:119–120; C3:308–309 | Identical |
| `Computation.decodeProgram` | 236–237 | C1:124–125; C3:313–314 | Identical |
| `Computation.inputEnabled` | 241–241 | C1:129–129; C3:318–318 | Identical |
| `Computation.wordEval` | 245–246 | C1:133–134; C3:322–323 | Identical |
| `Computation.WordHalts` | 249–249 | C1:137–137; C3:326–326 | Identical |

The two decoders use the unchanged C2 `uniform := by intro ...` proof. C3 uses
equation-style syntax for the same uniformity proposition. This report does not
infer successful elaborated comparison merely from this source-level observation.
The machine-readable companion records every copied source range, destination
range, segment hash, shared declaration and exact target-copy assertion.

## Source snapshot

| Source file | Lines | SHA-256 |
| --- | ---: | --- |
| `Challenge.lean` | 179 | `13694829c53bc1bb7f8579009a383cf4cd778b36bd2e4b9caad669dbf27bbfdb` |
| `Challenge12.lean` | 291 | `fc28eec29560afd692dbc4baec1a8a33bfc53bb339ba7a9079858061f79e6608` |
| `TuranUniversality/Palomar/Challenge13.lean` | 405 | `54100d5f792b9b2a23d1c8ec5490ebc1085d95622945aafa263e42328ac7c8f8` |
| `Solution.lean` | 27 | `82cc5367174c67c0a72cf3039dc1cc3301e45b6ff01fc3bf48c9632d745b0f47` |
| `Solution12.lean` | 38 | `167c6a5d5c569e9a507d2ef16fa97e7a682395e58dd00535bb2af3f81e0eb6b1` |
| `TuranUniversality/Palomar/Solution13.lean` | 13 | `2d8a1ec87699a4d0d4a6f8fa3d09c7784d351c61bb8edc81b0b3efdb7147e5f4` |

## Generated entry points

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Challenge.lean` | 538 | 21767 | `1a3a6f603600e00bad39e17d635638e10601dd7d316f16af5d7e64178ea121f1` |
| `Solution.lean` | 68 | 3388 | `11eba52fd9b074a6f7246ed94503041ac2ec3157ccee40e169083c5920fa4bd8` |
| `comparator.json` | 15 | 369 | `281b74997761bf918d5e70581a11c907ad77aa1f6dc98fec0742d98861c8243d` |

`Challenge.lean` imports only Mathlib and has exactly three deliberate target
placeholders. `Solution.lean` imports the original proof modules and has no
placeholder, custom axiom, unsafe declaration or native decision shortcut.
`definition_names` is empty. The permitted axioms are exactly `propext`,
`Quot.sound` and `Classical.choice`. No proof-limit increase or linter option
is introduced by this merge.

## Verification boundary

This report certifies the source-copy and packaging checks described above.
Lean builds, recursive Comparator checks and kernel validation are performed
centrally and recorded separately. The merge report itself makes no claim that
those subsequent checks passed.
