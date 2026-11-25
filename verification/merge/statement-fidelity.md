# Statement fidelity and scope: Theorems 1.1–1.3

## Scope and review status

This package, **Turing Universality in Hypergraph Turán Theory**, combines the
three mathematical endpoints for Theorems 1.1, 1.2, and 1.3 of the supplied V4
manuscript by Heng Li and Xizhi Liu, *Turing universality, computability, and
incompleteness in hypergraph Turán theory*. The formalization author and
responsible maintainer are **Xizhi Liu**.

This document records a separate assistant-performed source and mathematical
correspondence review. It is not a new kernel check, an independent human
review, or evidence of acceptance by Palomar. Current build, declaration
comparison, axiom, and kernel results belong in the package's verification
records; historical checks of the three separate entries do not by themselves
verify the merged entry.

The review read the manuscript's three numbered statements, their surrounding
definitions, the three original independent Challenges and Solutions, the
three public statement modules, and the concrete proof assembly and parameter
definitions. The manuscript reviewed has SHA-256:

```text
854323258588a104d997afa6026460565c5fdcbe76f56e65c605b9dd5592ea61
```

No missing mathematical clause of these three numbered statements was
identified, **subject to the explicit machine, encoding, and witness
qualifications below**. The appropriate claim is a formalization of their
existence and effectiveness assertions for the project's precisely defined
universal binary-input evaluator and verified graph constructions. This is
not a claim that every machine instruction, intermediate numerical constant,
or labeled output graph in the paper has been reproduced literally.

## The three targets

| Manuscript result | Exported declaration in `TuranUniversality.Registry` | Scope retained by the formal statement |
| --- | --- | --- |
| Theorem 1.1 | `main_theorem` | One fixed rational threshold in `(0,1)` with the baseline formula; a primitive-recursive compiler from literal finite binary words to one ordinary simple 3-graph; an edge in each output; convergence of ordinary normalized extremal numbers; both equality/nonhalting and strict-inequality/halting equivalences. |
| Theorem 1.2 | `numerical_main_theorem` | All ranks `r ≥ 3`; finite forbidden families; the original singleton endpoint at rank three; exact density scaling; threshold bounds; one input-independent finite template for each rank; attainment by uniform weights and the upper bound for every real probability weighting; hom-freeness and ordinary freeness of every finite blowup; effective family and template codes. |
| Theorem 1.3 | `structural_main_theorem` | One fixed rank threshold; a jointly primitive-recursive family compiler; an input-independent finite profile and two fixed ordinary separator tests for each rank; singleton extremal-profile space and original-vertex edge-edit stability in the nonhalting case; two nonempty compact disjoint phases, each homeomorphic to the entire inner extremal space, in the halting case. |

The proof assemblies are respectively
`Reduction/Universality.lean`, `Reduction/NumericalUniversality.lean`, and
`Structural/Main.lean`.

## Mathematical definitions

### Ordinary hypergraphs, containment, and density

`RGraph V r` is a finite set of finite subsets of `V`, with every edge having
cardinality `r`. Edges have no order or repetitions. `IsEmbedding` requires a
globally injective vertex map and preservation of every edge; it does not
require preservation of nonedges. All vertices, including isolated vertices,
are retained by this ordinary-subgraph notion.

`extremalNumber` and `familyExtremalNumber` maximize the actual edge count of
ordinary free graphs on `Fin n`, bounded by `n.choose r`. Their normalized
versions divide by that binomial coefficient. The density definitions use
the infimum over `n + r`; Theorems 1.1 and 1.2 explicitly assert convergence of
the normalized extremal sequence to the density used in the dichotomy.
Thus the exported numerical result concerns ordinary Turán density. A
Lagrangian upper or lower bound is used inside the proof, rather than silently
substituted for that density.

Graph codes carry a vertex count together with a finite list of potential
edges. Decoding discards invalid entries, forgets repetitions, and yields an
actual finite simple graph. A compiler produces one code for Theorem 1.1 and
a finite list of codes for Theorems 1.2 and 1.3. Those lists decode as finite
sets of forbidden graphs.

### Actual halting semantics

The formal input is `List Bool`. The leading bit enables program execution;
the tail is decoded to a Mathlib `Nat.Partrec.Code` and run on input zero.
An input without an enabled leading bit diverges. `WordHalts` is the domain
of this explicitly defined partial evaluator, not an uninterpreted predicate.
`Computation/Program.lean` proves the primitive-recursive encoding of standard
programs, the halting equivalence for that encoding, and that `[false]` does
not halt.

`Computation/Interpreter.lean` obtains a fixed finite interpreter from
Mathlib's proved compilation of partial-recursive functions. Its correctness
field connects the actual tape-machine run and `WordHalts` in both directions.
The implementation uses a two-sided tape representation, whereas the paper
describes a one-sided two-track machine. The reviewed endpoints specify the
halting domain of the project's evaluator. They do not contain a formal
identification of its literal machine states or step counts with a particular
manuscript machine. If the desired claim is about that literal machine on
identically encoded words, a machine-equivalence identification would be an
additional statement.

This qualification does not remove the actual universal halting content:
standard program halting is explicitly reduced to the fixed evaluator. No
arbitrary undecidable predicate is assumed.

### Constants, effectiveness, and the witnesses

Theorems 1.1 and 1.2 include

```lean
∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧
  τ = Weighted.rationalThreshold (m : ℚ)
```

`rationalThreshold` gives the explicit rational expression `6 B_*`. The
proof uses `tau3`, with a fixed physical-type count
`m = 4 * (10^16 + A) + 30`, where `A` is the alphabet size of the chosen
interpreter's local representation. The root-count polynomial and all
required bounds are proved in the source. The formalization changes the
root-code implementation and some sufficiently-large construction constants;
it does not claim that those auxiliary constants are the paper's literal
values.

The universal interpreter is selected with `Classical.choice`, and several
concrete compiler and threshold definitions are consequently marked
`noncomputable`. This is compatible with the separately proved `Primrec`
certificates: the endpoints assert the existence of functions satisfying that
specific computability property. The package does not claim to have extracted
a runnable compiler, printed a fully evaluated numerical threshold, or
measured practical output sizes.

The rank threshold for Theorem 1.3 is a fixed natural-number witness `R ≥ 4`.
In the proof it is `3 * blockCount + 4`, with `blockCount` determined by the
denominator of the same `tau3`. The structural compiler has a proof of
`Primrec₂`, not merely a separate existence proof for each rank. The numerical
family compiler is likewise jointly primitive recursive in rank and input,
and its template-code function is primitive recursive in rank. These exceed
the numbered statements' uniform computability requirements.

Each of the three exported theorem types has its own existential witnesses.
The proof assemblies actually instantiate them using the same `tau3` and
`forbiddenCompiler`. The three-target submission preserves those established
types; it does not add a fourth statement saying that arbitrary existential
witnesses selected independently from the three results are equal.

## Theorem 1.2 clause checks

The scaling is exactly

\[
  \frac{27r!}{6r^r},
\]

implemented in rational arithmetic by `Uniformity.densityScale`. The
rank-three equality identifies the decoded forbidden family with the
singleton of the same `single` compiler that appears in the density-scaling
clause. The fixed template is chosen as a function of rank before the input
word is quantified.

The statement requires a positive number of template vertices, gives the
exact normalized edge-polynomial value at uniform weights, and bounds that
value for **every real probability weighting**. It separately asserts
`familyHomFree` and ordinary freeness for every natural-number vector of
blowup class sizes, including zero-sized classes. These clauses express both
global optimality and the all-input fixed-construction lower bound.

## Theorem 1.3 clause checks

Profiles are functions from numbered finite test graphs to their real
homomorphism densities. Limit profiles are the closure of profiles of
nonempty finite graphs in the product topology. Duplicate isomorphic test
graphs are harmless coordinates; this realizes the paper's ordinary
homomorphism-density description. Forbidden freeness at the profile level is
vanishing of each forbidden homomorphism density, and extremality requires
the one-edge density to equal ordinary family Turán density.

The finite profile uses a finite set of **multisets** of roles. Repeated roles
on an edge are permitted, as in the manuscript definition; the profile is not
restricted to the blowup of a simple graph on distinct roles. The role count,
pattern, weights, exact rounding counts, and both separator test graphs are
chosen after the rank and before the input word. They are therefore independent
of the word.

`BalancedCounts` requires each class size to be the floor or ceiling of its
prescribed mass, with exact total equal to the original number of vertices.
`StableWithPattern` quantifies over every ordinary free sequence whose orders
tend to infinity and whose one-edge homomorphism density tends to the Turán
density. It supplies assignments on the **original vertex sets**, with those
exact class counts, and symmetric-difference edge count divided by `n^r`
tending to zero. This is the stated `o(n^r)` edge-edit conclusion.
One-edge homomorphism density is `r! e(G)/n^r`, which is asymptotically the
binomial-normalized edge density as `n` tends to infinity.

In the halting alternative, `TwoPhases` requires the full extremal space to
equal the disjoint union of two nonempty compact sets. The separator is exactly
constant on each, with values `c` and `-c` for one `c > 0`. Each phase is
homeomorphic to the **entire** inner extremal space; the whole outer space is
also asserted homeomorphic to its product with `Bool`. No phase has been
replaced by a single representative limit.

## Source dependency closure

`source-closure.json` is an import closure computed from the three proof
assembly modules. Comments were removed before parsing imports. Every imported
module having a source file in the original project was recursively included;
external Mathlib/Lean modules are listed separately. Each project file has its
relative path, original SHA-256, byte and line count, and direct imports.

| Root | Number of project modules in its closure |
| --- | ---: |
| `TuranUniversality.Reduction.Universality` | 180 |
| `TuranUniversality.Reduction.NumericalUniversality` | 211 |
| `TuranUniversality.Structural.Main` | 407 |
| Union | **419** |

The union contains **53,062 source lines and 2,368,907 bytes**. Original
Solution wrappers are hash-recorded but are not members of the copied closure;
the new merged Solution imports the three roots. The closure contains no
Palomar Challenge module. It also does not include the separate logical
independence or transcendence entry points.

## Explicit exclusions

The package does not claim Theorem 1.4, internalization of the density
equivalence in ZFC, any completed logical-independence proof, Section 11's
spectrum or transcendence statements, or the whole paper. The quantitative
certificate bounds, machine-time comparisons, and Busy-Beaver statements of
the separate later results are not targets of this submission.

The halting-case finite approximation paragraph immediately following
Theorem 1.3 is not an additional clause of `structural_main_theorem`. Some
supporting modules prove further finite approximation results, but the public
three-target scope should be described by the targets above.

## Independent source review of the merge

The combined Challenge, Solution, and comparator configuration were reviewed
after the merge writer completed them. A separate source-reading pass and
byte comparisons confirmed the following:

- The declarations of all three target theorems are unchanged from their
  respective original Challenges. All three Solution theorem declarations and
  proof bodies are likewise unchanged from their respective original Solutions.
- All **35** shared declarations retain the canonical Challenge12 text. The
  other originals contain identical text, except that Challenge13 writes the
  `uniform` proof fields of `Effective.decodeGraph` and
  `Effective.Uniform.decode` with equation-style syntax. Their edge sets and
  uniformity propositions are the same. Kernel/elaborated comparison, rather
  than this textual observation, decides the required declaration equality.
- All **10** source-derived Challenge segments match their recorded originals
  exactly. The three new segments contain the merged title and explanatory
  prose, notation scopes, or a blank separator. In particular the complete
  structural statement, stability definition, and phase definition were copied
  unchanged rather than reconstructed from a short summary.
- The merged Challenge imports exactly 12 Mathlib modules and no project proof
  module. It has exactly the three deliberate target `sorry` placeholders.
  The merged Solution imports exactly the three proof roots listed above and
  contains no `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, or `unsafe`
  token outside comments. Neither new wrapper introduces any `set_option`.
- `comparator.json` lists exactly the three exported theorem names, has an
  empty `definition_names` list, and permits only `propext`, `Quot.sound`, and
  `Classical.choice`.

These independently checked source hashes identify this review:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `1a3a6f603600e00bad39e17d635638e10601dd7d316f16af5d7e64178ea121f1` |
| `Solution.lean` | `11eba52fd9b074a6f7246ed94503041ac2ec3157ccee40e169083c5920fa4bd8` |
| `comparator.json` | `281b74997761bf918d5e70581a11c907ad77aa1f6dc98fec0742d98861c8243d` |

No Lean build or kernel replay was run as part of this source-review task.
The merged package's actual mechanical checks must be read separately from
the current verification results. In particular a source match does not
stand in for the recursive comparison of elaborated dependencies.
