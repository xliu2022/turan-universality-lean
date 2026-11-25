module

public import TuranUniversality.Effective.GraphEncoding
public import TuranUniversality.Computation.Program
public import TuranUniversality.Density.Extremal
public import TuranUniversality.Weighted.Baseline

/-! # The proof-side copy of the independently audited registry statement

The same definition appears in `Challenge.lean`, where all of its mathematical
dependencies are defined independently from Mathlib.  This module belongs to
the proof development and does not import the Challenge.
-/

@[expose] public section

open Filter Topology

namespace TuranUniversality.Registry

/-- Theorem 1.1: one fixed rational threshold and one primitive-recursive
compiler reduce this fixed universal binary halting problem to ordinary
Turán-density equality and strict inequality for single finite three-graphs.
There are no assumed extremal, semantic, or compiler-correctness hypotheses. -/
def mainStatement : Prop :=
  ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
    (∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧ τ = Weighted.rationalThreshold (m : ℚ)) ∧
    ∃ compiler : List Bool → Effective.GraphCode, Primrec compiler ∧
      ∀ w : List Bool,
        1 ≤ (Effective.decodeGraph (compiler w)).edges.card ∧
        Tendsto (extremalDensity (Effective.decodeGraph (compiler w))) atTop
          (𝓝 (turanDensity (Effective.decodeGraph (compiler w)))) ∧
        (turanDensity (Effective.decodeGraph (compiler w)) = (τ : ℝ) ↔
          ¬ Computation.WordHalts w) ∧
        ((τ : ℝ) < turanDensity (Effective.decodeGraph (compiler w)) ↔
          Computation.WordHalts w)

end TuranUniversality.Registry
