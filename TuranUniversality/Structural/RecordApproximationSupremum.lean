module

public import TuranUniversality.Structural.RecordApproximation

@[expose] public section

/-! # The supremum of actual complete legal record scores

The set below ranges over genuine finite vertex types, complete legal
objects and probability weights. It does not define the optimum by the
scalar formula. The upper bound and the constructed finite sequence show
that its supremum is the paper's `S(z)`.
-/

open Filter Topology

namespace TuranUniversality.Structural.RecordApproximation

def completeScoreValues (F : Finset (FiniteGraph 3)) (p q : ℝ) : Set ℝ :=
  {s | ∃ (V : Type) (d : DecidableEq V) (f : Fintype V),
    letI : DecidableEq V := d
    letI : Fintype V := f
    ∃ (O : LegalObject (homomorphicClosure F) V) (x : V → ℝ),
      ProbabilityWeights x ∧ s = O.score p q x}

theorem score_mem_completeScoreValues {V : Type} [DecidableEq V] [Fintype V]
    (F : Finset (FiniteGraph 3)) (p q : ℝ)
    (O : LegalObject (homomorphicClosure F) V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    O.score p q x ∈ completeScoreValues F p q :=
  ⟨V, inferInstance, inferInstance, O, x, hx, rfl⟩

theorem completeScoreValues_upper (F : Finset (FiniteGraph 3)) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F) :
    SwitchScalar.phaseScore p q (familyTuranDensity F) ∈ upperBounds (completeScoreValues F p q) := by
  rintro s ⟨V, d, f, O, x, hx, rfl⟩
  letI : DecidableEq V := d
  letI : Fintype V := f
  exact O.score_le_phaseScore F p q hp hpq hq hz x hx

theorem completeScoreValues_nonempty (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (p q : ℝ)
    (hz : p / q ≤ familyTuranDensity F) : (completeScoreValues F p q).Nonempty :=
  ⟨_, score_mem_completeScoreValues F p q (object F hedges false 0)
    (weights F p q 0) (weights_probability F p q hz 0)⟩

theorem phaseScore_isLUB (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F) :
    IsLUB (completeScoreValues F p q) (SwitchScalar.phaseScore p q (familyTuranDensity F)) := by
  refine ⟨completeScoreValues_upper F p q hp hpq hq hz, ?_⟩
  intro c hc
  apply le_of_tendsto (score_tendsto F hedges false p q hp hpq hq hz)
  exact Eventually.of_forall fun n => hc
    (score_mem_completeScoreValues F p q (object F hedges false n)
      (weights F p q n) (weights_probability F p q hz n))

theorem sSup_completeScoreValues (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F) :
    sSup (completeScoreValues F p q) = SwitchScalar.phaseScore p q (familyTuranDensity F) :=
  (phaseScore_isLUB F hedges p q hp hpq hq hz).csSup_eq
    (completeScoreValues_nonempty F hedges p q hz)

end TuranUniversality.Structural.RecordApproximation
