module

public import TuranUniversality.Structural.RecordComplete

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Repair changes the actual finite score by at most its disagreement

Both payoffs are zero on repeated samples. The comparison therefore applies
to the actual finite complete score, not only to its relaxed polynomial.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace RecordSystem

noncomputable def observedPayoff (R : RecordSystem V) (p q : ℝ) (f : Fin 4 → V) : ℝ :=
  truth (R.Successful f) * Label.payoff p q (R.label (Finset.univ.image f))

theorem observedPayoff_bounds (R : RecordSystem V) (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (f : Fin 4 → V) : 0 ≤ R.observedPayoff p q f ∧ R.observedPayoff p q f ≤ 161 * q := by
  have hq : 0 ≤ q := hp.trans hpq
  by_cases hf : R.Successful f
  · simp only [observedPayoff, hf, truth_true, one_mul]
    have h := Label.payoff_bounds p q hp hpq (R.label (Finset.univ.image f))
    constructor <;> linarith
  · simp only [observedPayoff, hf, truth_false, zero_mul]
    constructor <;> positivity

theorem payoff_mean (R : RecordSystem V) (p q : ℝ) (x : V → ℝ) :
    weightedMean x (R.observedPayoff p q) = 24 * R.score p q x := by
  have h := edge_value_mean R.recorded x (fun X => Label.payoff p q (R.label X))
  norm_num only [Nat.factorial] at h
  exact h

end RecordSystem

namespace LegalObject

variable {B : Finset (FiniteGraph 3)}

theorem payoffs_agree {R : RecordSystem V} (O : LegalObject B V) (p q : ℝ)
    (f : Fin 4 → V) (h : ¬ R.Disagreement O f) :
    O.records.observedPayoff p q f = R.observedPayoff p q f := by
  have h' : R.Successful f ∧ O.label (Finset.univ.image f) = R.label (Finset.univ.image f) := by
    simpa only [RecordSystem.Disagreement, not_or, not_not] using h
  have hO := (O.records_successful f).mpr h'.1.injective
  have hR : truth (R.Successful f) = 1 := by simp [truth, h'.1]
  have hC : truth (O.records.Successful f) = 1 := by simp [truth, hO]
  simp only [RecordSystem.observedPayoff, hR, hC, one_mul]
  change Label.payoff p q (O.label _) = Label.payoff p q (R.label _)
  rw [h'.2]

theorem payoff_difference_bounds {R : RecordSystem V} (O : LegalObject B V)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (f : Fin 4 → V) :
    (-161 * q) * truth (R.Disagreement O f) ≤
      O.records.observedPayoff p q f - R.observedPayoff p q f ∧
    O.records.observedPayoff p q f - R.observedPayoff p q f ≤
      (161 * q) * truth (R.Disagreement O f) := by
  by_cases hd : R.Disagreement O f
  · have hR := R.observedPayoff_bounds p q hp hpq f
    have hO := O.records.observedPayoff_bounds p q hp hpq f
    have ht : truth (R.Disagreement O f) = 1 := by simp [truth, hd]
    rw [ht, mul_one, mul_one]
    constructor <;> linarith
  · rw [O.payoffs_agree p q f hd]
    simp [truth, hd]

/-- The paper's payoff coupling estimate with the exact coefficient. -/
theorem score_distance_le {R : RecordSystem V} (O : LegalObject B V)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (x : V → ℝ) (hx : ProbabilityWeights x) :
    |O.score p q x - R.score p q x| ≤
      (161 * q / 24) * sampleProbability x (R.Disagreement O) := by
  have hl := weightedMean_mono x hx.1
    (fun f => (O.payoff_difference_bounds (R := R) p q hp hpq f).1)
  have hu := weightedMean_mono x hx.1
    (fun f => (O.payoff_difference_bounds (R := R) p q hp hpq f).2)
  rw [weightedMean_scale, weightedMean_sub, O.records.payoff_mean, R.payoff_mean] at hl
  rw [weightedMean_sub, O.records.payoff_mean, R.payoff_mean, weightedMean_scale] at hu
  change (-161 * q) * sampleProbability x (R.Disagreement O) ≤
    24 * O.score p q x - 24 * R.score p q x at hl
  change 24 * O.score p q x - 24 * R.score p q x ≤
    (161 * q) * sampleProbability x (R.Disagreement O) at hu
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu]

theorem repaired_score_distance_le {R : RecordSystem V} (O : LegalObject B V)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (x : V → ℝ) (hx : ProbabilityWeights x)
    (hd : sampleProbability x (R.Disagreement O) ≤ 5 * R.erasure x) :
    |O.score p q x - R.score p q x| ≤ (805 * q / 24) * R.erasure x := by
  have h := O.score_distance_le (R := R) p q hp hpq x hx
  have hmul := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 161 * q / 24 by have hq := hp.trans hpq; positivity)
  nlinarith only [h, hmul]

end LegalObject
end TuranUniversality.Structural
