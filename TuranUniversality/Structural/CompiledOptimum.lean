module

public import TuranUniversality.Structural.BlockDefects
public import TuranUniversality.Structural.RecordApproximationSupremum

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The exact supremum of actual compiled models

The lower sequence consists of genuine finite legal records and ordinary
compiled hypergraphs. Each block root receives `3/(5r)`, each suspension root
`1/r`, and the data probability weights are scaled by `4/r`.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.Compiled

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

noncomputable def optimalWeights (b t : ℕ) (x : V → ℝ) : Vertex b t V → ℝ :=
  Sum.elim (fun _ => 1 / (OuterWeights.arity b t : ℝ))
    (Sum.elim (fun _ => 3 / (5 * (OuterWeights.arity b t : ℝ)))
      (fun v => (4 / (OuterWeights.arity b t : ℝ)) * x v))

theorem optimalWeights_probability (b t : ℕ) (x : V → ℝ) (hx : ProbabilityWeights x) :
    ProbabilityWeights (optimalWeights b t x) := by
  have hr : 0 < (OuterWeights.arity b t : ℝ) :=
    Nat.cast_pos.mpr (OuterWeights.arity_pos b t)
  refine ⟨?_, ?_⟩
  · intro v
    rcases v with i | (v | v)
    · exact div_nonneg (by norm_num) hr.le
    · exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hr.le)
    · exact mul_nonneg (div_nonneg (by norm_num) hr.le) (hx.1 v)
  · simp only [optimalWeights, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum, hx.2, mul_one]
    simp only [Support.Vertex, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    simp only [Nat.cast_id]
    have har : (OuterWeights.arity b t : ℝ) = t + (3 * b + 4) := by
      simp [OuterWeights.arity]
    field_simp [ne_of_gt hr]
    rw [har]
    ring

theorem optimalWeights_dataMass (b t : ℕ) (x : V → ℝ) (hx : ∑ v, x v = 1) :
    dataMass (optimalWeights b t x) = 4 / (OuterWeights.arity b t : ℝ) := by
  simp only [dataMass, dataWeight, optimalWeights, Sum.elim_inr, ← Finset.mul_sum, hx, mul_one]

theorem optimalWeights_blockMass (b t : ℕ) (x : V → ℝ) (i : Fin b) :
    blockMass (optimalWeights b t x) i = 3 / (OuterWeights.arity b t : ℝ) := by
  simp only [blockMass, Support.blockMass, rootWeight, optimalWeights, Sum.elim_inl,
    Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem averageRoots_optimalWeights (b t : ℕ) (x : V → ℝ) :
    averageRoots (optimalWeights b t x) = optimalWeights b t x := by
  funext v
  rcases v with i | (⟨i, j⟩ | v)
  · rfl
  · change blockMass (optimalWeights b t x) i / 5 = 3 / (5 * (OuterWeights.arity b t : ℝ))
    rw [optimalWeights_blockMass]
    ring
  · rfl

theorem normalizedData_optimalWeights (b t : ℕ) (x : V → ℝ) (hx : ∑ v, x v = 1) :
    normalizedData (optimalWeights b t x) = x := by
  have hr : (OuterWeights.arity b t : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  funext v
  rw [normalizedData, optimalWeights_dataMass b t x hx]
  change ((4 / (OuterWeights.arity b t : ℝ)) * x v) / (4 / (OuterWeights.arity b t : ℝ)) = x v
  exact mul_div_cancel_left₀ _ (div_ne_zero (by norm_num) hr)

theorem factor_optimalWeights (b t : ℕ) (x : V → ℝ) (hx : ProbabilityWeights x) :
    factor (optimalWeights b t x) = OuterWeights.chi b t := by
  have hw := optimalWeights_probability b t x hx
  apply (OuterWeights.massFactor_eq_iff _ _ _ (fun i => hw.1 _)
    (blockMass_nonneg _ hw.1) (dataMass_nonneg _ hw.1) (mass_sum _ hw)).mpr
  refine ⟨fun _ => rfl, optimalWeights_blockMass b t x, optimalWeights_dataMass b t x hx.2⟩

/-- Averaging all roots makes every support-word bound an equality. -/
theorem polynomial_averageRoots (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (p q : ℝ) (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : Vertex b t V → ℝ) (hT : 0 < dataMass x) :
    (graph t Ω R).edgePolynomial (averageRoots x) =
      factor x * R.score p q (normalizedData x) := by
  rw [polynomial]
  change (∏ i, suspensionWeight x i) * ∑ X ∈ R.recorded.edges,
    (Support.poolGraph (Ω (R.label X))).edgePolynomial (Support.average (rootWeight x)) *
      ∏ v ∈ X, dataWeight x v = _
  simp_rw [Support.poolGraph_average, hΩ]
  change (∏ i, suspensionWeight x i) * ∑ X ∈ R.recorded.edges,
    (Label.payoff p q (R.label X) *
      ((1 / 25 : ℝ) ^ b * ∏ i, blockMass x i ^ 3)) * ∏ v ∈ X, dataWeight x v = _
  have he : (∑ X ∈ R.recorded.edges,
      (Label.payoff p q (R.label X) *
        ((1 / 25 : ℝ) ^ b * ∏ i, blockMass x i ^ 3)) * ∏ v ∈ X, dataWeight x v) =
      ((1 / 25 : ℝ) ^ b * ∏ i, blockMass x i ^ 3) * R.score p q (dataWeight x) := by
    rw [RecordSystem.score, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    ring
  rw [he, data_score R p q x hT]
  unfold factor OuterWeights.massFactor
  ring

theorem optimalWeights_value (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (p q : ℝ) (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    (graph t Ω R).edgePolynomial (optimalWeights b t x) =
      OuterWeights.chi b t * R.score p q x := by
  have hT : 0 < dataMass (optimalWeights b t x) := by
    rw [optimalWeights_dataMass b t x hx.2]
    exact div_pos (by norm_num) (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  calc
    _ = (graph t Ω R).edgePolynomial (averageRoots (optimalWeights b t x)) := by
      rw [averageRoots_optimalWeights]
    _ = _ := by
      rw [polynomial_averageRoots Ω R p q hΩ _ hT, factor_optimalWeights b t x hx,
        normalizedData_optimalWeights b t x hx.2]

def weightedValues (F : Finset (FiniteGraph 3)) (b t : ℕ)
    (Ω : Label → Finset (Cube.Word b)) : Set ℝ :=
  {z | ∃ (V : Type) (d : DecidableEq V) (f : Fintype V),
    letI : DecidableEq V := d
    letI : Fintype V := f
    ∃ (R : RecordSystem V) (x : Vertex b t V → ℝ),
      R.LocallyLegal (homomorphicClosure F) ∧ ProbabilityWeights x ∧
        z = (graph t Ω R).edgePolynomial x}

theorem mem_weightedValues {V : Type} [DecidableEq V] [Fintype V]
    (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (hR : R.LocallyLegal (homomorphicClosure F))
    (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    (graph t Ω R).edgePolynomial x ∈ weightedValues F b t Ω :=
  ⟨V, inferInstance, inferInstance, R, x, hR, hx, rfl⟩

theorem weightedValues_upper (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) ∈
      upperBounds (weightedValues F b t Ω) := by
  rintro z ⟨V, d, f, R, x, hR, hx, rfl⟩
  letI : DecidableEq V := d
  letI : Fintype V := f
  exact polynomial_upper F hedges Ω R hR p q hp hpq hq hz hΩ x hx

theorem approximation_value_tendsto (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) (phase : Bool) :
    Tendsto (fun n => (graph t Ω (RecordApproximation.object F hedges phase n).records).edgePolynomial
      (optimalWeights b t (RecordApproximation.weights F p q n))) atTop
        (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) := by
  have h := (RecordApproximation.score_tendsto F hedges phase p q hp hpq hq hz).const_mul
    (OuterWeights.chi b t)
  simpa only [optimalWeights_value Ω _ p q hΩ _ (RecordApproximation.weights_probability F p q hz _),
    LegalObject.score] using h

theorem weightedValues_nonempty (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b)) :
    (weightedValues F b t Ω).Nonempty := by
  let O := RecordApproximation.object F hedges false 0
  let y := RecordApproximation.weights F 0 1 0
  have hy := RecordApproximation.weights_probability F 0 1
    (by simpa using familyTuranDensity_nonneg F) 0
  exact ⟨_, mem_weightedValues F Ω O.records O.records_locallyLegal
    (optimalWeights b t y) (optimalWeights_probability b t y hy)⟩

/-- The exact Lagrangian supremum of genuine finite compiled models. -/
theorem weightedValues_isLUB (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    IsLUB (weightedValues F b t Ω)
      (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)) := by
  refine ⟨weightedValues_upper F hedges Ω p q hp hpq hq hz hΩ, ?_⟩
  intro c hc
  apply le_of_tendsto (approximation_value_tendsto F hedges Ω p q hp hpq hq hz hΩ false)
  exact Eventually.of_forall fun n => hc (mem_weightedValues F Ω
    (RecordApproximation.object F hedges false n).records
    (RecordApproximation.object F hedges false n).records_locallyLegal
    (optimalWeights b t (RecordApproximation.weights F p q n))
    (optimalWeights_probability b t _ (RecordApproximation.weights_probability F p q hz n)))

theorem sSup_weightedValues (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    sSup (weightedValues F b t Ω) =
      OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) :=
  (weightedValues_isLUB F hedges Ω p q hp hpq hq hz hΩ).csSup_eq
    (weightedValues_nonempty F hedges Ω)

end TuranUniversality.Structural.Compiled
