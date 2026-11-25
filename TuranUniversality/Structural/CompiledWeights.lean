module

public import TuranUniversality.Structural.Compiled
public import TuranUniversality.Structural.CodePools
public import TuranUniversality.Structural.OuterWeights
public import TuranUniversality.Structural.RecordScores

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The actual compiled graph satisfies the global defect inequality

All pool sizes below are literal finite cardinalities.  The final specialization
uses the constructed pools, and the data weights are normalized only when their
total mass is positive; the zero-mass case is proved directly from the edges.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

namespace RecordSystem

theorem score_scale {V : Type*} [DecidableEq V] [Fintype V]
    (R : RecordSystem V) (p q : ℝ) (x : V → ℝ) (c : ℝ) :
    R.score p q (fun v => c * x v) = c ^ 4 * R.score p q x := by
  unfold score
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X hX
  rw [R.recorded.uniform X hX]
  ring

theorem score_zero {V : Type*} [DecidableEq V] [Fintype V]
    (R : RecordSystem V) (p q : ℝ) : R.score p q (fun _ => 0) = 0 := by
  simpa using R.score_scale p q (fun _ => 0) 0

end RecordSystem

namespace SwitchScalar

theorem phaseScore_pos (p q z : ℝ) (hq : 0 < q) (hz : p / q ≤ z) :
    0 < phaseScore p q z := by
  have hd : 0 ≤ z - p / q := sub_nonneg.mpr hz
  unfold phaseScore gain
  positivity

end SwitchScalar

namespace Compiled

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def suspensionWeight (x : Vertex b t V → ℝ) (i : Fin t) : ℝ := x (.inl i)
def rootWeight (x : Vertex b t V → ℝ) (v : Support.Vertex b) : ℝ := x (.inr (.inl v))
def dataWeight (x : Vertex b t V → ℝ) (v : V) : ℝ := x (.inr (.inr v))
def blockMass (x : Vertex b t V → ℝ) (i : Fin b) : ℝ := Support.blockMass (rootWeight x) i
def dataMass (x : Vertex b t V → ℝ) : ℝ := ∑ v, dataWeight x v

noncomputable def normalizedData (x : Vertex b t V → ℝ) (v : V) : ℝ :=
  dataWeight x v / dataMass x

noncomputable def factor (x : Vertex b t V → ℝ) : ℝ :=
  OuterWeights.massFactor (suspensionWeight x) (blockMass x) (dataMass x)

theorem dataMass_nonneg (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) : 0 ≤ dataMass x :=
  Finset.sum_nonneg (fun v _ => hx _)

theorem blockMass_nonneg (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) (i : Fin b) :
    0 ≤ blockMass x i := by
  change 0 ≤ ∑ j : Fin 5, x (.inr (.inl ⟨i, j⟩))
  exact Finset.sum_nonneg (fun j _ => hx _)

theorem mass_sum (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    (∑ j, suspensionWeight x j) + (∑ i, blockMass x i) + dataMass x = 1 := by
  have h := hx.2
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma] at h
  simpa only [suspensionWeight, blockMass, Support.blockMass, rootWeight,
    dataMass, dataWeight, add_assoc] using h

theorem normalizedData_probability (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hT : 0 < dataMass x) : ProbabilityWeights (normalizedData x) := by
  refine ⟨fun v => div_nonneg (hx _) hT.le, ?_⟩
  simp only [normalizedData, ← Finset.sum_div]
  exact div_self (ne_of_gt hT)

theorem factor_nonneg (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) : 0 ≤ factor x :=
  OuterWeights.massFactor_nonneg _ _ _ (fun i => hx _) (blockMass_nonneg x hx)
    (dataMass_nonneg x hx)

theorem factor_le (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    factor x ≤ OuterWeights.chi b t :=
  OuterWeights.massFactor_le _ _ _ (fun i => hx.1 _) (blockMass_nonneg x hx.1)
    (dataMass_nonneg x hx.1) (mass_sum x hx)

theorem data_score (R : RecordSystem V) (p q : ℝ) (x : Vertex b t V → ℝ)
    (hT : 0 < dataMass x) :
    R.score p q (dataWeight x) = dataMass x ^ 4 * R.score p q (normalizedData x) := by
  have he : dataWeight x = fun v => dataMass x * normalizedData x v := by
    funext v
    simp [normalizedData, ne_of_gt hT, mul_div_cancel₀]
  rw [he, R.score_scale]

/-- The exact finite record score is the remaining data factor. -/
theorem polynomial_le_factor_score (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (p q : ℝ) (hΩ : ∀ l, ((Ω l).card : ℝ) = Label.payoff p q l)
    (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) (hT : 0 < dataMass x) :
    (graph t Ω R).edgePolynomial x ≤ factor x * R.score p q (normalizedData x) := by
  have h := polynomial_le Ω R x hx
  simp_rw [hΩ] at h
  change (graph t Ω R).edgePolynomial x ≤
    (∏ i, suspensionWeight x i) *
      ((1 / 25 : ℝ) ^ b * ∏ i, blockMass x i ^ 3) * R.score p q (dataWeight x) at h
  rw [data_score R p q x hT] at h
  unfold factor OuterWeights.massFactor
  nlinarith only [h]

theorem polynomial_eq_zero_of_dataMass (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hT : dataMass x = 0) : (graph t Ω R).edgePolynomial x = 0 := by
  have hz (v : V) : dataWeight x v = 0 := by
    have hle : dataWeight x v ≤ dataMass x :=
      Finset.single_le_sum (fun w _ => show 0 ≤ dataWeight x w from hx _) (Finset.mem_univ v)
    rw [hT] at hle
    exact le_antisymm hle (hx _)
  rw [polynomial]
  have hsum : (∑ X ∈ R.recorded.edges,
      (Support.poolGraph (Ω (R.label X))).edgePolynomial (rootWeight x) *
        ∏ v ∈ X, dataWeight x v) = 0 := by
    apply Finset.sum_eq_zero
    intro X hX
    have hc := R.recorded.uniform X hX
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
    rw [Finset.prod_eq_zero hv (hz v), mul_zero]
  change (∏ i, suspensionWeight x i) * (∑ X ∈ R.recorded.edges,
    (Support.poolGraph (Ω (R.label X))).edgePolynomial (rootWeight x) *
      ∏ v ∈ X, dataWeight x v) = 0
  rw [hsum, mul_zero]

theorem factor_eq_zero_of_dataMass (x : Vertex b t V → ℝ) (hT : dataMass x = 0) :
    factor x = 0 := by simp [factor, OuterWeights.massFactor, hT]

theorem normalizedData_eq_zero (x : Vertex b t V → ℝ) (hT : dataMass x = 0) :
    normalizedData x = fun _ => 0 := by
  funext v
  simp [normalizedData, hT]

theorem normalized_erasure_nonneg (R : RecordSystem V) (x : Vertex b t V → ℝ)
    (hx : ∀ v, 0 ≤ x v) : 0 ≤ R.erasure (normalizedData x) := by
  by_cases hT : dataMass x = 0
  · rw [normalizedData_eq_zero x hT]
    simp [RecordSystem.erasure, RGraph.edgePolynomial_uniform]
  · exact R.erasure_nonneg _ (normalizedData_probability x hx
      (lt_of_le_of_ne (dataMass_nonneg x hx) (Ne.symm hT)))

theorem polynomial_le_factor_score_all (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (p q : ℝ) (hΩ : ∀ l, ((Ω l).card : ℝ) = Label.payoff p q l)
    (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    (graph t Ω R).edgePolynomial x ≤ factor x * R.score p q (normalizedData x) := by
  by_cases hT : dataMass x = 0
  · rw [polynomial_eq_zero_of_dataMass Ω R x hx hT, factor_eq_zero_of_dataMass x hT,
      zero_mul]
  · exact polynomial_le_factor_score Ω R p q hΩ x hx
      (lt_of_le_of_ne (dataMass_nonneg x hx) (Ne.symm hT))

/-- Equation `defectglobal`, for actual compiled graphs and literal pool sizes. -/
theorem defect_global (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (hlocal : R.LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ l, ((Ω l).card : ℝ) = Label.payoff p q l)
    (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) (hT : 0 < dataMass x) :
    (graph t Ω R).edgePolynomial x ≤ factor x *
      (SwitchScalar.phaseScore p q (familyTuranDensity F) -
        (160 * q / 48) * R.erasure (normalizedData x)) := by
  exact (polynomial_le_factor_score Ω R p q hΩ x hx.1 hT).trans
    (mul_le_mul_of_nonneg_left
      (RecordSystem.score_le_penalty F hedges hlocal p q hp hpq hq hz (normalizedData x)
        (normalizedData_probability x hx.1 hT)) (factor_nonneg x hx.1))

/-- The zero-data branch is proved from the actual edges, so the quantitative
inequality applies uniformly to every probability weighting. -/
theorem defect_global_all (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (hlocal : R.LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ l, ((Ω l).card : ℝ) = Label.payoff p q l)
    (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    (graph t Ω R).edgePolynomial x ≤ factor x *
      (SwitchScalar.phaseScore p q (familyTuranDensity F) -
        (160 * q / 48) * R.erasure (normalizedData x)) := by
  by_cases hT : dataMass x = 0
  · rw [polynomial_eq_zero_of_dataMass Ω R x hx.1 hT,
      factor_eq_zero_of_dataMass x hT, zero_mul]
  · exact defect_global F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx
      (lt_of_le_of_ne (dataMass_nonneg x hx.1) (Ne.symm hT))

theorem normalized_score_le (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (R : RecordSystem V)
    (hlocal : R.LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    R.score p q (normalizedData x) ≤ SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  by_cases hT : dataMass x = 0
  · rw [normalizedData_eq_zero x hT, R.score_zero]
    exact (SwitchScalar.phaseScore_pos p q _ hq hz).le
  · have hx' := normalizedData_probability x hx
      (lt_of_le_of_ne (dataMass_nonneg x hx) (Ne.symm hT))
    have hp' := RecordSystem.score_le_penalty F hedges hlocal p q hp hpq hq hz _ hx'
    have he := R.erasure_nonneg _ hx'
    have hqe := mul_nonneg (show 0 ≤ 160 * q / 48 by positivity) he
    linarith

theorem polynomial_upper (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (hlocal : R.LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ l, ((Ω l).card : ℝ) = Label.payoff p q l)
    (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    (graph t Ω R).edgePolynomial x ≤
      OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  have hS := SwitchScalar.phaseScore_pos p q (familyTuranDensity F) hq hz
  by_cases hT : dataMass x = 0
  · rw [polynomial_eq_zero_of_dataMass Ω R x hx.1 hT]
    exact mul_nonneg (OuterWeights.chi_pos b t).le hS.le
  · have hTp : 0 < dataMass x := lt_of_le_of_ne (dataMass_nonneg x hx.1) (Ne.symm hT)
    have h := defect_global F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hTp
    have he := R.erasure_nonneg (normalizedData x) (normalizedData_probability x hx.1 hTp)
    have hpen := mul_nonneg (factor_nonneg x hx.1)
      (mul_nonneg (show 0 ≤ 160 * q / 48 by positivity) he)
    have hK := mul_le_mul_of_nonneg_right (factor_le x hx) hS.le
    nlinarith only [h, hpen, hK]

/-- Specialization to the actually constructed seven word pools. -/
theorem codePool_upper (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (R : RecordSystem V)
    (hlocal : R.LocallyLegal (homomorphicClosure F))
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    (x : Vertex (CodePools.blockCount q) t V → ℝ) (hx : ProbabilityWeights x) :
    (graph t (CodePools.pool p q hpq) R).edgePolynomial x ≤
      OuterWeights.chi (CodePools.blockCount q) t *
        SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  exact polynomial_upper F hedges _ R hlocal p q (Nat.cast_nonneg _)
    (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) x hx

end Compiled
end TuranUniversality.Structural
