module

public import TuranUniversality.Uniformity.Suspension
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-! # The exact mass factor in a suspension -/

open scoped BigOperators

namespace TuranUniversality

theorem product_le_card_inv_pow {I : Type*} [Fintype I] [Nonempty I]
    (z : I → ℝ) (hz : ∀ i, 0 ≤ z i) (hs : ∑ i, z i = 1) :
    (∏ i, z i) ≤ ((Fintype.card I : ℝ)⁻¹) ^ Fintype.card I := by
  have hn : 0 < Fintype.card I := Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : I => (1 : ℝ)) z
    (by intro i hi; norm_num) (by simpa using (Nat.cast_pos.mpr hn : (0 : ℝ) < Fintype.card I))
    (fun i _ => hz i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    one_mul, hs, one_div] at h
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hz i)) _) h (Fintype.card I)
  rwa [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hz i)) (Nat.ne_of_gt hn)] at hpow

theorem suspension_mass_bound {I : Type*} [Fintype I]
    (t : ℝ) (y : I → ℝ) (ht : 0 ≤ t) (hy : ∀ i, 0 ≤ y i)
    (hs : t + ∑ i, y i = 1) :
    t ^ 3 * (∏ i, y i) ≤ 27 / (Fintype.card I + 3 : ℝ) ^ (Fintype.card I + 3) := by
  let z : I ⊕ Fin 3 → ℝ := Sum.elim y (fun _ => t / 3)
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    cases i with
    | inl i => exact hy i
    | inr i => dsimp [z]; positivity
  have hsum : ∑ i, z i = 1 := by
    simp [z, Fintype.sum_sum_type]
    linarith
  have h := product_le_card_inv_pow z hz hsum
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat,
    Fintype.prod_sum_type, z, Sum.elim_inl, Sum.elim_inr, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h
  rw [inv_pow, ← one_div] at h
  calc
    t ^ 3 * (∏ i, y i) = 27 * ((∏ i, y i) * (t / 3) ^ 3) := by ring
    _ ≤ 27 * (1 / (Fintype.card I + 3 : ℝ) ^ (Fintype.card I + 3)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

namespace RGraph

theorem edgePolynomial_scale {V : Type*} [DecidableEq V] {r : ℕ}
    (G : RGraph V r) (x : V → ℝ) (c : ℝ) :
    G.edgePolynomial (fun v => c * x v) = c ^ r * G.edgePolynomial x := by
  unfold edgePolynomial
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [G.uniform e he]

/-- A bound on probability weights scales cubically with arbitrary mass. -/
theorem three_polynomial_bound_of_mass {V : Type*} [DecidableEq V] [Fintype V]
    (G : RGraph V 3) (b : ℝ)
    (hb : ∀ x, ProbabilityWeights x → G.edgePolynomial x ≤ b)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    G.edgePolynomial x ≤ (∑ v, x v) ^ 3 * b := by
  let t := ∑ v, x v
  have ht : 0 ≤ t := Finset.sum_nonneg (fun v _ => hx v)
  by_cases hzero : t = 0
  · have hxzero : ∀ v, x v = 0 := by
      intro v
      have hle : x v ≤ t := Finset.single_le_sum (fun w _ => hx w) (Finset.mem_univ v)
      exact le_antisymm (by simpa [hzero] using hle) (hx v)
    have hpoly : G.edgePolynomial x = 0 := by
      have heq : x = fun _ => 0 := funext hxzero
      rw [heq]
      rw [G.edgePolynomial_uniform]
      norm_num
    rw [hpoly]
    change 0 ≤ t ^ 3 * b
    simp [hzero]
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    let w := fun v => t⁻¹ * x v
    have hw : ProbabilityWeights w := by
      refine ⟨fun v => mul_nonneg (inv_nonneg.mpr ht) (hx v), ?_⟩
      dsimp [w]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hzero
    have heq : x = fun v => t * w v := by
      funext v
      dsimp [w]
      rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul]
    calc
      G.edgePolynomial x = t ^ 3 * G.edgePolynomial w := by
        rw [heq, G.edgePolynomial_scale]
      _ ≤ t ^ 3 * b := mul_le_mul_of_nonneg_left (hb w hw) (pow_nonneg ht _)

end RGraph

namespace RGraph

theorem suspension_polynomial_bound {V : Type*} [DecidableEq V] [Fintype V]
    (G : RGraph V 3) (s : ℕ) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ x, ProbabilityWeights x → G.edgePolynomial x ≤ b)
    (w : Fin s ⊕ V → ℝ) (hw : ProbabilityWeights w) :
    (G.suspension s).edgePolynomial w ≤ 27 / (s + 3 : ℝ) ^ (s + 3) * b := by
  let y : Fin s → ℝ := fun i => w (Sum.inl i)
  let x : V → ℝ := fun v => w (Sum.inr v)
  let t := ∑ v, x v
  have hy : ∀ i, 0 ≤ y i := fun i => hw.1 _
  have hx : ∀ v, 0 ≤ x v := fun v => hw.1 _
  have ht : 0 ≤ t := Finset.sum_nonneg (fun v _ => hx v)
  have hs : t + ∑ i, y i = 1 := by
    have h := hw.2
    rw [Fintype.sum_sum_type] at h
    dsimp [t, x, y]
    linarith
  have hm := suspension_mass_bound t y ht hy hs
  simp only [Fintype.card_fin] at hm
  have heq : w = Sum.elim y x := by funext v; cases v <;> rfl
  rw [heq, G.suspension_polynomial]
  calc
    (∏ i, y i) * G.edgePolynomial x ≤ (∏ i, y i) * (t ^ 3 * b) :=
      mul_le_mul_of_nonneg_left (G.three_polynomial_bound_of_mass b hb x hx)
        (Finset.prod_nonneg (fun i _ => hy i))
    _ = (t ^ 3 * (∏ i, y i)) * b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm hb0

noncomputable def suspensionWeights {V : Type*} (s : ℕ) (x : V → ℝ) : Fin s ⊕ V → ℝ :=
  Sum.elim (fun _ => (s + 3 : ℝ)⁻¹) (fun v => (3 / (s + 3 : ℝ)) * x v)

theorem suspensionWeights_probability {V : Type*} [Fintype V]
    (s : ℕ) (x : V → ℝ) (hx : ProbabilityWeights x) :
    ProbabilityWeights (suspensionWeights s x) := by
  have hr : (s + 3 : ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · intro v
    cases v with
    | inl i => dsimp [suspensionWeights]; positivity
    | inr v => exact mul_nonneg (by positivity) (hx.1 v)
  · simp only [suspensionWeights, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, hx.2, mul_one]
    field_simp
    <;> ring

theorem suspensionWeights_value {V : Type*} [DecidableEq V]
    (G : RGraph V 3) (s : ℕ) (x : V → ℝ) :
    (G.suspension s).edgePolynomial (suspensionWeights s x) =
      27 / (s + 3 : ℝ) ^ (s + 3) * G.edgePolynomial x := by
  rw [suspensionWeights, G.suspension_polynomial, G.edgePolynomial_scale]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_add, inv_pow]
  have hr : (s + 3 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

end RGraph
end TuranUniversality
