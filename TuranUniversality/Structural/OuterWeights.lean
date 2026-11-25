module

public import TuranUniversality.Uniformity.MassOptimization
public import TuranUniversality.Structural.CompactOptimization
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

/-! # The outer mass factor and its unique AM--GM maximizer

The four data slots, three slots per code block, and all suspension slots
are actual finite coordinates. Their equality conditions give precisely the
root-block, suspension and total-data masses in the structural theorem.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural

theorem product_eq_card_inv_pow_iff {J : Type*} [Fintype J] [Nonempty J]
    (z : J → ℝ) (hz : ∀ j, 0 ≤ z j) (hs : ∑ j, z j = 1) :
    (∏ j, z j) = ((Fintype.card J : ℝ)⁻¹) ^ Fintype.card J ↔
      ∀ j, z j = (Fintype.card J : ℝ)⁻¹ := by
  classical
  have hn : 0 < Fintype.card J := Fintype.card_pos
  have hnr : 0 < (Fintype.card J : ℝ) := Nat.cast_pos.mpr hn
  have hw : ∑ _j : J, (Fintype.card J : ℝ)⁻¹ = 1 := by
    simp [ne_of_gt hnr]
  have hav : (∑ j : J, (Fintype.card J : ℝ)⁻¹ * z j) = (Fintype.card J : ℝ)⁻¹ := by
    rw [← Finset.mul_sum, hs, mul_one]
  constructor
  · intro he
    have heq : (∏ j : J, z j ^ ((Fintype.card J : ℝ)⁻¹)) =
        ∑ j : J, (Fintype.card J : ℝ)⁻¹ * z j := by
      rw [Real.finsetProd_rpow Finset.univ z (fun j _ => hz j), he, hav]
      exact Real.pow_rpow_inv_natCast (inv_nonneg.mpr hnr.le) (ne_of_gt hn)
    have h := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ
      (fun _ : J => (Fintype.card J : ℝ)⁻¹) z (fun _ _ => inv_pos.mpr hnr) hw
      (fun j _ => hz j)).mp heq
    intro j
    simpa only [hav] using h j (Finset.mem_univ j)
  · intro he
    simp only [he, Finset.prod_const, Finset.card_univ]

/-- Arbitrarily close AM--GM values force every coordinate to its unique
uniform limit. No unproved stability principle is used. -/
theorem probability_product_tendsto {J I : Type*} [Fintype J] [Nonempty J]
    {l : Filter I} (z : I → J → ℝ) (hz : ∀ i, ProbabilityWeights (z i))
    (hp : Tendsto (fun i => ∏ j, z i j) l
      (𝓝 (((Fintype.card J : ℝ)⁻¹) ^ Fintype.card J))) :
    Tendsto z l (𝓝 (fun _ : J => (Fintype.card J : ℝ)⁻¹)) := by
  apply tendsto_of_unique_value_on_compact (isCompact_stdSimplex ℝ J)
    (fun w : J → ℝ => ∏ j, w j) (by fun_prop)
    (fun _ => (Fintype.card J : ℝ)⁻¹)
    (((Fintype.card J : ℝ)⁻¹) ^ Fintype.card J) ?_ z
    (Eventually.of_forall hz) hp
  intro w hw he
  exact funext ((product_eq_card_inv_pow_iff w hw.1 hw.2).mp he)

namespace OuterWeights

abbrev Slot (b t : ℕ) := Fin t ⊕ ((Fin b × Fin 3) ⊕ Fin 4)

def arity (b t : ℕ) := t + (3 * b + 4)

instance (b t : ℕ) : Nonempty (Slot b t) := ⟨.inr (.inr 0)⟩

@[simp] theorem slot_card (b t : ℕ) : Fintype.card (Slot b t) = arity b t := by
  simp [Slot, arity, Nat.mul_comm]

theorem arity_pos (b t : ℕ) : 0 < arity b t := by unfold arity; omega

noncomputable def massVector {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ) :
    Slot b t → ℝ := Sum.elim y (Sum.elim (fun ij => s ij.1 / 3) (fun _ => T / 4))

theorem massVector_sum {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ) :
    (∑ j, massVector y s T j) = (∑ j, y j) + (∑ i, s i) + T := by
  simp only [massVector, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]
  have h (i : Fin b) : (3 : ℝ) * (s i / 3) = s i := by ring
  simp only [h]
  ring

theorem massVector_probability {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ)
    (hy : ∀ j, 0 ≤ y j) (hs : ∀ i, 0 ≤ s i) (hT : 0 ≤ T)
    (htotal : (∑ j, y j) + (∑ i, s i) + T = 1) :
    ProbabilityWeights (massVector y s T) := by
  refine ⟨?_, (massVector_sum y s T).trans htotal⟩
  intro v
  rcases v with j | (⟨i, k⟩ | k)
  · exact hy j
  · exact div_nonneg (hs i) (by norm_num)
  · exact div_nonneg hT (by norm_num)

noncomputable def massFactor {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ) : ℝ :=
  (1 / 25 : ℝ) ^ b * T ^ 4 * (∏ i, s i ^ 3) * ∏ j, y j

noncomputable def scale (b : ℕ) : ℝ := 3 ^ (3 * b) * 4 ^ 4 / 25 ^ b

noncomputable def chi (b t : ℕ) : ℝ := scale b * ((arity b t : ℝ)⁻¹) ^ arity b t

theorem scale_pos (b : ℕ) : 0 < scale b := by unfold scale; positivity

theorem chi_pos (b t : ℕ) : 0 < chi b t := by
  have hr : 0 < (arity b t : ℝ) := Nat.cast_pos.mpr (arity_pos b t)
  exact mul_pos (scale_pos b) (pow_pos (inv_pos.mpr hr) _)

theorem chi_formula (b t : ℕ) :
    chi b t = 3 ^ (3 * b) * 4 ^ 4 / (25 ^ b * (arity b t : ℝ) ^ arity b t) := by
  unfold chi scale
  rw [inv_pow]
  ring

theorem massFactor_product {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ) :
    massFactor y s T = scale b * ∏ j, massVector y s T j := by
  simp only [massVector, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    div_pow, Finset.prod_div_distrib]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm b 3]
  unfold massFactor scale
  rw [div_pow, one_pow]
  field_simp <;> ring

theorem massFactor_nonneg {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ)
    (hy : ∀ j, 0 ≤ y j) (hs : ∀ i, 0 ≤ s i) (hT : 0 ≤ T) :
    0 ≤ massFactor y s T := by
  unfold massFactor
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hT 4))
    (Finset.prod_nonneg (fun i _ => pow_nonneg (hs i) 3)))
    (Finset.prod_nonneg (fun j _ => hy j))

theorem massFactor_le {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ)
    (hy : ∀ j, 0 ≤ y j) (hs : ∀ i, 0 ≤ s i) (hT : 0 ≤ T)
    (htotal : (∑ j, y j) + (∑ i, s i) + T = 1) : massFactor y s T ≤ chi b t := by
  have hz := massVector_probability y s T hy hs hT htotal
  have hp := product_le_card_inv_pow (massVector y s T) hz.1 hz.2
  rw [slot_card] at hp
  rw [massFactor_product]
  exact mul_le_mul_of_nonneg_left hp (scale_pos b).le

theorem massFactor_eq_iff {b t : ℕ} (y : Fin t → ℝ) (s : Fin b → ℝ) (T : ℝ)
    (hy : ∀ j, 0 ≤ y j) (hs : ∀ i, 0 ≤ s i) (hT : 0 ≤ T)
    (htotal : (∑ j, y j) + (∑ i, s i) + T = 1) :
    massFactor y s T = chi b t ↔
      (∀ j, y j = 1 / (arity b t : ℝ)) ∧ (∀ i, s i = 3 / (arity b t : ℝ)) ∧
        T = 4 / (arity b t : ℝ) := by
  have hz := massVector_probability y s T hy hs hT htotal
  rw [massFactor_product, chi, mul_right_inj' (ne_of_gt (scale_pos b))]
  rw [← slot_card b t, product_eq_card_inv_pow_iff _ hz.1 hz.2]
  simp only [slot_card]
  constructor
  · intro h
    refine ⟨fun j => by simpa [massVector, one_div] using h (.inl j), ?_, ?_⟩
    · intro i
      have hi := h (.inr (.inl ⟨i, 0⟩))
      change s i / 3 = _ at hi
      rw [div_eq_iff (by norm_num : (3 : ℝ) ≠ 0)] at hi
      simpa [div_eq_mul_inv, mul_comm] using hi
    · have hi := h (.inr (.inr 0))
      change T / 4 = _ at hi
      rw [div_eq_iff (by norm_num : (4 : ℝ) ≠ 0)] at hi
      simpa [div_eq_mul_inv, mul_comm] using hi
  · rintro ⟨hy, hs, hT⟩ j
    rcases j with j | (⟨i, k⟩ | k)
    · simpa [massVector, one_div] using hy j
    · dsimp [massVector]
      rw [hs i]
      ring
    · dsimp [massVector]
      rw [hT]
      ring

end OuterWeights
end TuranUniversality.Structural
