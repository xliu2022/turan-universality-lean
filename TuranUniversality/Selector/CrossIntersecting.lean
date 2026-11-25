/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ProductMixing
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Cross-intersecting families of finite words

This proves the cross-intersection inequality from the manuscript
(`lem:spectral-cross`). The product mixing bound is proved in
`ProductMixing`, not assumed here.
-/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

variable {α β : Type*}

/-- Two words differ at every coordinate. -/
def AllDifferent : {d : ℕ} → Words α d → Words α d → Prop
  | 0, _, _ => True
  | _ + 1, x, y => x.1 ≠ y.1 ∧ AllDifferent x.2 y.2

/-- Families are cross-intersecting when every word in one shares a
coordinate with every word in the other. -/
def CrossIntersecting {d : ℕ} (A B : Finset (Words α d)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, ¬AllDifferent x y

/-- Recursive words are equivalent to the usual functions on `Fin d`. -/
def wordsEquivFunction (α : Type*) : (d : ℕ) → Words α d ≃ (Fin d → α)
  | 0 => (Equiv.arrowPUnitOfIsEmpty (Fin 0) α).symm
  | d + 1 => (Equiv.prodCongr (Equiv.refl α) (wordsEquivFunction α d)).trans
      (Fin.consEquiv (fun _ => α))

theorem allDifferent_iff {d : ℕ} (x y : Words α d) :
    AllDifferent x y ↔ ∀ i, wordsEquivFunction α d x i ≠ wordsEquivFunction α d y i := by
  induction d with
  | zero => simp [AllDifferent]
  | succ d ih =>
      change (x.1 ≠ y.1 ∧ AllDifferent x.2 y.2) ↔
        ∀ i, (Fin.cons x.1 (wordsEquivFunction α d x.2) : Fin (d + 1) → α) i ≠
          (Fin.cons y.1 (wordsEquivFunction α d y.2) : Fin (d + 1) → α) i
      simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ih]

theorem complete_tensor_vanish [Fintype α]
    (hn : 2 ≤ Fintype.card α) (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (f : α × β → ℝ) (i : α) (x : β)
    (hf : ∀ j, j ≠ i → T (fun y => f (j, y)) x = 0) :
    tensorStep (1 / ((Fintype.card α : ℝ) - 1)) T f (i, x) = 0 := by
  classical
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  have hmean : T (fun y => mean (fun j => f (j, y))) x =
      T (fun y => f (i, y)) x / Fintype.card α := by
    rw [linearMap_mean]
    change mean (fun j => T (fun y => f (j, y)) x) = _
    rw [mean_eq_sum_div_card]
    congr 1
    exact Fintype.sum_eq_single i hf
  rw [tensorStep_apply, hmean]
  field_simp [hn0, hn1]
  ring

/-- At the complete-graph parameter, the product operator at `x` vanishes
when the input vanishes on every word differing from `x` everywhere. -/
theorem productNoise_vanish [Fintype α]
    (hn : 2 ≤ Fintype.card α) (d : ℕ) (f : Words α d → ℝ) (x : Words α d)
    (hf : ∀ y, AllDifferent x y → f y = 0) :
    productNoise (1 / ((Fintype.card α : ℝ) - 1)) d f x = 0 := by
  induction d with
  | zero => exact hf x trivial
  | succ d ih =>
      apply complete_tensor_vanish hn (productNoise _ d) f x.1 x.2
      intro j hji
      apply ih (fun y => f (j, y)) x.2
      intro y hxy
      exact hf (j, y) ⟨Ne.symm hji, hxy⟩

/-- Real indicator of a finite set. -/
noncomputable def indicator (A : Finset β) (x : β) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

/-- Uniform density of a finite set in its finite ambient type. -/
noncomputable def density [Fintype β] (A : Finset β) : ℝ := mean (indicator A)

theorem density_eq_card [Fintype β] (A : Finset β) :
    density A = (A.card : ℝ) / Fintype.card β := by
  classical
  simp [density, mean_eq_sum_div_card, indicator]

theorem density_map_equiv {γ : Type*} [Fintype β] [Fintype γ]
    (e : β ≃ γ) (A : Finset β) : density (A.map e.toEmbedding) = density A := by
  rw [density_eq_card, density_eq_card, Finset.card_map, Fintype.card_congr e]

theorem density_nonneg [Fintype β] (A : Finset β) : 0 ≤ density A := by
  apply mean_nonneg
  intro x
  simp only [indicator]
  split_ifs <;> norm_num

theorem density_le_one [Fintype β] [Nonempty β] (A : Finset β) : density A ≤ 1 := by
  rw [← mean_const (α := β) (1 : ℝ)]
  apply mean_mono
  intro x
  simp only [indicator]
  split_ifs <;> norm_num

theorem energy_indicator [Fintype β] (A : Finset β) : energy (indicator A) = density A := by
  apply mean_congr
  intro x
  simp [indicator]

theorem energy_indicator_centered [Fintype β] [Nonempty β] (A : Finset β) :
    energy (fun x => indicator A x - density A) = density A * (1 - density A) := by
  change energy (fun x => indicator A x - mean (indicator A)) = _
  rw [energy_centered, energy_indicator]
  change density A - density A ^ 2 = _
  ring

theorem cross_intersecting_correlation_zero [Fintype α]
    (hn : 2 ≤ Fintype.card α) {d : ℕ} (A B : Finset (Words α d))
    (hAB : CrossIntersecting A B) :
    mean (fun x => indicator A x *
      productNoise (1 / ((Fintype.card α : ℝ) - 1)) d (indicator B) x) = 0 := by
  classical
  calc
    _ = mean (fun _ : Words α d => (0 : ℝ)) := by
      apply mean_congr
      intro x
      by_cases hx : x ∈ A
      · have hz : productNoise (1 / ((Fintype.card α : ℝ) - 1)) d (indicator B) x = 0 := by
          apply productNoise_vanish hn
          intro y hxy
          have hy : y ∉ B := fun hy => hAB x hx y hy hxy
          simp [indicator, hy]
        rw [hz, mul_zero]
      · simp [indicator, hx]
    _ = 0 := mean_zero

/-- Cross-intersection bound, in any finite alphabet of size at least two.
It includes zero-density families. -/
theorem cross_intersecting_density_bound [Fintype α] [Nonempty α]
    (hn : 2 ≤ Fintype.card α) {d : ℕ} (A B : Finset (Words α d))
    (hAB : CrossIntersecting A B) :
    density A * density B ≤
      (1 - density A) * (1 - density B) / ((Fintype.card α : ℝ) - 1) ^ 2 := by
  let r : ℝ := 1 / ((Fintype.card α : ℝ) - 1)
  let T := productNoise (α := α) r d
  let a := density A
  let b := density B
  let f : Words α d → ℝ := fun x => indicator A x - a
  let g : Words α d → ℝ := fun x => indicator B x - b
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hden : 0 < (Fintype.card α : ℝ) - 1 := by linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one hden).mpr
    linarith
  have hrsq : r ^ 2 ≤ 1 := by nlinarith
  have hTg : T g = fun x => T (indicator B) x - b := by
    funext x
    change T (fun y => indicator B y - b) x = _
    rw [map_fun_sub]
    change _ - productNoise r d (fun _ => b) x = _
    rw [productNoise_const]
  have hz : mean (fun x => indicator A x * T (indicator B) x) = 0 :=
    cross_intersecting_correlation_zero hn A B hAB
  have hc : mean (fun x => f x * T g x) = -(a * b) := by
    rw [hTg]
    calc
      mean (fun x => f x * (T (indicator B) x - b)) =
          mean (fun x => indicator A x * T (indicator B) x -
            b * indicator A x - a * T (indicator B) x + a * b) :=
        mean_congr fun x => by dsimp [f]; ring
      _ = -(a * b) := by
        simp only [mean_add, mean_sub, mean_const_mul, mean_const, hz]
        change 0 - b * a - a * mean (productNoise r d (indicator B)) + a * b = _
        rw [productNoise_mean]
        change 0 - b * a - a * b + a * b = _
        ring
  have hEg : energy (T g) ≤ r ^ 2 * energy g := by
    have h := productNoise_bound (α := α) r hrsq d g
    have hmg : mean g = 0 := centered_mean (indicator B)
    simpa [hmg] using h
  have hEf : energy f = a * (1 - a) := energy_indicator_centered A
  have hEg' : energy g = b * (1 - b) := energy_indicator_centered B
  have hproduct : (a * b) ^ 2 ≤ r ^ 2 * a * (1 - a) * b * (1 - b) := by
    calc
      (a * b) ^ 2 = mean (fun x => f x * T g x) ^ 2 := by rw [hc]; ring
      _ ≤ energy f * energy (T g) := mean_mul_sq_le f (T g)
      _ ≤ energy f * (r ^ 2 * energy g) :=
        mul_le_mul_of_nonneg_left hEg (energy_nonneg f)
      _ = r ^ 2 * a * (1 - a) * b * (1 - b) := by rw [hEf, hEg']; ring
  have ha0 : 0 ≤ a := density_nonneg A
  have hb0 : 0 ≤ b := density_nonneg B
  have ha1 : a ≤ 1 := density_le_one A
  have hb1 : b ≤ 1 := density_le_one B
  change a * b ≤ (1 - a) * (1 - b) / ((Fintype.card α : ℝ) - 1) ^ 2
  by_cases hab : a * b = 0
  · rw [hab]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1))
      (sq_nonneg _)
  · have habpos : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha0 hb0) (Ne.symm hab)
    have hcancel : a * b ≤ r ^ 2 * (1 - a) * (1 - b) := by
      apply (mul_le_mul_iff_left₀ habpos).mp
      convert hproduct using 1 <;> ring
    calc
      a * b ≤ r ^ 2 * (1 - a) * (1 - b) := hcancel
      _ = (1 - a) * (1 - b) / ((Fintype.card α : ℝ) - 1) ^ 2 := by
        dsimp [r]
        field_simp [ne_of_gt hden]

theorem cross_intersecting_density_le [Fintype α] [Nonempty α]
    (hn : 2 ≤ Fintype.card α) {d : ℕ} (A B : Finset (Words α d))
    (hAB : CrossIntersecting A B) (hA : 0 < density A) :
    density B ≤ 1 / (((Fintype.card α : ℝ) - 1) ^ 2 * density A) := by
  have h := cross_intersecting_density_bound hn A B hAB
  have ha0 := density_nonneg A
  have hb0 := density_nonneg B
  have ha1 := density_le_one A
  have hb1 := density_le_one B
  have hnum : (1 - density A) * (1 - density B) ≤ 1 := by
    have hab : density A * density B ≤ density A :=
      mul_le_of_le_one_right ha0 hb1
    nlinarith
  have hmul : density A * density B ≤ 1 / ((Fintype.card α : ℝ) - 1) ^ 2 :=
    h.trans (div_le_div_of_nonneg_right hnum (sq_nonneg _))
  calc
    density B ≤ (1 / ((Fintype.card α : ℝ) - 1) ^ 2) / density A := by
      apply (le_div_iff₀ hA).mpr
      simpa [mul_comm] using hmul
    _ = 1 / (((Fintype.card α : ℝ) - 1) ^ 2 * density A) := by rw [div_div]

/-- The same bound on the standard function representation of words. -/
theorem cross_intersecting_functions_bound [Fintype α] [Nonempty α]
    (hn : 2 ≤ Fintype.card α) {d : ℕ} (A B : Finset (Fin d → α))
    (hAB : ∀ x ∈ A, ∀ y ∈ B, ∃ i, x i = y i) :
    density A * density B ≤
      (1 - density A) * (1 - density B) / ((Fintype.card α : ℝ) - 1) ^ 2 := by
  let e := wordsEquivFunction α d
  let A' := A.map e.symm.toEmbedding
  let B' := B.map e.symm.toEmbedding
  have hcross : CrossIntersecting A' B' := by
    intro u hu v hv hdiff
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨i, hi⟩ := hAB x hx y hy
    have hne := (allDifferent_iff _ _).mp hdiff i
    change e (e.symm x) i ≠ e (e.symm y) i at hne
    simp only [Equiv.apply_symm_apply] at hne
    exact hne hi
  have h := cross_intersecting_density_bound hn A' B' hcross
  simpa only [A', B', density_map_equiv] using h

end TuranUniversality.Selector
