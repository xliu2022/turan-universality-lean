/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ProjectionMoments
public import TuranUniversality.Selector.SliceNumerics

/-!
# A dense coordinate section in an intersecting family

The conditional averages are explicitly defined by finite averaging.
The conclusion combines the proved second- and fourth-moment estimates.
-/

@[expose] public section

namespace TuranUniversality.Selector

variable {α : Type*}

/-- Average after fixing one specified coordinate. -/
noncomputable def sectionAverage [Fintype α] :
    (d : ℕ) → (Words α d → ℝ) → Fin d → α → ℝ
  | 0, _, j => Fin.elim0 j
  | d + 1, f, j => Fin.cases
      (fun b => mean (fun y => f (b, y)))
      (fun k => sectionAverage d (fun y => mean (fun i => f (i, y))) k) j

@[simp] theorem sectionAverage_zero [Fintype α] (d : ℕ)
    (f : Words α (d + 1) → ℝ) (b : α) :
    sectionAverage (d + 1) f 0 b = mean (fun y => f (b, y)) := rfl

@[simp] theorem sectionAverage_succ [Fintype α] (d : ℕ)
    (f : Words α (d + 1) → ℝ) (j : Fin d) (b : α) :
    sectionAverage (d + 1) f j.succ b =
      sectionAverage d (fun y => mean (fun i => f (i, y))) j b := rfl

theorem sectionAverage_nonneg [Fintype α] (d : ℕ) (f : Words α d → ℝ)
    (hf : ∀ x, 0 ≤ f x) (j : Fin d) (b : α) : 0 ≤ sectionAverage d f j b := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
      refine Fin.cases ?_ ?_ j
      · exact mean_nonneg fun y => hf (b, y)
      · intro k
        exact ih _ (fun y => mean_nonneg fun i => hf (i, y)) k

theorem sectionAverage_mean [Fintype α] (d : ℕ) (f : Words α d → ℝ) (j : Fin d) :
    mean (sectionAverage d f j) = mean f := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
      refine Fin.cases ?_ ?_ j
      · exact (mean_prod f).symm
      · intro k
        rw [show sectionAverage (d + 1) f k.succ =
          sectionAverage d (fun y => mean (fun i => f (i, y))) k from rfl, ih]
        rw [mean_comm]
        exact (mean_prod f).symm

theorem componentBound_of_sections_le [Fintype α] [Nonempty α]
    (M : ℝ) (d : ℕ) (f : Words α d → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsections : ∀ j b, sectionAverage d f j b ≤ M) :
    ComponentBound M d f := by
  induction d with
  | zero => trivial
  | succ d ih =>
      have hm0 : 0 ≤ mean f := mean_nonneg hf
      have hmM : mean f ≤ M := by
        rw [← sectionAverage_mean (d + 1) f 0, ← mean_const (α := α) M]
        exact mean_mono (fun b => hsections 0 b)
      constructor
      · intro i
        have hrow0 : 0 ≤ mean (fun y => f (i, y)) := mean_nonneg fun y => hf (i, y)
        have hrowM : mean (fun y => f (i, y)) ≤ M := hsections 0 i
        apply abs_le.mpr
        constructor <;> linarith
      · exact ih _ (fun y => mean_nonneg fun i => hf (i, y))
          (fun j b => hsections j.succ b)

/-- An intersecting family above density `1/(64n)` has a coordinate
section of density greater than `2⁻¹³`. -/
theorem intersecting_has_large_section [Fintype α] [Nonempty α]
    (hn : 1048576 ≤ Fintype.card α) {d : ℕ}
    (F : Finset (Words α d)) (hF : CrossIntersecting F F)
    (hdensity : 1 / (64 * (Fintype.card α : ℝ)) < density F) :
    ∃ j b, (1 / 8192 : ℝ) < sectionAverage d (indicator F) j b := by
  classical
  by_contra hnone
  push Not at hnone
  have hn2 : 2 ≤ Fintype.card α := by omega
  let r : ℝ := 1 / ((Fintype.card α : ℝ) - 1)
  have hnR : (1048576 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hden : 0 < (Fintype.card α : ℝ) - 1 := by linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one hden).mpr
    linarith
  have hrsq : r ^ 2 ≤ 1 := by nlinarith
  have hcomponents : ComponentBound (1 / 8192) d (indicator F) := by
    apply componentBound_of_sections_le _ _ _ _ hnone
    intro x
    by_cases hx : x ∈ F <;> simp [indicator, hx]
  have hlower := firstProjection_lower_of_zero_correlation r hrsq d (indicator F)
    (cross_intersecting_correlation_zero hn2 F F hF)
  rw [energy_indicator] at hlower
  have hholder := indicator_correlation_fourth F (firstProjection d (indicator F))
  rw [firstProjection_inner] at hholder
  have hfourth := firstProjection_fourth (1 / 8192) d (indicator F) hcomponents
  have hmoment : energy (firstProjection d (indicator F)) ^ 4 ≤
      density F ^ 3 * ((1 / 8192 : ℝ) ^ 2 * energy (firstProjection d (indicator F)) +
        3 * energy (firstProjection d (indicator F)) ^ 2) := by
    exact hholder.trans (mul_le_mul_of_nonneg_left hfourth (by
      exact pow_nonneg (density_nonneg F) 3))
  exact slice_moment_contradiction (Fintype.card α) (density F)
    (energy (firstProjection d (indicator F))) hnR hdensity hlower hmoment

end TuranUniversality.Selector
