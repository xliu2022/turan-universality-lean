/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.CoordinateSections

/-!
# Concentration in a coordinate slice

This file proves the complete statement labeled `lem:spectral-fourth` and
`cor:spectral-slice` in `turan_universality_V4.tex`, including the bound on
all families cross-intersecting with the selected section.
-/

@[expose] public section

namespace TuranUniversality.Selector

variable {α : Type*}

theorem cross_intersecting_with_dense_section [Fintype α] [Nonempty α]
    (hn : 1048576 ≤ Fintype.card α) {d : ℕ}
    (A B : Finset (Words α d)) (hA : (1 / 8192 : ℝ) < density A)
    (hAB : CrossIntersecting A B) :
    density B ≤ 1 / (64 * (Fintype.card α : ℝ)) := by
  have hn2 : 2 ≤ Fintype.card α := by omega
  have hnR : (1048576 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  let n : ℝ := Fintype.card α
  have hnpos : 0 < n := by dsimp [n]; linarith
  have hpoly : 524288 * n ≤ (n - 1) ^ 2 := by
    have hprod := mul_nonneg (show 0 ≤ n - 1048576 by dsimp [n]; linarith)
      (le_of_lt hnpos)
    nlinarith [hprod]
  have hden : 64 * n ≤ (n - 1) ^ 2 * density A := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hA) (sq_nonneg (n - 1))
    nlinarith [h, hpoly]
  have hapos : 0 < density A := (by norm_num : (0 : ℝ) < 1 / 8192).trans hA
  have h := cross_intersecting_density_le hn2 A B hAB hapos
  exact h.trans (one_div_le_one_div_of_le (show 0 < 64 * n by positivity) hden)

/-- Every intersecting family is either small or concentrated in one
coordinate slice. The chosen section also has uniformly small
cross-intersecting families. -/
theorem spectral_slice [Fintype α] [Nonempty α]
    (hn : 1048576 ≤ Fintype.card α) {d : ℕ}
    (F : Finset (Words α (d + 1))) (hF : CrossIntersecting F F) :
    density F ≤ 1 / (64 * (Fintype.card α : ℝ)) ∨
      ∃ (j : Fin (d + 1)) (b : α),
        density (outsideSlice F j b) ≤ 1 / (64 * (Fintype.card α : ℝ)) ∧
          ∀ G : Finset (Words α d),
            CrossIntersecting (wordSection F j b) G →
              density G ≤ 1 / (64 * (Fintype.card α : ℝ)) := by
  classical
  by_cases hsmall : density F ≤ 1 / (64 * (Fintype.card α : ℝ))
  · exact Or.inl hsmall
  · have hlarge : 1 / (64 * (Fintype.card α : ℝ)) < density F := lt_of_not_ge hsmall
    obtain ⟨j, b, hsection⟩ := intersecting_has_large_section hn F hF hlarge
    have hsection' : (1 / 8192 : ℝ) < density (wordSection F j b) := by
      rw [density_wordSection_eq_average]
      exact hsection
    have hcross : ∀ G : Finset (Words α d),
        CrossIntersecting (wordSection F j b) G →
          density G ≤ 1 / (64 * (Fintype.card α : ℝ)) := by
      intro G hG
      exact cross_intersecting_with_dense_section hn (wordSection F j b) G hsection' hG
    refine Or.inr ⟨j, b, ?_, hcross⟩
    rw [density_outsideSlice]
    calc
      _ ≤ mean (fun _ : α => 1 / (64 * (Fintype.card α : ℝ))) := by
        apply mean_mono
        intro c
        by_cases hcb : c = b
        · simp only [ite_eq_left hcb]
          positivity
        · simp only [ite_eq_right hcb]
          exact hcross _ (sections_cross_intersecting F hF j (Ne.symm hcb))
      _ = 1 / (64 * (Fintype.card α : ℝ)) := mean_const _

end TuranUniversality.Selector
