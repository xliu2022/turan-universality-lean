/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! # Numerical estimates for concentration in a coordinate slice -/

@[expose] public section

namespace TuranUniversality.Selector

/-- The numerical contradiction used to obtain a section of density
greater than `2⁻¹³`. Variables `a` and `W` are the family density and the
first-level energy. -/
theorem slice_moment_contradiction (n a W : ℝ)
    (hn : (1048576 : ℝ) ≤ n)
    (ha : 1 / (64 * n) < a)
    (hlower : a ^ 2 ≤ (1 / (n - 1)) * W + (1 / (n - 1)) ^ 2 * a)
    (hmoment : W ^ 4 ≤ a ^ 3 * ((1 / 8192 : ℝ) ^ 2 * W + 3 * W ^ 2)) : False := by
  have hnpos : 0 < n := by linarith
  have hzpos : 0 < n - 1 := by linarith
  have hapos : 0 < a := (by positivity : 0 < (1 : ℝ) / (64 * n)).trans ha
  have hna : (1 / 64 : ℝ) < n * a := by
    have h := (div_lt_iff₀ (show 0 < 64 * n by positivity)).mp ha
    nlinarith
  let v : ℝ := W / a
  have hW : W = a * v := by dsimp [v]; field_simp
  have hlower' : a ≤ (1 / (n - 1)) * v + (1 / (n - 1)) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hapos).mp
    rw [hW] at hlower
    nlinarith [hlower]
  have hscaled : a * (n - 1) ^ 2 ≤ v * (n - 1) + 1 := by
    have h := mul_le_mul_of_nonneg_right hlower' (sq_nonneg (n - 1))
    field_simp [ne_of_gt hzpos] at h
    nlinarith [h]
  have hzhalf : n / 2 ≤ n - 1 := by linarith
  have hbonus : 1 ≤ a * n * (n - 1) / 4 := by
    have h := mul_le_mul_of_nonneg_right (le_of_lt hna)
      (show 0 ≤ (n - 1) / 4 by positivity)
    nlinarith [h]
  have hhalf : n * a / 2 * (n - 1) ≤ a * (n - 1) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hzhalf
      (show 0 ≤ a * (n - 1) by positivity)
    nlinarith [h]
  have hvlarge : n * a / 4 ≤ v := by
    apply (mul_le_mul_iff_right₀ hzpos).mp
    nlinarith [hscaled, hbonus, hhalf]
  have hv : (1 / 256 : ℝ) < v := by linarith
  have hvpos : 0 < v := by linarith
  have hmoment' : v ^ 4 ≤ (1 / 8192 : ℝ) ^ 2 * v + 3 * a * v ^ 2 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hapos 4)).mp
    rw [hW] at hmoment
    convert hmoment using 1 <;> ring
  have hcubic : v ^ 3 ≤ (1 / 8192 : ℝ) ^ 2 + 3 * a * v := by
    apply (mul_le_mul_iff_right₀ hvpos).mp
    nlinarith [hmoment']
  have hnv : 24 ≤ n * v := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hv) (le_of_lt hnpos)
    nlinarith [h]
  have hsmall : 3 * a * v ≤ v ^ 3 / 2 := by
    have h1 := mul_le_mul_of_nonneg_right
      (show n * a ≤ 4 * v by linarith) (show 0 ≤ 3 * v by positivity)
    have h2 := mul_le_mul_of_nonneg_right hnv (show 0 ≤ v ^ 2 / 2 by positivity)
    apply (mul_le_mul_iff_left₀ hnpos).mp
    nlinarith [h1, h2]
  have hcube : (1 / 256 : ℝ) ^ 3 < v ^ 3 := by
    gcongr
  norm_num at hcube
  norm_num at hcubic
  nlinarith [hcubic, hsmall, hcube]

end TuranUniversality.Selector
