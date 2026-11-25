module

public import TuranUniversality.Weighted.Baseline

/-!
# Absorbing the contribution of ambiguous codes

The first theorem isolates the polynomial calculation in the manuscript's
ambiguity estimate. The second part checks its coefficient hypotheses for the
explicit rational baseline parameters.
-/

@[expose] public section

namespace TuranUniversality.Weighted

/-- The square estimate used to control the cubic reward. -/
theorem ambiguous_cube_bound (s t w x : ℝ) (ht : 0 ≤ t)
    (hw : 0 ≤ w) (hwt : w ≤ t) :
    w ^ 3 ≤ 2 * t * (t - x * s) ^ 2 + 2 * x ^ 2 * s ^ 2 * w := by
  have hsq : w ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hw ht).mpr hwt
  have hfirst := mul_le_mul_of_nonneg_left hsq hw
  have hsecond := mul_nonneg hw (sq_nonneg (t - 2 * x * s))
  have hthird := mul_nonneg (sub_nonneg.mpr hwt) (sq_nonneg (t - x * s))
  nlinarith

/-- Quantitative ambiguity estimate, with abstract coefficients.

Here `r = 1/(2m)`, `h = 1/(2q)`, and `B` is the value of the baseline
polynomial at the current total data mass `t`.
-/
theorem ambiguity_gap (Bstar B r h d s t w x : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hw : 0 ≤ w) (hwt : w ≤ t)
    (hBstar : 1 / 8 ≤ Bstar) (hd : r ≤ d)
    (hepsilon : x ^ 2 / 3 ≤ h - 2 * r * x)
    (hfactor : Bstar - B = (t - x * s) ^ 2 * (Bstar * t + d * s)) :
    r * s * (t - w - x * s) ^ 2 + 7 * x ^ 2 / 27 * s ^ 2 * w ≤
      Bstar - (B + 2 * r * s * (t * w - w ^ 2 / 2) - h * s ^ 2 * w + w ^ 3 / 27) := by
  have hidentity :
      Bstar - (B + 2 * r * s * (t * w - w ^ 2 / 2) - h * s ^ 2 * w + w ^ 3 / 27) =
      r * s * (t - w - x * s) ^ 2 +
        (Bstar * t + s * (d - r)) * (t - x * s) ^ 2 +
        (h - 2 * r * x) * s ^ 2 * w - w ^ 3 / 27 := by
    linear_combination hfactor
  have hcube := ambiguous_cube_bound s t w x ht hw hwt
  have hmain : 0 ≤ (Bstar - 2 / 27) * t * (t - x * s) ^ 2 := by
    have hco : 0 ≤ Bstar - 2 / 27 := by linarith
    positivity
  have hside : 0 ≤ s * (d - r) * (t - x * s) ^ 2 := by
    have hco := sub_nonneg.mpr hd
    positivity
  have hepsmul := mul_le_mul_of_nonneg_right hepsilon
    (show 0 ≤ s ^ 2 * w by positivity)
  nlinarith

theorem ambiguity_le (Bstar B r h d s t w x : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hw : 0 ≤ w) (hwt : w ≤ t)
    (hBstar : 1 / 8 ≤ Bstar) (hd : r ≤ d)
    (hepsilon : x ^ 2 / 3 ≤ h - 2 * r * x)
    (hfactor : Bstar - B = (t - x * s) ^ 2 * (Bstar * t + d * s)) :
    B + 2 * r * s * (t * w - w ^ 2 / 2) - h * s ^ 2 * w + w ^ 3 / 27 ≤ Bstar := by
  have hgap := ambiguity_gap Bstar B r h d s t w x hs ht hw hwt hBstar hd hepsilon hfactor
  have hnonneg : 0 ≤ r * s * (t - w - x * s) ^ 2 + 7 * x ^ 2 / 27 * s ^ 2 * w := by
    positivity
  linarith

theorem one_eighth_le_coeffA (q : ℝ) (hq : 12 ≤ q) : 1 / 8 ≤ coeffA q := by
  have hq0 : 0 < q := by linarith
  unfold coeffA
  apply (le_div_iff₀ (show 0 < 6 * q ^ 2 by positivity)).mpr
  nlinarith [mul_nonneg hq0.le (sub_nonneg.mpr hq)]

theorem one_eighth_le_baselineMax (m : ℝ) (hm : 30 ≤ m) :
    1 / 8 ≤ baselineMax m (rootCount m) := by
  have hq := rootCount_gt_twice m hm
  have ha := one_eighth_le_coeffA (rootCount m) (by linarith)
  exact ha.trans (baselineMax_strict_bounds m hm).1.le

theorem six_le_kappa (m : ℝ) (hm : 30 ≤ m) : 6 ≤ kappa m := by
  have hden : 0 < m - 1 := by linarith
  have hdiv : 1 / (m - 1) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  unfold kappa
  linarith

theorem kappa_lt_half (m : ℝ) (hm : 1 < m) : kappa m < m / 2 := by
  have hpos : 0 < 1 / (m - 1) := by positivity
  unfold kappa
  linarith

theorem factorCoefficient_lower (m : ℝ) (hm : 30 ≤ m) :
    1 / (2 * m) ≤
      factorCoefficient (coeffA (rootCount m)) (coeffB (rootCount m)) (coeffC m)
        (criticalRatio m (rootCount m)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 < m := by linarith
  have hq2m := rootCount_gt_twice m hm
  have hq0 : 0 < rootCount m := by linarith
  have hx : 0 < criticalRatio m (rootCount m) := div_pos (kappa_pos m hm2) hq0
  have heq := baselineMax_eq_stationaryValue m (rootCount m) hm2 hq0
  have hv := one_eighth_le_baselineMax m hm
  have hva := (baselineMax_strict_bounds m hm).1.le
  rw [heq] at hv hva
  have hmul := mul_le_mul_of_nonneg_right hv hx.le
  have hc : coeffC m = 1 / 2 - 1 / (2 * m) := by
    unfold coeffC
    field_simp
  have hroot : 3 * coeffA (rootCount m) - 1 / 2 +
      criticalRatio m (rootCount m) / 4 =
      (kappa m / 4 - 3 / 2) / rootCount m + 1 / (rootCount m) ^ 2 := by
    unfold coeffA criticalRatio
    field_simp
    ring
  have hk := six_le_kappa m hm
  have hkn : 0 ≤ kappa m / 4 - 3 / 2 := by linarith
  have hroot0 : 0 ≤ (kappa m / 4 - 3 / 2) / rootCount m + 1 / (rootCount m) ^ 2 := by
    positivity
  unfold factorCoefficient
  nlinarith

theorem parameter_epsilon (m q : ℝ) (hm : 1 < m) (hq : 0 < q) :
    1 / (2 * q) - 2 * (1 / (2 * m)) * criticalRatio m q =
      1 / (m * (m - 1) * q) := by
  have hm0 : m ≠ 0 := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  unfold criticalRatio kappa
  field_simp
  ring

theorem parameter_epsilon_lower (m : ℝ) (hm : 30 ≤ m) :
    (criticalRatio m (rootCount m)) ^ 2 / 3 ≤
      1 / (2 * rootCount m) - 2 * (1 / (2 * m)) * criticalRatio m (rootCount m) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hq2m := rootCount_gt_twice m hm
  have hq0 : 0 < rootCount m := by linarith
  have hk0 := kappa_pos m (by linarith)
  have hkh := (kappa_lt_half m (by linarith)).le
  have hksq : (kappa m) ^ 2 ≤ (m / 2) ^ 2 :=
    (sq_le_sq₀ hk0.le (by positivity)).mpr hkh
  have hA := mul_le_mul_of_nonneg_right
    (show m * (m - 1) ≤ m ^ 2 by nlinarith) (sq_nonneg (kappa m))
  have hB := mul_le_mul_of_nonneg_left hksq (sq_nonneg m)
  have hqbound := (rootCount_bounds m hm).1
  have hcentral : m * (m - 1) * (kappa m) ^ 2 ≤ 3 * rootCount m := by
    nlinarith
  rw [parameter_epsilon m (rootCount m) (by linarith) hq0]
  unfold criticalRatio
  rw [div_pow, div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have := mul_le_mul_of_nonneg_right hcentral hq0.le
  nlinarith

/-- The quantitative inequality in the manuscript's ambiguity lemma. -/
theorem baseline_ambiguity_gap (m s t w : ℝ) (hm : 30 ≤ m)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hw : 0 ≤ w) (hwt : w ≤ t) :
    s / (2 * m) * (t - w - criticalRatio m (rootCount m) * s) ^ 2 +
        7 * (criticalRatio m (rootCount m)) ^ 2 / 27 * s ^ 2 * w ≤
      baselineMax m (rootCount m) -
        (baseline m (rootCount m) t + s / m * (t * w - w ^ 2 / 2) -
          s ^ 2 * w / (2 * rootCount m) + w ^ 3 / 27) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 < m := by linarith
  have hq2m := rootCount_gt_twice m hm
  have hq0 : 0 < rootCount m := by linarith
  have hx : 0 < criticalRatio m (rootCount m) := div_pos (kappa_pos m hm2) hq0
  have hsrel : s = 1 - t := by linarith
  have hfactor := stationary_factorization (coeffA (rootCount m)) (coeffB (rootCount m))
    (coeffC m) (criticalRatio m (rootCount m)) t (by positivity)
    (stationaryRemainder_rootCount m hm)
  rw [← hsrel, ← baselineMax_eq_stationaryValue m (rootCount m) hm2 hq0] at hfactor
  have hgap := ambiguity_gap (baselineMax m (rootCount m)) (baseline m (rootCount m) t)
    (1 / (2 * m)) (1 / (2 * rootCount m))
    (factorCoefficient (coeffA (rootCount m)) (coeffB (rootCount m)) (coeffC m)
      (criticalRatio m (rootCount m))) s t w (criticalRatio m (rootCount m))
    hs ht hw hwt (one_eighth_le_baselineMax m hm) (factorCoefficient_lower m hm)
    (parameter_epsilon_lower m hm) hfactor
  have hr : 2 * (1 / (2 * m)) * s = s / m := by field_simp
  rw [hr] at hgap
  convert hgap using 1 <;> ring

theorem baseline_ambiguity_le (m s t w : ℝ) (hm : 30 ≤ m)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hw : 0 ≤ w) (hwt : w ≤ t) :
    baseline m (rootCount m) t + s / m * (t * w - w ^ 2 / 2) -
      s ^ 2 * w / (2 * rootCount m) + w ^ 3 / 27 ≤ baselineMax m (rootCount m) := by
  have hgap := baseline_ambiguity_gap m s t w hm hs ht hst hw hwt
  have hm0 : 0 < m := by linarith
  have hnonneg : 0 ≤ s / (2 * m) * (t - w - criticalRatio m (rootCount m) * s) ^ 2 +
      7 * (criticalRatio m (rootCount m)) ^ 2 / 27 * s ^ 2 * w := by positivity
  linarith

end TuranUniversality.Weighted
