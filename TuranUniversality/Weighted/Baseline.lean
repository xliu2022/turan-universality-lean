module

public import Mathlib

/-!
# The rational baseline polynomial

Algebraic part of Lemma 4.3 of `turan_universality_V4.tex`.
The generic cubic lemma avoids differentiation and will also be used in the
ambiguity estimate. All parameters are treated symbolically; no gigantic
root set is evaluated.
-/

@[expose] public section

namespace TuranUniversality.Weighted

/-- The edge polynomial of the baseline construction. -/
def cubic (a b c t : ℝ) : ℝ :=
  a * (1 - t) ^ 3 + b * (1 - t) ^ 2 * t + c * (1 - t) * t ^ 2

/-- The stationary value, in the coordinate `x = t / (1-t)`. -/
noncomputable def stationaryValue (a b c x : ℝ) : ℝ :=
  (a + b * x + c * x ^ 2) / (1 + x) ^ 3

def stationaryRemainder (a b c x : ℝ) : ℝ :=
  (b - 3 * a) + (2 * c - 2 * b) * x - c * x ^ 2

noncomputable def factorCoefficient (a b c x : ℝ) : ℝ :=
  3 * stationaryValue a b c x - c + 2 * stationaryValue a b c x * x

theorem cubic_at_critical_mass (a b c x : ℝ) (hx : 1 + x ≠ 0) :
    cubic a b c (x / (1 + x)) = stationaryValue a b c x := by
  unfold cubic stationaryValue
  field_simp
  ring

/-- Exact factorization at the stationary point. -/
theorem stationary_factorization (a b c x t : ℝ) (hx : 1 + x ≠ 0)
    (hstat : stationaryRemainder a b c x = 0) :
    stationaryValue a b c x - cubic a b c t =
      (t - x * (1 - t)) ^ 2 *
        (stationaryValue a b c x * t + factorCoefficient a b c x * (1 - t)) := by
  unfold cubic stationaryValue factorCoefficient
  unfold stationaryValue
  unfold stationaryRemainder at hstat
  field_simp
  linear_combination -(t - 1) ^ 2 * (x + 1) ^ 2 * (t * x + t - x) * hstat

/-- A positive stationary ratio gives a strict improvement over the root-only
baseline under the elementary coefficient inequalities used below. -/
theorem stationaryValue_gt_a (a b c x : ℝ) (hx : 0 < x)
    (hab : 3 * a < b) (hbc : c < b) (hac : a < c)
    (hstat : stationaryRemainder a b c x = 0) :
    a < stationaryValue a b c x := by
  have hden : 1 + x ≠ 0 := by positivity
  have hidentity : stationaryValue a b c x - a =
      x ^ 2 * ((2 * b - c - 3 * a) + (c - a) * x) / (1 + x) ^ 3 := by
    unfold stationaryValue
    unfold stationaryRemainder at hstat
    field_simp
    linear_combination x * hstat
  have hbracket : 0 < (2 * b - c - 3 * a) + (c - a) * x := by
    have := mul_pos (sub_pos.mpr hac) hx
    linarith
  have hpositive : 0 <
      x ^ 2 * ((2 * b - c - 3 * a) + (c - a) * x) / (1 + x) ^ 3 := by
    positivity
  linarith

theorem factorCoefficient_pos (a b c x : ℝ) (hx : 0 < x)
    (hab : 3 * a < b) (hbc : c < b) (hac : a < c)
    (hstat : stationaryRemainder a b c x = 0) :
    0 < factorCoefficient a b c x := by
  have hden : 1 + x ≠ 0 := by positivity
  have hgap := stationaryValue_gt_a a b c x hx hab hbc hac hstat
  have hf := stationary_factorization a b c x 0 hden hstat
  norm_num [cubic] at hf
  have hprod : 0 < x ^ 2 * factorCoefficient a b c x := by linarith
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hx)).mp hprod

theorem cubic_le_stationaryValue (a b c x t : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hab : 3 * a < b) (hbc : c < b) (hac : a < c)
    (hstat : stationaryRemainder a b c x = 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cubic a b c t ≤ stationaryValue a b c x := by
  have hvalue : 0 < stationaryValue a b c x :=
    ha.trans (stationaryValue_gt_a a b c x hx hab hbc hac hstat)
  have hd := factorCoefficient_pos a b c x hx hab hbc hac hstat
  have hf := stationary_factorization a b c x t (by positivity) hstat
  have hnonneg : 0 ≤ (t - x * (1 - t)) ^ 2 *
      (stationaryValue a b c x * t + factorCoefficient a b c x * (1 - t)) := by
    positivity
  linarith

theorem cubic_eq_stationaryValue_iff (a b c x t : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hab : 3 * a < b) (hbc : c < b) (hac : a < c)
    (hstat : stationaryRemainder a b c x = 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cubic a b c t = stationaryValue a b c x ↔ t = x / (1 + x) := by
  have hden : 1 + x ≠ 0 := by positivity
  constructor
  · intro heq
    have hv : 0 < stationaryValue a b c x :=
      ha.trans (stationaryValue_gt_a a b c x hx hab hbc hac hstat)
    have hd := factorCoefficient_pos a b c x hx hab hbc hac hstat
    have hcoef : 0 < stationaryValue a b c x * t +
        factorCoefficient a b c x * (1 - t) := by
      rcases eq_or_lt_of_le ht0 with ht | ht
      · subst t
        simpa using hd
      · have hfirst := mul_pos hv ht
        have hsecond := mul_nonneg hd.le (sub_nonneg.mpr ht1)
        linarith
    have hf := stationary_factorization a b c x t hden hstat
    rw [heq, sub_self] at hf
    have hsquare : (t - x * (1 - t)) ^ 2 = 0 :=
      (mul_eq_zero.mp hf.symm).resolve_right (ne_of_gt hcoef)
    have hlinear : t - x * (1 - t) = 0 := (sq_eq_zero_iff).mp hsquare
    apply (eq_div_iff hden).mpr
    nlinarith
  · rintro rfl
    exact cubic_at_critical_mass a b c x hden

/-- Coefficient comparison with the complete three-graph polynomial. -/
theorem cubic_lt_one_sixth (a b c t : ℝ) (ha : a < 1 / 6)
    (hb : b ≤ 1 / 2) (hc : c ≤ 1 / 2) (ht0 : 0 < t) (ht1 : t < 1) :
    cubic a b c t < 1 / 6 := by
  have hs : 0 < 1 - t := sub_pos.mpr ht1
  have hA := mul_lt_mul_of_pos_right ha (pow_pos hs 3)
  have hB := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (1 - t) ^ 2 * t by positivity)
  have hC := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (1 - t) * t ^ 2 by positivity)
  have ht3 := pow_pos ht0 3
  unfold cubic
  nlinarith

/-- The root-count polynomial, viewed as a real parameter for the algebraic
inequalities. Its integrality is a separate finite-construction fact. -/
noncomputable def rootCount (m : ℝ) : ℝ :=
  (m ^ 4 - 10 * m ^ 3 + 13 * m ^ 2 + 12 * m + 4) / 8

noncomputable def kappa (m : ℝ) : ℝ := m / 2 - 1 / (m - 1)

noncomputable def coeffA (q : ℝ) : ℝ := (q - 1) * (q - 2) / (6 * q ^ 2)

noncomputable def coeffB (q : ℝ) : ℝ := (q - 2) / (2 * q)

noncomputable def coeffC (m : ℝ) : ℝ := (m - 1) / (2 * m)

noncomputable def criticalRatio (m q : ℝ) : ℝ := kappa m / q

noncomputable def criticalMass (m q : ℝ) : ℝ := kappa m / (q + kappa m)

noncomputable def baseline (m q t : ℝ) : ℝ := cubic (coeffA q) (coeffB q) (coeffC m) t

noncomputable def baselineMax (m q : ℝ) : ℝ := baseline m q (criticalMass m q)

theorem rootCount_bounds (m : ℝ) (hm : 30 ≤ m) :
    m ^ 4 / 12 ≤ rootCount m ∧ rootCount m ≤ m ^ 4 / 8 := by
  have hm0 : 0 ≤ m := by linarith
  have h2 := mul_nonneg hm0 (sub_nonneg.mpr hm)
  have h3 := mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm)
  have h4 := mul_nonneg (pow_nonneg hm0 3) (sub_nonneg.mpr hm)
  unfold rootCount
  constructor <;> nlinarith [sq_nonneg m]

theorem rootCount_gt_twice (m : ℝ) (hm : 30 ≤ m) :
    2 * m < rootCount m := by
  have hm0 : 0 ≤ m := by linarith
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have h2 := mul_nonneg hm0 (sub_nonneg.mpr hm)
  have h4 := mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm2)
  have hq := (rootCount_bounds m hm).1
  nlinarith

theorem kappa_factorization (m : ℝ) (hm : m - 1 ≠ 0) :
    kappa m = (m - 2) * (m + 1) / (2 * (m - 1)) := by
  unfold kappa
  field_simp
  ring

theorem kappa_pos (m : ℝ) (hm : 2 < m) : 0 < kappa m := by
  rw [kappa_factorization m (by linarith)]
  exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)

theorem kappa_identity (m : ℝ) (hm : m ≠ 0) (hm1 : m - 1 ≠ 0) :
    1 - 2 * kappa m + coeffC m * (kappa m) ^ 2 =
      rootCount m / (m * (m - 1)) := by
  unfold kappa coeffC rootCount
  field_simp
  ring

theorem stationaryRemainder_formula (m q : ℝ)
    (hm : m ≠ 0) (hm1 : m - 1 ≠ 0) (hq : q ≠ 0) :
    stationaryRemainder (coeffA q) (coeffB q) (coeffC m) (criticalRatio m q) =
      (q - rootCount m) / (m * q ^ 2 * (m - 1)) := by
  unfold stationaryRemainder coeffA coeffB coeffC criticalRatio kappa rootCount
  field_simp
  ring

theorem stationaryRemainder_rootCount (m : ℝ) (hm : 30 ≤ m) :
    stationaryRemainder (coeffA (rootCount m)) (coeffB (rootCount m)) (coeffC m)
      (criticalRatio m (rootCount m)) = 0 := by
  have hq := rootCount_gt_twice m hm
  rw [stationaryRemainder_formula m (rootCount m) (by linarith) (by linarith)
    (by linarith)]
  simp

theorem coeffA_pos (q : ℝ) (hq : 2 < q) : 0 < coeffA q := by
  unfold coeffA
  exact div_pos (mul_pos (by linarith) (by linarith)) (by positivity)

theorem coeffA_lt_one_sixth (q : ℝ) (hq : 2 < q) : coeffA q < 1 / 6 := by
  unfold coeffA
  apply (div_lt_iff₀ (show 0 < 6 * q ^ 2 by positivity)).mpr
  nlinarith

theorem coeffB_lt_one_half (q : ℝ) (hq : 0 < q) : coeffB q < 1 / 2 := by
  unfold coeffB
  apply (div_lt_iff₀ (show 0 < 2 * q by positivity)).mpr
  linarith

theorem coeffC_lt_one_half (m : ℝ) (hm : 0 < m) : coeffC m < 1 / 2 := by
  unfold coeffC
  apply (div_lt_iff₀ (show 0 < 2 * m by positivity)).mpr
  linarith

theorem one_fourth_le_coeffC (m : ℝ) (hm : 2 ≤ m) : 1 / 4 ≤ coeffC m := by
  unfold coeffC
  apply (le_div_iff₀ (show 0 < 2 * m by linarith)).mpr
  linarith

theorem coeffB_sub_three_coeffA (q : ℝ) (hq : q ≠ 0) :
    coeffB q - 3 * coeffA q = (q - 2) / (2 * q ^ 2) := by
  unfold coeffA coeffB
  field_simp
  ring

theorem coeffB_sub_coeffC (m q : ℝ) (hm : m ≠ 0) (hq : q ≠ 0) :
    coeffB q - coeffC m = (q - 2 * m) / (2 * m * q) := by
  unfold coeffB coeffC
  field_simp
  ring

theorem baseline_coefficient_bounds (m q : ℝ) (hm : 4 ≤ m) (hq : 2 * m < q) :
    0 < coeffA q ∧ 3 * coeffA q < coeffB q ∧ coeffC m < coeffB q ∧
      coeffA q < coeffC m := by
  have hm0 : 0 < m := by linarith
  have hq2 : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  refine ⟨coeffA_pos q hq2, ?_, ?_, ?_⟩
  · have hid := coeffB_sub_three_coeffA q (ne_of_gt hq0)
    have hpos : 0 < (q - 2) / (2 * q ^ 2) := by positivity
    linarith
  · have hid := coeffB_sub_coeffC m q (ne_of_gt hm0) (ne_of_gt hq0)
    have hpos : 0 < (q - 2 * m) / (2 * m * q) := by positivity
    linarith
  · have ha := coeffA_lt_one_sixth q hq2
    have hc := one_fourth_le_coeffC m (by linarith)
    linarith

theorem criticalMass_eq_ratio (m q : ℝ) (hq : q ≠ 0) (hsum : q + kappa m ≠ 0) :
    criticalMass m q = criticalRatio m q / (1 + criticalRatio m q) := by
  unfold criticalMass criticalRatio
  field_simp

theorem baselineMax_eq_stationaryValue (m q : ℝ) (hm : 2 < m) (hq : 0 < q) :
    baselineMax m q =
      stationaryValue (coeffA q) (coeffB q) (coeffC m) (criticalRatio m q) := by
  have hk := kappa_pos m hm
  have hx : 0 < criticalRatio m q := div_pos hk hq
  unfold baselineMax baseline
  rw [criticalMass_eq_ratio m q (ne_of_gt hq) (by positivity)]
  exact cubic_at_critical_mass _ _ _ _ (by positivity)

theorem criticalMass_pos (m q : ℝ) (hm : 2 < m) (hq : 0 < q) :
    0 < criticalMass m q := by
  unfold criticalMass
  exact div_pos (kappa_pos m hm) (add_pos hq (kappa_pos m hm))

theorem criticalMass_lt_one (m q : ℝ) (hm : 2 < m) (hq : 0 < q) :
    criticalMass m q < 1 := by
  unfold criticalMass
  apply (div_lt_one (add_pos hq (kappa_pos m hm))).mpr
  linarith

theorem baselineMax_strict_bounds (m : ℝ) (hm : 30 ≤ m) :
    coeffA (rootCount m) < baselineMax m (rootCount m) ∧
      baselineMax m (rootCount m) < 1 / 6 := by
  have hm2 : 2 < m := by linarith
  have hq2m := rootCount_gt_twice m hm
  have hq0 : 0 < rootCount m := by linarith
  obtain ⟨ha, hab, hbc, hac⟩ := baseline_coefficient_bounds m (rootCount m)
    (by linarith) hq2m
  constructor
  · rw [baselineMax_eq_stationaryValue m (rootCount m) hm2 hq0]
    exact stationaryValue_gt_a _ _ _ _ (div_pos (kappa_pos m hm2) hq0)
      hab hbc hac (stationaryRemainder_rootCount m hm)
  · unfold baselineMax baseline
    exact cubic_lt_one_sixth _ _ _ _
      (coeffA_lt_one_sixth _ (by linarith))
      (coeffB_lt_one_half _ hq0).le
      (coeffC_lt_one_half _ (by linarith)).le
      (criticalMass_pos _ _ hm2 hq0) (criticalMass_lt_one _ _ hm2 hq0)

theorem baseline_le_max (m t : ℝ) (hm : 30 ≤ m) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    baseline m (rootCount m) t ≤ baselineMax m (rootCount m) := by
  have hm2 : 2 < m := by linarith
  have hq2m := rootCount_gt_twice m hm
  have hq0 : 0 < rootCount m := by linarith
  obtain ⟨ha, hab, hbc, hac⟩ := baseline_coefficient_bounds m (rootCount m)
    (by linarith) hq2m
  rw [baselineMax_eq_stationaryValue m (rootCount m) hm2 hq0]
  exact cubic_le_stationaryValue _ _ _ _ _ ha
    (div_pos (kappa_pos m hm2) hq0) hab hbc hac
    (stationaryRemainder_rootCount m hm) ht0 ht1

theorem baseline_eq_max_iff (m t : ℝ) (hm : 30 ≤ m) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    baseline m (rootCount m) t = baselineMax m (rootCount m) ↔
      t = criticalMass m (rootCount m) := by
  have hm2 : 2 < m := by linarith
  have hq2m := rootCount_gt_twice m hm
  have hq0 : 0 < rootCount m := by linarith
  obtain ⟨ha, hab, hbc, hac⟩ := baseline_coefficient_bounds m (rootCount m)
    (by linarith) hq2m
  rw [baselineMax_eq_stationaryValue m (rootCount m) hm2 hq0,
    criticalMass_eq_ratio m (rootCount m) (ne_of_gt hq0)
      (ne_of_gt (add_pos hq0 (kappa_pos m hm2)))]
  exact cubic_eq_stationaryValue_iff _ _ _ _ _ ha
    (div_pos (kappa_pos m hm2) hq0) hab hbc hac
    (stationaryRemainder_rootCount m hm) ht0 ht1

/-- An explicit rational expression for the manuscript's threshold. -/
def rationalThreshold (m : ℚ) : ℚ :=
  let q := (m ^ 4 - 10 * m ^ 3 + 13 * m ^ 2 + 12 * m + 4) / 8
  let k := m / 2 - 1 / (m - 1)
  let t := k / (q + k)
  6 * ((q - 1) * (q - 2) / (6 * q ^ 2) * (1 - t) ^ 3 +
    (q - 2) / (2 * q) * (1 - t) ^ 2 * t +
    (m - 1) / (2 * m) * (1 - t) * t ^ 2)

theorem rationalThreshold_cast (m : ℚ) :
    (rationalThreshold m : ℝ) = 6 * baselineMax m (rootCount m) := by
  simp only [rationalThreshold, baselineMax, baseline, cubic, criticalMass,
    coeffA, coeffB, coeffC, rootCount, kappa]
  push_cast
  ring

theorem rationalThreshold_mem (m : ℚ) (hm : 30 ≤ m) :
    0 < rationalThreshold m ∧ rationalThreshold m < 1 := by
  have hmr : (30 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hlo, hhi⟩ := baselineMax_strict_bounds m hmr
  have hq := rootCount_gt_twice m hmr
  have ha := coeffA_pos (rootCount m) (by linarith)
  have hcast := rationalThreshold_cast m
  have hreal : (0 : ℝ) < (rationalThreshold m : ℝ) ∧
      (rationalThreshold m : ℝ) < 1 := by
    constructor <;> nlinarith
  exact_mod_cast hreal

end TuranUniversality.Weighted
