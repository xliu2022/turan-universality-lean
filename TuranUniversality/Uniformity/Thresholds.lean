module

public import TuranUniversality.Reduction.Universality
public import TuranUniversality.Uniformity.MassOptimization

@[expose] public section

/-! # Rational thresholds in every uniformity -/

namespace TuranUniversality.Uniformity

/-- The factor converting the ordinary three-uniform density to uniformity `r`. -/
def densityScale (r : ℕ) : ℚ := 27 * (r.factorial : ℚ) / (6 * (r : ℚ) ^ r)

@[simp] theorem densityScale_three : densityScale 3 = 1 := by norm_num [densityScale]

theorem densityScale_pos {r : ℕ} (hr : 0 < r) : 0 < densityScale r := by
  unfold densityScale
  have hf : (0 : ℚ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hp : (0 : ℚ) < r := by exact_mod_cast hr
  positivity

theorem densityScale_succ (r : ℕ) (hr : 0 < r) :
    densityScale (r + 1) = densityScale r * ((r : ℚ) / (r + 1 : ℚ)) ^ r := by
  have h0 : (r : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have h1 : (r + 1 : ℚ) ≠ 0 := by positivity
  simp only [densityScale, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, div_pow]
  field_simp
  <;> ring

theorem densityScale_succ_le (r : ℕ) (hr : 0 < r) : densityScale (r + 1) ≤ densityScale r := by
  rw [densityScale_succ r hr]
  have h0 : (0 : ℚ) ≤ (r : ℚ) / (r + 1 : ℚ) := by positivity
  have h1 : (r : ℚ) / (r + 1 : ℚ) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℚ) < r + 1)).mpr
    linarith
  have hp : ((r : ℚ) / (r + 1 : ℚ)) ^ r ≤ 1 := pow_le_one₀ h0 h1
  have hscale := (densityScale_pos hr).le
  nlinarith

theorem densityScale_le_one {r : ℕ} (hr : 3 ≤ r) : densityScale r ≤ 1 := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ n hn ih => exact le_trans (densityScale_succ_le n (by omega)) ih

theorem densityScale_cast (r : ℕ) :
    (densityScale r : ℝ) = 27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r) := by
  simp [densityScale]

/-- One rational threshold for each uniformity; the theorem concerns `r ≥ 3`. -/
noncomputable def thresholdR (r : ℕ) : ℚ := densityScale r * tau3

@[simp] theorem thresholdR_three : thresholdR 3 = tau3 := by simp [thresholdR]

theorem thresholdR_bounds {r : ℕ} (hr : 3 ≤ r) : 0 < thresholdR r ∧ thresholdR r < 1 := by
  have hc := densityScale_pos (show 0 < r by omega)
  have hle := densityScale_le_one hr
  have ht := tau3_bounds
  constructor
  · exact mul_pos hc ht.1
  · change densityScale r * tau3 < 1
    calc
      densityScale r * tau3 ≤ 1 * tau3 := mul_le_mul_of_nonneg_right hle ht.1.le
      _ < 1 := by simpa using ht.2

theorem thresholdR_cast (r : ℕ) :
    (thresholdR r : ℝ) =
      (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) * (tau3 : ℝ) := by
  simp only [thresholdR, Rat.cast_mul, densityScale_cast]

end TuranUniversality.Uniformity
