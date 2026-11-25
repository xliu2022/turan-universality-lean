module

public import TuranUniversality.Weighted.Grounded

/-! # The reward of the single data-only edge

Explicit polynomial proofs of the four endpoint cases in the nonhalting
estimate. The final lemma absorbs the reward using the finite-path constant 4.
-/

@[expose] public section

namespace TuranUniversality.Weighted

theorem triple_product_le_cube (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  have h1 : 0 ≤ (a + b - 2 * c) ^ 2 * (4 * a + 4 * b + c) := by positivity
  have h2 : 0 ≤ c * (a - b) ^ 2 := by positivity
  nlinarith

theorem one_ambiguous_polynomial (w η : ℝ) (hw : 0 ≤ w) (hη : 0 ≤ η) :
    w * η ^ 2 ≤ w ^ 3 / 27 + 2 * η ^ 3 := by
  have h : 0 ≤ (w - 3 * η) ^ 2 * (w + 6 * η) := by positivity
  nlinarith

theorem two_ambiguous_polynomial (w η : ℝ) (hw : 0 ≤ w) (hη : 0 ≤ η) :
    w ^ 2 * η / 4 ≤ w ^ 3 / 27 + 2 * η ^ 3 := by
  have h : 0 ≤ (2 * w - 9 * η) ^ 2 * (4 * w + 9 * η) := by positivity
  have hη3 : 0 ≤ η ^ 3 := by positivity
  nlinarith

theorem all_ambiguous_reward (a b c w η : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hw : a + b + c ≤ w) :
    a * b * c ≤ w ^ 3 / 27 + 2 * η ^ 3 := by
  have hAM := triple_product_le_cube a b c ha hb hc
  have hpow : (a + b + c) ^ 3 ≤ w ^ 3 := by gcongr
  have hη3 : 0 ≤ η ^ 3 := by positivity
  nlinarith

/-- Two ambiguous endpoints and one declared endpoint. -/
theorem one_declared_reward (a b c w η : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hw : a + b ≤ w) (hcη : c ≤ η) :
    a * b * c ≤ w ^ 3 / 27 + 2 * η ^ 3 := by
  have hw0 : 0 ≤ w := by linarith
  have hsum0 : 0 ≤ a + b := by linarith
  have hsq : (a + b) ^ 2 ≤ w ^ 2 := (sq_le_sq₀ hsum0 hw0).mpr hw
  have hab : a * b ≤ w ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
  have hprod : a * b * c ≤ w ^ 2 * η / 4 := by
    have h := mul_le_mul hab hcη hc (by positivity : 0 ≤ w ^ 2 / 4)
    nlinarith
  exact hprod.trans (two_ambiguous_polynomial w η hw0 hη)

/-- One ambiguous endpoint and two declared endpoints. -/
theorem two_declared_reward (a b c w η : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hw : a ≤ w) (hbη : b ≤ η) (hcη : c ≤ η) :
    a * b * c ≤ w ^ 3 / 27 + 2 * η ^ 3 := by
  have hw0 : 0 ≤ w := ha.trans hw
  have hbc : b * c ≤ η ^ 2 := by
    nlinarith [mul_le_mul hbη hcη hc hη]
  have hprod : a * b * c ≤ w * η ^ 2 := by
    have h := mul_le_mul hw hbc (mul_nonneg hb hc) hw0
    nlinarith
  exact hprod.trans (one_ambiguous_polynomial w η hw0 hη)

theorem all_declared_reward (a b c w η : ℝ)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hw : 0 ≤ w) (hη : 0 ≤ η)
    (haη : a ≤ η) (hbη : b ≤ η) (hcη : c ≤ η) :
    a * b * c ≤ w ^ 3 / 27 + 2 * η ^ 3 := by
  have hab : a * b ≤ η ^ 2 := by nlinarith [mul_le_mul haη hbη hb hη]
  have hprod : a * b * c ≤ η ^ 3 := by
    nlinarith [mul_le_mul hab hcη hc (sq_nonneg η)]
  have hw3 : 0 ≤ w ^ 3 := by positivity
  have hη3 : 0 ≤ η ^ 3 := by positivity
  nlinarith

/-- The defect penalty absorbs every declared-endpoint reward when the
grounded estimate is used with constant 4. -/
theorem marker_defect_absorption (M w η t D α : ℝ)
    (hD : 0 ≤ D) (hreward : M ≤ w ^ 3 / 27 + 2 * η ^ 3)
    (hgrounded : η ^ 3 ≤ 4 * t * D) (hα : 8 * t ≤ α) :
    M - α * D ≤ w ^ 3 / 27 := by
  have hpenalty := mul_le_mul_of_nonneg_right hα hD
  nlinarith

end TuranUniversality.Weighted
