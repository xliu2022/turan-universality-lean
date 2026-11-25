module

public import TuranUniversality.Structural.RecordPayoff

@[expose] public section

/-! # The quartic switch and its unique maximizer

The factorization proves the global quartic bound directly.  Its zero-gap
case is included, and the phase score is the exact function in Section 7.
-/

namespace TuranUniversality.Structural.SwitchScalar

def value (δ α : ℝ) : ℝ := δ * α ^ 3 * (1 - α) - α ^ 4

noncomputable def optimalMass (δ : ℝ) : ℝ := 3 * δ / (4 * (1 + δ))

noncomputable def gain (δ : ℝ) : ℝ := 27 * δ ^ 4 / (256 * (1 + δ) ^ 3)

noncomputable def phaseScore (p q z : ℝ) : ℝ := 160 * q / 24 + (q / 6) * gain (z - p / q)

theorem deficit_factor (δ α : ℝ) (hδ : 0 ≤ δ) :
    gain δ - value δ α = (α - optimalMass δ) ^ 2 *
      ((1 + δ) * (α + δ / (4 * (1 + δ))) ^ 2 + δ ^ 2 / (8 * (1 + δ))) := by
  have hd : 1 + δ ≠ 0 := by linarith
  unfold gain value optimalMass
  field_simp [hd]
  ring

theorem value_le_gain (δ α : ℝ) (hδ : 0 ≤ δ) : value δ α ≤ gain δ := by
  have h : 0 ≤ gain δ - value δ α := by
    rw [deficit_factor δ α hδ]
    positivity
  linarith

theorem value_eq_gain_iff (δ α : ℝ) (hδ : 0 ≤ δ) :
    value δ α = gain δ ↔ α = optimalMass δ := by
  constructor
  · intro heq
    by_cases hz : δ = 0
    · simpa [hz, value, gain, optimalMass] using heq
    · have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
      have hp : 0 < (1 + δ) * (α + δ / (4 * (1 + δ))) ^ 2 +
          δ ^ 2 / (8 * (1 + δ)) := by positivity
      have hfactor := deficit_factor δ α hδ
      rw [heq, sub_self] at hfactor
      have hs : (α - optimalMass δ) ^ 2 = 0 :=
        (mul_eq_zero.mp hfactor.symm).resolve_right (ne_of_gt hp)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro heq
    have h := deficit_factor δ α hδ
    rw [heq, sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
    rw [heq]
    linarith

theorem value_at_optimal (δ : ℝ) (hδ : 0 ≤ δ) : value δ (optimalMass δ) = gain δ :=
  (value_eq_gain_iff δ (optimalMass δ) hδ).mpr rfl

theorem optimalMass_nonneg (δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ optimalMass δ := by
  unfold optimalMass
  positivity

theorem optimalMass_pos (δ : ℝ) (hδ : 0 < δ) : 0 < optimalMass δ := by
  unfold optimalMass
  positivity

theorem optimalMass_lt_three_quarters (δ : ℝ) (hδ : 0 ≤ δ) : optimalMass δ < 3 / 4 := by
  have hd : 0 < 4 * (1 + δ) := by positivity
  rw [optimalMass, div_lt_iff₀ hd]
  linarith

theorem neutralMass_gt_half (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 / 2 < 1 - optimalMass δ := by
  have hd : 0 < 4 * (1 + δ) := by positivity
  have hlt : optimalMass δ < 1 / 2 := by
    rw [optimalMass, div_lt_iff₀ hd]
    linarith
  linarith

theorem phaseScore_formula (p q z : ℝ) :
    phaseScore p q z = 160 * q / 24 +
      (9 * q / 512) * (z - p / q) ^ 4 / (1 + z - p / q) ^ 3 := by
  unfold phaseScore gain
  have h : 1 + (z - p / q) = 1 + z - p / q := by ring
  rw [h]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

theorem relaxed_le_phaseScore (p q z α : ℝ) (hq : 0 ≤ q) (hz : p / q ≤ z) :
    160 * q / 24 + (q / 6) * value (z - p / q) α ≤ phaseScore p q z := by
  have hm := mul_le_mul_of_nonneg_left
    (value_le_gain (z - p / q) α (sub_nonneg.mpr hz)) (show 0 ≤ q / 6 by positivity)
  simpa only [phaseScore, add_comm] using add_le_add_left hm (160 * q / 24)

end TuranUniversality.Structural.SwitchScalar
