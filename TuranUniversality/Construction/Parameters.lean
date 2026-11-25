module

public import TuranUniversality.Construction.BlockCodes
public import TuranUniversality.Weighted.Ambiguity

@[expose] public section

/-! # Explicit integral root-count parameters

Writing the physical-type count as `4*a+30` makes the prescribed root count
an even polynomial with positive natural coefficients. This is the same
stationary baseline as in the manuscript, with all constants fixed independently
of the binary input.
-/

namespace TuranUniversality.Construction

open Weighted

def physicalCount (a : ℕ) : ℕ := 4 * a + 30

def rootNumber (a : ℕ) : ℕ :=
  32 * a ^ 4 + 880 * a ^ 3 + 9026 * a ^ 2 + 40896 * a + 69008

theorem physicalCount_ge (a : ℕ) : 30 ≤ physicalCount a := by unfold physicalCount; omega

theorem rootNumber_even (a : ℕ) : 2 ∣ rootNumber a := by
  refine ⟨16 * a ^ 4 + 440 * a ^ 3 + 4513 * a ^ 2 + 20448 * a + 34504, ?_⟩
  unfold rootNumber
  ring

theorem rootNumber_cast (a : ℕ) : (rootNumber a : ℝ) = rootCount (physicalCount a) := by
  unfold rootNumber physicalCount rootCount
  push_cast
  ring

theorem rootNumber_bounds (a : ℕ) :
    (physicalCount a : ℝ) ^ 4 / 12 ≤ rootNumber a ∧
      (rootNumber a : ℝ) ≤ (physicalCount a : ℝ) ^ 4 / 8 := by
  rw [rootNumber_cast]
  exact rootCount_bounds _ (by exact_mod_cast physicalCount_ge a)

theorem rootNumber_large (a : ℕ) : 4 * physicalCount a ≤ rootNumber a := by
  unfold physicalCount rootNumber
  omega

def chosenParameter (alphabetCard : ℕ) : ℕ := 10000000000000000 + alphabetCard

def codeCount (alphabetCard : ℕ) : ℕ :=
  physicalCount (chosenParameter alphabetCard) + alphabetCard - 1

theorem chosenParameter_large (A : ℕ) : 10000000000000000 ≤ chosenParameter A := by
  unfold chosenParameter
  omega

theorem codeCount_pos (A : ℕ) : 0 < codeCount A := by
  have := physicalCount_ge (chosenParameter A)
  unfold codeCount
  omega

theorem codeCount_le (A : ℕ) : codeCount A ≤ 2 * physicalCount (chosenParameter A) := by
  unfold codeCount physicalCount chosenParameter
  omega

def chosenBlocks (A : ℕ) : BlockParameters (codeCount A) (rootNumber (chosenParameter A)) :=
  makeBlockParameters _ _ (codeCount_pos A)
    (by have := rootNumber_large (chosenParameter A); have := codeCount_le A; omega)
    (rootNumber_even (chosenParameter A))

def threshold (A : ℕ) : ℚ := rationalThreshold (physicalCount (chosenParameter A))

theorem threshold_bounds (A : ℕ) : 0 < threshold A ∧ threshold A < 1 := by
  apply rationalThreshold_mem
  exact_mod_cast physicalCount_ge (chosenParameter A)

theorem threshold_cast (A : ℕ) :
    (threshold A : ℝ) = 6 * baselineMax (physicalCount (chosenParameter A))
      (rootNumber (chosenParameter A)) := by
  unfold threshold
  rw [rationalThreshold_cast]
  norm_cast
  rw [rootNumber_cast]

end TuranUniversality.Construction
