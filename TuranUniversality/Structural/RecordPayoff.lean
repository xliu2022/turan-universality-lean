module

public import TuranUniversality.Structural.Record
public import TuranUniversality.Density.Box

@[expose] public section

/-! # The seven actual record payoffs of Section 7 -/

namespace TuranUniversality.Structural.Label

open Density

def correction (p q : ℝ) : Label → ℝ
  | .inl j => if j = 3 then -p else if j = 4 then -4 * q else 0
  | .inr _ => q - p

def payoff (p q : ℝ) (l : Label) : ℝ := 160 * q + correction p q l

theorem correction_formula (p q : ℝ) (l : Label) :
    correction p q l =
      -p * truth (l.count = 3) - 4 * q * truth (l.count = 4) + q * truth (l.phase ≠ none) := by
  cases l with
  | inl j => fin_cases j <;> simp [correction, count, phase, truth]
  | inr a => simp [correction, count, phase, truth]; ring

theorem correction_bounds (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (l : Label) :
    -4 * q ≤ correction p q l ∧ correction p q l ≤ 4 * q := by
  cases l with
  | inl j =>
    fin_cases j <;> norm_num [correction] <;>
      (first | (constructor <;> linarith) | linarith)
  | inr a => change -4 * q ≤ q - p ∧ q - p ≤ 4 * q; constructor <;> linarith

theorem payoff_bounds (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (l : Label) :
    156 * q ≤ payoff p q l ∧ payoff p q l ≤ 161 * q := by
  have hc := correction_bounds p q hp hpq l
  have hu : correction p q l ≤ q := by
    cases l with
    | inl j => fin_cases j <;> norm_num [correction] <;> linarith
    | inr a => dsimp [correction]; linarith
  dsimp [payoff]
  constructor <;> linarith

end TuranUniversality.Structural.Label
