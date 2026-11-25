module

public import TuranUniversality.Density.WeightedCollisions
public import TuranUniversality.Density.Box

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Elementary error bounds for finite weighted expectations -/

open scoped BigOperators

namespace TuranUniversality.Density

variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V]

theorem weightedMean_add (x : V → ℝ) (F G : (A → V) → ℝ) :
    weightedMean x (fun f => F f + G f) = weightedMean x F + weightedMean x G := by
  simp only [weightedMean, mul_add, Finset.sum_add_distrib]

theorem weightedMean_sub (x : V → ℝ) (F G : (A → V) → ℝ) :
    weightedMean x (fun f => F f - G f) = weightedMean x F - weightedMean x G := by
  simp only [weightedMean, mul_sub, Finset.sum_sub_distrib]

theorem weightedMean_abs_sub_le (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (F G : (A → V) → ℝ) :
    |weightedMean x F - weightedMean x G| ≤ weightedMean x (fun f => |F f - G f|) := by
  rw [← weightedMean_sub]
  unfold weightedMean
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro f _
  have hw : 0 ≤ productWeight x f := Finset.prod_nonneg (fun a _ => hx (f a))
  rw [abs_mul, abs_of_nonneg hw]

theorem weightedMean_collision_le [DecidableEq V] (x : V → ℝ) (hx : ProbabilityWeights x) :
    weightedMean x (fun f : A → V => truth (¬ Function.Injective f)) ≤
      (Fintype.card A : ℝ) ^ 2 * ∑ v, (x v) ^ 2 := by
  classical
  have h := (distinctWeight_subprob_bounds (A := A) x hx.1 hx.2.le).2
  rw [distinctWeight_deficit] at h
  convert h using 1
  apply weightedMean_congr
  intro f
  unfold truth
  split_ifs <;> rfl

end TuranUniversality.Density
