module

public import Mathlib

/-!
# A finite path estimate for the matching defect

This gives the constant `4` version of the grounded estimate used in the
nonhalting bound. The manuscript's sharper constant is `9/4`; the numerical
absorption argument has enough slack for `4`. The proof below uses only finite
sums, clipping, telescoping squares and Cauchy--Schwarz.
-/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

def pathMass (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), u i

def pathEnergy (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (u i - u (i + 1)) ^ 2

theorem sum_path_differences (u : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (u i - u (i + 1))) = u 0 - u n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sum_path_adjacent (u : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (u i + u (i + 1))) =
      2 * pathMass u n - u 0 - u n := by
  unfold pathMass
  rw [Finset.sum_add_distrib]
  have hleft := Finset.sum_range_succ u n
  have hright := Finset.sum_range_succ' u n
  linarith

theorem pathMass_nonneg (u : ℕ → ℝ) (n : ℕ)
    (hu : ∀ i ≤ n, 0 ≤ u i) : 0 ≤ pathMass u n := by
  exact Finset.sum_nonneg fun i hi => hu i (by simpa using Finset.mem_range.mp hi)

theorem pathEnergy_nonneg (u : ℕ → ℝ) (n : ℕ) : 0 ≤ pathEnergy u n := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The path estimate when the initial weight dominates the path. -/
theorem grounded_path_bound_of_bounded (u : ℕ → ℝ) (n : ℕ) (μ D : ℝ)
    (hu : ∀ i ≤ n, 0 ≤ u i) (hbound : ∀ i ≤ n, u i ≤ u 0)
    (hend : u n = 0) (hmass : pathMass u n ≤ μ) (henergy : pathEnergy u n ≤ D) :
    (u 0) ^ 3 ≤ 4 * μ * D := by
  have ha : 0 ≤ u 0 := hu 0 (Nat.zero_le n)
  have hμ : 0 ≤ μ := (pathMass_nonneg u n hu).trans hmass
  have hD : 0 ≤ D := (pathEnergy_nonneg u n).trans henergy
  have hadj : (∑ i ∈ Finset.range n, (u i + u (i + 1))) ≤ 2 * μ := by
    rw [sum_path_adjacent u n, hend]
    linarith
  have hsquares : (∑ i ∈ Finset.range n, (u i + u (i + 1)) ^ 2) ≤
      4 * u 0 * μ := by
    calc
      (∑ i ∈ Finset.range n, (u i + u (i + 1)) ^ 2) ≤
          ∑ i ∈ Finset.range n, (2 * u 0) * (u i + u (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
        have hi1n : i + 1 ≤ n := Finset.mem_range.mp hi
        have hi0 := hu i hin
        have hi10 := hu (i + 1) hi1n
        have hib := hbound i hin
        have hi1b := hbound (i + 1) hi1n
        calc
          (u i + u (i + 1)) ^ 2 = (u i + u (i + 1)) * (u i + u (i + 1)) := by ring
          _ ≤ (2 * u 0) * (u i + u (i + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = (2 * u 0) * ∑ i ∈ Finset.range n, (u i + u (i + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * u 0) * (2 * μ) := mul_le_mul_of_nonneg_left hadj (by positivity)
      _ = 4 * u 0 * μ := by ring
  have htel : (∑ i ∈ Finset.range n,
      (u i - u (i + 1)) * (u i + u (i + 1))) = (u 0) ^ 2 := by
    calc
      (∑ i ∈ Finset.range n, (u i - u (i + 1)) * (u i + u (i + 1))) =
          ∑ i ∈ Finset.range n, ((u i) ^ 2 - (u (i + 1)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (u 0) ^ 2 - (u n) ^ 2 := sum_path_differences (fun i => (u i) ^ 2) n
      _ = (u 0) ^ 2 := by rw [hend]; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun i => u i - u (i + 1)) (fun i => u i + u (i + 1))
  rw [htel] at hcs
  have hsquares0 : 0 ≤ ∑ i ∈ Finset.range n, (u i + u (i + 1)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfourth : ((u 0) ^ 2) ^ 2 ≤ u 0 * (4 * μ * D) := by
    calc
      ((u 0) ^ 2) ^ 2 ≤ pathEnergy u n *
          ∑ i ∈ Finset.range n, (u i + u (i + 1)) ^ 2 := hcs
      _ ≤ D * ∑ i ∈ Finset.range n, (u i + u (i + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_right henergy hsquares0
      _ ≤ D * (4 * u 0 * μ) := mul_le_mul_of_nonneg_left hsquares hD
      _ = u 0 * (4 * μ * D) := by ring
  rcases eq_or_lt_of_le ha with haz | hap
  · calc
      (u 0) ^ 3 = 0 := by rw [← haz]; norm_num
      _ ≤ 4 * μ * D := mul_nonneg (mul_nonneg (by norm_num) hμ) hD
  · have hmul : u 0 * (u 0) ^ 3 ≤ u 0 * (4 * μ * D) := by
      nlinarith [hfourth]
    exact le_of_mul_le_mul_left hmul hap

/-- Clipping from above cannot increase the square of a difference. -/
theorem min_sq_difference_le (a x y : ℝ) :
    (min a x - min a y) ^ 2 ≤ (x - y) ^ 2 := by
  by_cases hx : x ≤ a
  · by_cases hy : y ≤ a
    · rw [min_eq_right hx, min_eq_right hy]
    · have hay : a ≤ y := le_of_not_ge hy
      rw [min_eq_right hx, min_eq_left hay]
      have hs : (a - x) ^ 2 ≤ (y - x) ^ 2 :=
        (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
      nlinarith
  · have hax : a ≤ x := le_of_not_ge hx
    by_cases hy : y ≤ a
    · rw [min_eq_left hax, min_eq_right hy]
      exact (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
    · have hay : a ≤ y := le_of_not_ge hy
      rw [min_eq_left hax, min_eq_left hay]
      simpa using sq_nonneg (x - y)

/-- The finite grounded estimate, with the constant `4`.

No monotonicity or initial-maximum condition is imposed on the path weights.
The hypotheses are exactly the bounds needed when a simple path is extracted
from a relation component and its missing incidence is completed by a zero leaf.
-/
theorem grounded_path_bound (u : ℕ → ℝ) (n : ℕ) (μ D : ℝ)
    (hu : ∀ i ≤ n, 0 ≤ u i) (hend : u n = 0)
    (hmass : pathMass u n ≤ μ) (henergy : pathEnergy u n ≤ D) :
    (u 0) ^ 3 ≤ 4 * μ * D := by
  let v : ℕ → ℝ := fun i => min (u 0) (u i)
  have ha : 0 ≤ u 0 := hu 0 (Nat.zero_le n)
  have hv0 : v 0 = u 0 := min_self _
  have hv : ∀ i ≤ n, 0 ≤ v i := by
    intro i hi
    exact le_min ha (hu i hi)
  have hvbound : ∀ i ≤ n, v i ≤ v 0 := by
    intro i hi
    rw [hv0]
    exact min_le_left _ _
  have hvend : v n = 0 := by
    dsimp [v]
    rw [hend, min_eq_right ha]
  have hvmass : pathMass v n ≤ μ := by
    apply le_trans _ hmass
    exact Finset.sum_le_sum fun i hi => min_le_right _ _
  have hvenergy : pathEnergy v n ≤ D := by
    apply le_trans _ henergy
    exact Finset.sum_le_sum fun i hi => min_sq_difference_le (u 0) (u i) (u (i + 1))
  have h := grounded_path_bound_of_bounded v n μ D hv hvbound hvend hvmass hvenergy
  simpa only [hv0] using h

end TuranUniversality.Weighted
