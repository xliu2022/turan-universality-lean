/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic

/-! # The density cost of deleting marked guard vertices -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

/-- With total deletion budget at most twice the individual cap, the
remaining product density is at least the square of the capped density. -/
theorem product_retention_bound {I : Type*} [Fintype I]
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) (t : I → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (htu : ∀ i, t i ≤ u)
    (hsum : ∑ i, t i ≤ 2 * u) :
    (1 - u) ^ 2 ≤ ∏ i, (1 - t i) := by
  have hupos : 0 < 1 - u := by linarith
  have htpos (i : I) : 0 < 1 - t i := by have := htu i; linarith
  have hpoint (i : I) : (t i / u) * Real.log (1 - u) ≤ Real.log (1 - t i) := by
    have hfrac0 : 0 ≤ t i / u := div_nonneg (ht0 i) (le_of_lt hu0)
    have hfrac1 : t i / u ≤ 1 := (div_le_one hu0).mpr (htu i)
    have h := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show 1 - u ∈ Set.Ioi 0 from hupos)
      (show 0 ≤ 1 - t i / u by linarith) hfrac0 (by ring)
    have heq : (1 - t i / u) * 1 + (t i / u) * (1 - u) = 1 - t i := by
      field_simp
      ring
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add, heq] using h
  have hfracsum : ∑ i, t i / u ≤ 2 := by
    rw [← Finset.sum_div]
    exact (div_le_iff₀ hu0).mpr hsum
  have hlogneg : Real.log (1 - u) ≤ 0 :=
    Real.log_nonpos (le_of_lt hupos) (by linarith)
  have hlogs : 2 * Real.log (1 - u) ≤ ∑ i, Real.log (1 - t i) := by
    calc
      2 * Real.log (1 - u) ≤ (∑ i, t i / u) * Real.log (1 - u) :=
        mul_le_mul_of_nonpos_right hfracsum hlogneg
      _ = ∑ i, (t i / u) * Real.log (1 - u) := Finset.sum_mul ..
      _ ≤ ∑ i, Real.log (1 - t i) := Finset.sum_le_sum (fun i _ => hpoint i)
  apply (Real.log_le_log_iff (sq_pos_of_pos hupos)
    (Finset.prod_pos (fun i _ => htpos i))).mp
  rw [Real.log_pow, Real.log_prod (fun i _ => ne_of_gt (htpos i))]
  norm_num
  exact hlogs

/-- The constant `12` in the guard sampling lemma. The hypotheses are
exactly the total deletion budget, individual cap, and retained-size
estimate used in the manuscript. -/
theorem guard_product_density_bound {I : Type*} [Fintype I]
    (q n : ℝ) (hq : 0 < q) (hn : 19 * q / 20 < n)
    (a N : I → ℝ) (ha0 : ∀ i, 0 ≤ a i) (hacap : ∀ i, a i ≤ q / 2)
    (habudget : ∑ i, a i ≤ q)
    (hN : ∀ i, n - 4 * a i / 3 ≤ N i) :
    (∏ i, n / N i) < 12 := by
  have hnpos : 0 < n := by linarith
  let u : ℝ := 2 * q / (3 * n)
  let t : I → ℝ := fun i => 4 * a i / (3 * n)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    apply (div_lt_one (show 0 < 3 * n by positivity)).mpr
    linarith
  have ht0 (i : I) : 0 ≤ t i := by
    dsimp [t]
    exact div_nonneg (mul_nonneg (by norm_num) (ha0 i)) (by positivity)
  have htu (i : I) : t i ≤ u := by
    dsimp [t, u]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := hacap i
    linarith
  have hsum : ∑ i, t i ≤ 2 * u := by
    calc
      ∑ i, t i = (4 * ∑ i, a i) / (3 * n) := by
        simp [t, Finset.sum_div, Finset.mul_sum]
      _ ≤ (4 * q) / (3 * n) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * u := by dsimp [u]; ring
  have hret := product_retention_bound u hu0 hu1 t ht0 htu hsum
  have hfrac (i : I) : 1 - t i ≤ N i / n := by
    apply (le_div_iff₀ hnpos).mpr
    have h := hN i
    dsimp [t]
    field_simp [ne_of_gt hnpos]
    nlinarith
  have hsmall : u < (40 / 57 : ℝ) := by
    dsimp [u]
    apply (div_lt_iff₀ (show 0 < 3 * n by positivity)).mpr
    linarith
  have hsquare : (1 / 12 : ℝ) < (1 - u) ^ 2 := by
    nlinarith [sq_nonneg (u - 40 / 57)]
  have hprod : (1 / 12 : ℝ) < ∏ i, N i / n := by
    apply hsquare.trans_le
    apply hret.trans
    exact Finset.prod_le_prod₀ (fun i _ => by have := htu i; linarith) (fun i _ => hfrac i)
  have hprodpos : 0 < ∏ i, N i / n := (by norm_num : (0 : ℝ) < 1 / 12).trans hprod
  have heq : (∏ i, n / N i) = 1 / (∏ i, N i / n) := by
    simp [Finset.prod_div_distrib]
  rw [heq]
  apply (div_lt_iff₀ hprodpos).mpr
  linarith

end TuranUniversality.Selector
