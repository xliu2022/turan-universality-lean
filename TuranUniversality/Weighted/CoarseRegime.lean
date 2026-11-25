module

public import TuranUniversality.Weighted.Coarse

/-! # Small data mass and root variance above the baseline -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

theorem coarse_mass_small (q u t : ℝ) (hu : 8 ≤ u) (hqu : q = u ^ 2)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hcoarse : 0 ≤ t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54) :
    t < 4 / u := by
  have hu0 : 0 < u := by linarith
  have hq0 : 0 < q := by rw [hqu]; positivity
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hid : 54 * q * (t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54) =
      27 * t + 54 * t ^ 2 - 7 * q * t ^ 3 := by
    field_simp
    ring
  have hpoly : 0 ≤ 27 * t + 54 * t ^ 2 - 7 * q * t ^ 3 := by
    rw [← hid]
    positivity
  by_contra hbig
  have h4 : 4 ≤ u * t := by
    have h := (div_le_iff₀ hu0).mp (le_of_not_gt hbig)
    nlinarith
  have ht0 : 0 < t := by nlinarith
  have hsq : 16 ≤ q * t ^ 2 := by
    rw [hqu]
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) (by nlinarith : 0 ≤ u * t + 4)]
  have hcube := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 7 * t)
  have ht2 := mul_le_mul_of_nonneg_left ht1 ht
  nlinarith

theorem coarse_variance_small (q u s t V : ℝ) (hu : 8 ≤ u) (hqu : q = u ^ 2)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hV : 0 ≤ V)
    (hcoarse : s / 12 * V ≤ t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54) :
    t < 4 / u ∧ 1 / 2 < s ∧ V ≤ 96 / (q * u) := by
  have hu0 : 0 < u := by linarith
  have hq0 : 0 < q := by rw [hqu]; positivity
  have hqu0 : 0 < q * u := mul_pos hq0 hu0
  have hcoarse0 : 0 ≤ t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54 :=
    (mul_nonneg (div_nonneg hs (by norm_num)) hV).trans hcoarse
  have htSmall := coarse_mass_small q u t hu hqu ht (by linarith) hcoarse0
  have h4 : u * t < 4 := by
    have h := (lt_div_iff₀ hu0).mp htSmall
    nlinarith
  have htHalf : t < 1 / 2 := by nlinarith
  have hsHalf : 1 / 2 < s := by linarith
  have hpoly : u * t / 2 + u * t ^ 2 ≤ 4 := by
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt h4) ht
    nlinarith
  have hF : t / (2 * q) + t ^ 2 / q ≤ 4 / (q * u) := by
    apply (le_div_iff₀ hqu0).mpr
    have hident : (t / (2 * q) + t ^ 2 / q) * (q * u) = u * t / 2 + u * t ^ 2 := by
      field_simp
    rw [hident]
    exact hpoly
  have hV24 : V / 24 ≤ s / 12 * V := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s - 1 / 2) hV]
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  refine ⟨htSmall, hsHalf, ?_⟩
  have hcomb : V / 24 ≤ 4 / (q * u) := by linarith
  have h96 : 24 * (4 / (q * u)) = 96 / (q * u) := by ring
  linarith

universe u v w
variable {Roots : Type u} {Data : Type v} {Code : Type w}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Data] [Fintype Data] [Fintype Code]

/-- The two smallness estimates used in the weighted compiler follow from
the graph polynomial, H1, one marker, and the threshold comparison. -/
theorem CodeSystem.fine_regime (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (u : ℝ)
    (hu : 8 ≤ u) (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1)
    (hH1 : C.HasCandidates M) (hone : M.dataTriples.card ≤ 1)
    (hP : coeffA (Fintype.card Roots) ≤ M.toRGraph.edgePolynomial (Sum.elim z x)) :
    (∑ d, x d) < 4 / u ∧ 1 / 2 < (∑ r, z r) ∧
      rootVariance Finset.univ z ≤ 96 / ((Fintype.card Roots : ℝ) * u) := by
  have hq : 8 ≤ Fintype.card Roots := by
    have hqr : (8 : ℝ) ≤ Fintype.card Roots := by nlinarith
    exact_mod_cast hqr
  have hqpos : (0 : ℝ) < Fintype.card Roots := by exact_mod_cast (by omega : 0 < Fintype.card Roots)
  have hs : 0 ≤ ∑ r, z r := Finset.sum_nonneg fun r _ => hz r
  have ht : 0 ≤ ∑ d, x d := Finset.sum_nonneg fun d _ => hx d
  have hV : 0 ≤ rootVariance Finset.univ z :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  have hC := C.edgePolynomial_coarse_bound M z x hq hz hx hH1 hone
  have hrelax := coarse_cubic_relaxation (Fintype.card Roots : ℝ) (∑ d, x d)
    hqpos ht (by linarith)
  have hsEq : (∑ r, z r) = 1 - ∑ d, x d := by linarith
  rw [← hsEq] at hrelax
  apply coarse_variance_small _ u _ _ _ hu hqu hs ht hnorm hV
  linarith

end TuranUniversality.Weighted
