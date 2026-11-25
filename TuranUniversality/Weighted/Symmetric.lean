module

public import TuranUniversality.Weighted.Baseline

/-! # Finite elementary symmetric sums and root variance

The symmetric sums are defined by genuine subsets, so these identities apply
directly to the edge polynomial of a complete root hypergraph.
-/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

noncomputable def elementary {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (k : ℕ) : ℝ :=
  ∑ e ∈ I.powersetCard k, ∏ v ∈ e, z v

theorem multiset_esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

theorem multiset_esymm_cons (a : ℝ) (s : Multiset ℝ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
  rw [← Multiset.sum_map_mul_left]

theorem multiset_second_identity (s : Multiset ℝ) :
    2 * s.esymm 2 = s.sum ^ 2 - (s.map (fun z => z ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [multiset_esymm_cons a s 1, multiset_esymm_one]
    simp only [Multiset.sum_cons, Multiset.map_cons]
    nlinarith

theorem multiset_third_identity (s : Multiset ℝ) :
    6 * s.esymm 3 = s.sum ^ 3 - 3 * s.sum * (s.map (fun z => z ^ 2)).sum +
      2 * (s.map (fun z => z ^ 3)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [multiset_esymm_cons a s 2]
    simp only [Multiset.sum_cons, Multiset.map_cons]
    have hsecond := multiset_second_identity s
    linear_combination ih + 3 * a * hsecond

theorem elementary_second_identity {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) :
    2 * elementary I z 2 = (∑ v ∈ I, z v) ^ 2 - ∑ v ∈ I, (z v) ^ 2 := by
  have h := multiset_second_identity (I.val.map z)
  simpa only [Finset.esymm_map_val, Multiset.map_map, Function.comp_apply,
    Finset.sum_map_val, elementary] using h

theorem elementary_third_identity {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) :
    6 * elementary I z 3 = (∑ v ∈ I, z v) ^ 3 -
      3 * (∑ v ∈ I, z v) * (∑ v ∈ I, (z v) ^ 2) + 2 * ∑ v ∈ I, (z v) ^ 3 := by
  have h := multiset_third_identity (I.val.map z)
  simpa only [Finset.esymm_map_val, Multiset.map_map, Function.comp_apply,
    Finset.sum_map_val, elementary] using h

noncomputable def rootVariance {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) : ℝ :=
  ∑ v ∈ I, (z v - (∑ j ∈ I, z j) / (I.card : ℝ)) ^ 2

noncomputable def centeredCubes {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) : ℝ :=
  ∑ v ∈ I, (z v - (∑ j ∈ I, z j) / (I.card : ℝ)) ^ 3

theorem second_moment_shift {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (c : ℝ) :
    (∑ v ∈ I, (z v) ^ 2) =
      (∑ v ∈ I, (z v - c) ^ 2) + 2 * c * (∑ v ∈ I, z v) - (I.card : ℝ) * c ^ 2 := by
  calc
    (∑ v ∈ I, (z v) ^ 2) = ∑ v ∈ I, ((z v - c) ^ 2 + 2 * c * z v - c ^ 2) := by
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const]
      simp only [nsmul_eq_mul]

theorem third_moment_shift {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (c : ℝ) :
    (∑ v ∈ I, (z v) ^ 3) =
      (∑ v ∈ I, (z v - c) ^ 3) + 3 * c * (∑ v ∈ I, (z v - c) ^ 2) +
        3 * c ^ 2 * (∑ v ∈ I, z v) - 2 * (I.card : ℝ) * c ^ 3 := by
  calc
    (∑ v ∈ I, (z v) ^ 3) =
        ∑ v ∈ I, ((z v - c) ^ 3 + 3 * c * (z v - c) ^ 2 + 3 * c ^ 2 * z v - 2 * c ^ 3) := by
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const]
      simp only [nsmul_eq_mul]
      ring

theorem root_centered_identity {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (hcard : 0 < I.card) :
    elementary I z 3 = coeffA I.card * (∑ v ∈ I, z v) ^ 3 -
      ((∑ v ∈ I, z v) / 2 - (∑ v ∈ I, z v) / (I.card : ℝ)) * rootVariance I z +
        centeredCubes I z / 3 := by
  let s := ∑ v ∈ I, z v
  let q : ℝ := I.card
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (Nat.ne_of_gt hcard)
  have h2base := second_moment_shift I z (s / q)
  change (∑ v ∈ I, (z v) ^ 2) =
    rootVariance I z + 2 * (s / q) * s - q * (s / q) ^ 2 at h2base
  have h2 : (∑ v ∈ I, (z v) ^ 2) = rootVariance I z + s ^ 2 / q := by
    rw [h2base]
    field_simp
    ring
  have h3base := third_moment_shift I z (s / q)
  change (∑ v ∈ I, (z v) ^ 3) = centeredCubes I z + 3 * (s / q) * rootVariance I z +
    3 * (s / q) ^ 2 * s - 2 * q * (s / q) ^ 3 at h3base
  have h3 : (∑ v ∈ I, (z v) ^ 3) =
      centeredCubes I z + 3 * (s / q) * rootVariance I z + s ^ 3 / q ^ 2 := by
    rw [h3base]
    field_simp
    ring
  have hE := elementary_third_identity I z
  change 6 * elementary I z 3 = s ^ 3 - 3 * s * (∑ v ∈ I, (z v) ^ 2) +
    2 * (∑ v ∈ I, (z v) ^ 3) at hE
  rw [h2, h3] at hE
  change elementary I z 3 = coeffA q * s ^ 3 - (s / 2 - s / q) * rootVariance I z +
    centeredCubes I z / 3
  calc
    elementary I z 3 = (s ^ 3 - 3 * s * (rootVariance I z + s ^ 2 / q) +
        2 * (centeredCubes I z + 3 * (s / q) * rootVariance I z + s ^ 3 / q ^ 2)) / 6 := by
      linarith
    _ = _ := by
      unfold coeffA
      field_simp
      ring

theorem centeredCubes_le {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (hz : ∀ v ∈ I, 0 ≤ z v) :
    centeredCubes I z ≤ (∑ v ∈ I, z v) * (1 - 1 / (I.card : ℝ)) * rootVariance I z := by
  unfold centeredCubes rootVariance
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hsingle : z v ≤ ∑ j ∈ I, z j := Finset.single_le_sum hz hv
  have hdelta : z v - (∑ j ∈ I, z j) / (I.card : ℝ) ≤
      (∑ j ∈ I, z j) * (1 - 1 / (I.card : ℝ)) := by
    calc
      z v - (∑ j ∈ I, z j) / (I.card : ℝ) ≤
          (∑ j ∈ I, z j) - (∑ j ∈ I, z j) / (I.card : ℝ) := sub_le_sub_right hsingle _
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_right hdelta
    (sq_nonneg (z v - (∑ j ∈ I, z j) / (I.card : ℝ)))
  nlinarith

/-- The complete root triple contribution, including its variance penalty. -/
theorem root_triples_variance_bound {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (hcard : 8 ≤ I.card) (hz : ∀ v ∈ I, 0 ≤ z v) :
    elementary I z 3 ≤ coeffA I.card * (∑ v ∈ I, z v) ^ 3 -
      (∑ v ∈ I, z v) / 12 * rootVariance I z := by
  have hcard0 : 0 < I.card := by omega
  have hq8 : (8 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard
  have hq0 : (0 : ℝ) < (I.card : ℝ) := by positivity
  have hs : 0 ≤ ∑ v ∈ I, z v := Finset.sum_nonneg hz
  have hV : 0 ≤ rootVariance I z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcenter := root_centered_identity I z hcard0
  have hcube := centeredCubes_le I z hz
  have hcoef : (2 / 3 : ℝ) / (I.card : ℝ) ≤ 1 / 12 :=
    (div_le_iff₀ hq0).mpr (by linarith)
  have hmult := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hs hV)
  simp only [div_eq_mul_inv] at hcenter hcube hmult ⊢
  nlinarith

theorem root_pairs_bound {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) :
    elementary I z 2 ≤ (∑ v ∈ I, z v) ^ 2 / 2 := by
  have h := elementary_second_identity I z
  have hsq : 0 ≤ ∑ v ∈ I, (z v) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

end TuranUniversality.Weighted
