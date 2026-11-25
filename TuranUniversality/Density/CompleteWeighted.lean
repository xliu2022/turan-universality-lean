module

public import TuranUniversality.Weighted.Symmetric
public import TuranUniversality.Weighted.Ambiguity
public import TuranUniversality.Weighted.Marker

@[expose] public section

/-! # Complete hypergraph bounds with an upper bound on the number of vertices -/

namespace TuranUniversality.Weighted

open scoped BigOperators

theorem coeffA_mono (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) : coeffA a ≤ coeffA b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hbracket : 0 ≤ 3 * a * b - 2 * a - 2 * b := by
    have h1 : 0 ≤ a * (b - 2) := mul_nonneg ha0.le (by linarith)
    have h2 : 0 ≤ 2 * b * (a - 1) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hdiff : coeffA b - coeffA a =
      (b - a) * (3 * a * b - 2 * a - 2 * b) / (6 * a ^ 2 * b ^ 2) := by
    unfold coeffA
    field_simp
    ring
  have hnonneg : 0 ≤ (b - a) * (3 * a * b - 2 * a - 2 * b) /
      (6 * a ^ 2 * b ^ 2) := div_nonneg (mul_nonneg (sub_nonneg.mpr hab) hbracket) (by positivity)
  linarith

theorem root_triples_complete_bound {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (hcard : 4 ≤ I.card) (hz : ∀ v ∈ I, 0 ≤ z v) :
    elementary I z 3 ≤ coeffA I.card * (∑ v ∈ I, z v) ^ 3 := by
  have hcard0 : 0 < I.card := by omega
  have hq4 : (4 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard
  have hq0 : (0 : ℝ) < (I.card : ℝ) := by positivity
  have hs : 0 ≤ ∑ v ∈ I, z v := Finset.sum_nonneg hz
  have hV : 0 ≤ rootVariance I z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcenter := root_centered_identity I z hcard0
  have hcube := centeredCubes_le I z hz
  have hcoef : (2 / 3 : ℝ) / (I.card : ℝ) ≤ 1 / 6 :=
    (div_le_iff₀ hq0).mpr (by linarith)
  have hmult := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hs hV)
  simp only [div_eq_mul_inv] at hcenter hcube hmult ⊢
  nlinarith

theorem complete_triples_card_le {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (k : ℕ) (hk : 12 ≤ k)
    (hcard : I.card ≤ k) (hz : ∀ v ∈ I, 0 ≤ z v) :
    elementary I z 3 ≤ coeffA k * (∑ v ∈ I, z v) ^ 3 := by
  have hs : 0 ≤ ∑ v ∈ I, z v := Finset.sum_nonneg hz
  have hkreal : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := one_eighth_le_coeffA k hkreal
  by_cases hfour : 4 ≤ I.card
  · apply (root_triples_complete_bound I z hfour hz).trans
    apply mul_le_mul_of_nonneg_right (coeffA_mono _ _ (by exact_mod_cast hfour)
      (by exact_mod_cast hcard)) (pow_nonneg hs 3)
  · by_cases hthree : I.card = 3
    · have he : elementary I z 3 = ∏ v ∈ I, z v := by
        unfold elementary
        rw [← hthree, Finset.powersetCard_self, Finset.sum_singleton]
      obtain ⟨a, b, c, hab, hac, hbc, hI⟩ := Finset.card_eq_three.mp hthree
      have hza := hz a (by simp [hI])
      have hzb := hz b (by simp [hI])
      have hzc := hz c (by simp [hI])
      have hAM := triple_product_le_cube (z a) (z b) (z c) hza hzb hzc
      have hsum : (∑ v ∈ I, z v) = z a + z b + z c := by simp [hI, hab, hac, hbc, add_assoc]
      have hprod : (∏ v ∈ I, z v) = z a * z b * z c := by simp [hI, hab, hac, hbc, mul_assoc]
      rw [he, hprod, hsum]
      have hmul := mul_le_mul_of_nonneg_right ha (pow_nonneg (add_nonneg (add_nonneg hza hzb) hzc) 3)
      have hcube0 : 0 ≤ (z a + z b + z c) ^ 3 := by positivity
      nlinarith only [hAM, hmul, hcube0]
    · have hsmall : I.card < 3 := by omega
      have he : elementary I z 3 = 0 := by
        unfold elementary
        rw [Finset.powersetCard_eq_empty.mpr hsmall, Finset.sum_empty]
      rw [he]
      positivity

theorem complete_pairs_card_le {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (k : ℕ) (hk : 0 < k) (hcard : I.card ≤ k) :
    elementary I z 2 ≤ (1 - 1 / (k : ℝ)) * (∑ v ∈ I, z v) ^ 2 / 2 := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I z (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsq : 0 ≤ ∑ v ∈ I, (z v) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcards : (I.card : ℝ) ≤ k := by exact_mod_cast hcard
  have hprod := mul_le_mul_of_nonneg_left hcards hsq
  have hlower : (∑ v ∈ I, z v) ^ 2 / (k : ℝ) ≤ ∑ v ∈ I, (z v) ^ 2 :=
    (div_le_iff₀ hk0).mpr (by nlinarith)
  have hsecond := elementary_second_identity I z
  simp only [div_eq_mul_inv] at hlower ⊢
  nlinarith

end TuranUniversality.Weighted
