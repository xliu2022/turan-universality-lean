module

public import TuranUniversality.Weighted.OneRootSum
public import TuranUniversality.Weighted.CoarseRegime

/-! # Mass of the actual indexed root copies -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

theorem embedded_sum_variance {A Roots : Type*} [Fintype A]
    [Fintype Roots] [DecidableEq Roots] (f : A ↪ Roots) (z : Roots → ℝ) :
    ((∑ a, z (f a)) - (Fintype.card A : ℝ) *
      ((∑ r, z r) / (Fintype.card Roots : ℝ))) ^ 2 ≤
      (Fintype.card A : ℝ) * rootVariance Finset.univ z := by
  let center := (∑ r, z r) / (Fintype.card Roots : ℝ)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun a : A => z (f a) - center)
  have hsub : (∑ a, (z (f a) - center) ^ 2) ≤ rootVariance Finset.univ z := by
    have himage : (∑ a, (z (f a) - center) ^ 2) =
        ∑ r ∈ Finset.univ.image f, (z r - center) ^ 2 := by
      symm
      apply Finset.sum_image
      exact fun _ _ _ _ he => f.injective he
    rw [himage]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro r hr hnot
    exact sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
  exact hcs.trans hmul

/-- Numerical copy-mass estimates, with no square roots in the proof. -/
theorem copy_mass_bounds (q u n s V Z : ℝ) (hu : 0 < u) (hqu : q = u ^ 2)
    (hnlo : 2048 * u ≤ n) (hnhi : n ≤ 2049 * u) (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1)
    (hV : V ≤ 96 / (q * u)) (hZ : (Z - n * s / q) ^ 2 ≤ n * V) :
    512 / u ≤ Z ∧ Z ≤ 3000 / u := by
  have hq : 0 < q := by rw [hqu]; positivity
  have hune : u ≠ 0 := ne_of_gt hu
  have hqne : q ≠ 0 := ne_of_gt hq
  have hn : 0 ≤ n := by nlinarith
  have hs : 0 ≤ s := by linarith
  have hmeanlo : 1024 ≤ n * s / u := by
    apply (le_div_iff₀ hu).mpr
    have hmul := mul_le_mul_of_nonneg_right hnlo hs
    nlinarith
  have hmeanhi : n * s / u ≤ 2049 := by
    apply (div_le_iff₀ hu).mpr
    have hmul := mul_le_mul_of_nonneg_left hshi hn
    nlinarith
  have hVar : q * (n * V) ≤ 196704 := by
    have hmul := mul_le_mul_of_nonneg_left hV (mul_nonneg (le_of_lt hq) hn)
    have hid : (q * n) * (96 / (q * u)) = 96 * n / u := by
      field_simp
    have hn' : 96 * n / u ≤ 196704 := by
      apply (div_le_iff₀ hu).mpr
      nlinarith
    rw [hid] at hmul
    nlinarith
  have hdiff : (u * Z - n * s / u) ^ 2 ≤ 196704 := by
    have hmul := mul_le_mul_of_nonneg_left hZ (le_of_lt hq)
    have hid : q * (Z - n * s / q) ^ 2 = (u * Z - n * s / u) ^ 2 := by
      rw [hqu]
      field_simp
    rw [hid] at hmul
    exact hmul.trans hVar
  constructor
  · apply (div_le_iff₀ hu).mpr
    by_contra hnot
    have hsmall : Z * u < 512 := lt_of_not_ge hnot
    have hgap : 512 < n * s / u - u * Z := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ n * s / u - u * Z - 512)
      (by linarith : 0 ≤ n * s / u - u * Z + 512)]
  · apply (le_div_iff₀ hu).mpr
    by_contra hnot
    have hlarge : 3000 < Z * u := lt_of_not_ge hnot
    have hgap : 951 < u * Z - n * s / u := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ u * Z - n * s / u - 951)
      (by linarith : 0 ≤ u * Z - n * s / u + 951)]

namespace CompilerSignature

universe u v w
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots]

def copyEmbedding (S : CompilerSignature Roots Code Kinds L) (e : Fin 3) : Fin L ↪ Roots where
  toFun j := S.copyRoot (e, j)
  inj' := by
    intro i j hij
    exact congrArg Prod.snd (S.copyRoot.injective hij)

theorem copyMass_variance (S : CompilerSignature Roots Code Kinds L) (z : Roots → ℝ) (e : Fin 3) :
    (S.copyMass z e - (L : ℝ) * (∑ r, z r) / (Fintype.card Roots : ℝ)) ^ 2 ≤
      (L : ℝ) * rootVariance Finset.univ z := by
  have h := embedded_sum_variance (S.copyEmbedding e) z
  simpa only [Fintype.card_fin, copyEmbedding, Function.Embedding.coeFn_mk,
    copyMass, mul_div_assoc] using h

theorem copyMass_bounds (S : CompilerSignature Roots Code Kinds L)
    (z : Roots → ℝ) (u : ℝ) (hu : 0 < u) (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hslo : 1 / 2 ≤ ∑ r, z r) (hshi : (∑ r, z r) ≤ 1)
    (hV : rootVariance Finset.univ z ≤ 96 / ((Fintype.card Roots : ℝ) * u)) (e : Fin 3) :
    512 / u ≤ S.copyMass z e ∧ S.copyMass z e ≤ 3000 / u :=
  copy_mass_bounds _ u L _ _ _ hu hqu hLlo hLhi hslo hshi hV (S.copyMass_variance z e)

theorem incidenceWeight_le_total [DecidableEq Kinds]
    (S : CompilerSignature Roots Code Kinds L) (z : Roots → ℝ) (hz : ∀ r, 0 ≤ z r) (k : Kinds) :
    incidenceWeight S.sourceKind S.targetKind (S.copyMass z) k ≤ ∑ e, S.copyMass z e := by
  apply Finset.sum_le_sum
  intro e he
  have hnonneg := S.copyMass_nonneg z hz e
  by_cases hs : S.sourceKind e = k <;> by_cases ht : S.targetKind e = k
  · exact False.elim (S.source_ne_target e (hs.trans ht.symm))
  · simp [hs, ht]
  · simp [hs, ht]
  · simpa [hs, ht] using hnonneg

theorem root_coefficient_bounds [DecidableEq Kinds]
    (S : CompilerSignature Roots Code Kinds L) (z : Roots → ℝ) (u : ℝ)
    (hu : 100000 ≤ u) (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hz : ∀ r, 0 ≤ z r) (hslo : 1 / 2 ≤ ∑ r, z r) (hshi : (∑ r, z r) ≤ 1)
    (hV : rootVariance Finset.univ z ≤ 96 / ((Fintype.card Roots : ℝ) * u)) :
    (∀ e, 2 * (256 / u) ≤ S.copyMass z e) ∧
    (∀ k, incidenceWeight S.sourceKind S.targetKind (S.copyMass z) k ≤ (∑ r, z r) / 4) := by
  have hu0 : 0 < u := by linarith
  have hcopies := S.copyMass_bounds z u hu0 hqu hLlo hLhi hslo hshi hV
  constructor
  · intro e
    have h := (hcopies e).1
    have heq : 2 * (256 / u) = 512 / u := by ring
    rw [heq]
    exact h
  · intro k
    have htotal : (∑ e, S.copyMass z e) ≤ 9000 / u := by
      calc
        (∑ e, S.copyMass z e) ≤ ∑ _e : Fin 3, 3000 / u :=
          Finset.sum_le_sum fun e _ => (hcopies e).2
        _ = _ := by norm_num; ring
    have hnum : 9000 / u ≤ (∑ r, z r) / 4 := by
      apply (div_le_iff₀ hu0).mpr
      nlinarith
    exact (S.incidenceWeight_le_total z hz k).trans (htotal.trans hnum)

end CompilerSignature

end TuranUniversality.Weighted
