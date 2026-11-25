module

public import TuranUniversality.Weighted.RootCopies
public import TuranUniversality.Weighted.Ambiguity

/-! # The actual rooted compiler polynomial estimate -/

@[expose] public section

namespace TuranUniversality.Weighted.CompilerSignature

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

omit [DecidableEq Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem ambiguousWeight_nonneg (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    0 ≤ S.codes.ambiguousWeight M x := Finset.sum_nonneg fun d _ => hx d

omit [DecidableEq Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem ambiguousWeight_le_total (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    S.codes.ambiguousWeight M x ≤ ∑ d, x d := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  exact fun d _ _ => hx d

/-- Summing the verified root, code, type, matching and ambiguity estimates
for the actual hypergraph. Only the actual marker contribution remains. -/
theorem edgePolynomial_fine_bound (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (z : Roots → ℝ) (x : Data → ℝ) (u : ℝ)
    (hm : 30 ≤ Fintype.card Kinds) (hu : 100000 ≤ u)
    (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1)
    (hP : coeffA (Fintype.card Roots) ≤ M.toRGraph.edgePolynomial (Sum.elim z x)) :
    M.toRGraph.edgePolynomial (Sum.elim z x) ≤
      baseline (Fintype.card Kinds) (Fintype.card Roots) (∑ d, x d) +
      (∑ r, z r) / (Fintype.card Kinds : ℝ) *
        ((∑ d, x d) * S.codes.ambiguousWeight M x - (S.codes.ambiguousWeight M x) ^ 2 / 2) -
      (∑ r, z r) ^ 2 * S.codes.ambiguousWeight M x / (2 * (Fintype.card Roots : ℝ)) +
      M.contribution 0 z x - (256 / u) * S.totalDefect M h x -
      (∑ r, z r) / 24 * rootVariance Finset.univ z -
      (∑ r, z r) / 4 * rootVariance Finset.univ ((S.partition M h.candidates).mass x) := by
  have hs : 0 ≤ ∑ r, z r := Finset.sum_nonneg fun r _ => hz r
  have ht : 0 ≤ ∑ d, x d := Finset.sum_nonneg fun d _ => hx d
  have hw := S.ambiguousWeight_nonneg M x hx
  have hwt := S.ambiguousWeight_le_total M x hx
  have hreg := S.codes.fine_regime M z x u (by linarith) hqu hz hx hnorm h.candidates h.oneMarker hP
  have hroot := S.root_coefficient_bounds z u hu hqu hLlo hLhi hz (le_of_lt hreg.2.1)
    (by linarith) hreg.2.2
  have hq : 8 ≤ Fintype.card Roots := by
    have hr : (8 : ℝ) ≤ Fintype.card Roots := by nlinarith
    exact_mod_cast hr
  have hm0 : (Fintype.card Kinds : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card Kinds ≠ 0)
  have htSmall : (∑ d, x d) ≤ 1 / 24 := by
    have hsmall : 4 / u ≤ 1 / 24 := by
      apply (div_le_iff₀ (by linarith : 0 < u)).mpr
      linarith
    exact (le_of_lt hreg.1).trans hsmall
  have hws : S.codes.ambiguousWeight M x ≤ (∑ r, z r) / 12 := by
    linarith [hreg.2.1]
  have h3 := M.contribution_three_variance_bound z x hq hz
  have h2 := S.codes.two_root_contribution_bound M z x (by omega) hz hx h.candidates
  have h1 := S.one_root_variance_bound M h z x hz hx (by omega)
    ((∑ r, z r) / 4) (256 / u) hroot.2 hroot.1
  have hV : 0 ≤ rootVariance Finset.univ z := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hVloss := mul_le_mul_of_nonneg_right hws hV
  have htype : coeffC (Fintype.card Kinds) * (∑ r, z r) *
        ((∑ d, x d) - S.codes.ambiguousWeight M x) ^ 2 +
      (∑ r, z r) * ((∑ d, x d) * S.codes.ambiguousWeight M x -
        (S.codes.ambiguousWeight M x) ^ 2 / 2) =
      coeffC (Fintype.card Kinds) * (∑ r, z r) * (∑ d, x d) ^ 2 +
      (∑ r, z r) / (Fintype.card Kinds : ℝ) *
        ((∑ d, x d) * S.codes.ambiguousWeight M x - (S.codes.ambiguousWeight M x) ^ 2 / 2) := by
    unfold coeffC
    field_simp
    ring
  rw [htype] at h1
  have hbase : baseline (Fintype.card Kinds) (Fintype.card Roots) (∑ d, x d) =
      coeffA (Fintype.card Roots) * (∑ r, z r) ^ 3 +
      coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 * (∑ d, x d) +
      coeffC (Fintype.card Kinds) * (∑ r, z r) * (∑ d, x d) ^ 2 := by
    unfold baseline cubic
    rw [show 1 - (∑ d, x d) = ∑ r, z r by linarith]
  rw [hbase, M.edgePolynomial_four_shapes]
  nlinarith

/-- Once the actual marker reward has been absorbed by the actual union
matching defects, the whole hypergraph is bounded by the rational baseline. -/
theorem edgePolynomial_le_baseline_of_marker_absorbed
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (z : Roots → ℝ) (x : Data → ℝ) (u : ℝ)
    (hm : 30 ≤ Fintype.card Kinds) (hu : 100000 ≤ u)
    (hq : (Fintype.card Roots : ℝ) = rootCount (Fintype.card Kinds : ℝ))
    (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1)
    (hmarker : M.contribution 0 z x - (256 / u) * S.totalDefect M h x ≤
      (S.codes.ambiguousWeight M x) ^ 3 / 27) :
    M.toRGraph.edgePolynomial (Sum.elim z x) ≤
      baselineMax (Fintype.card Kinds) (Fintype.card Roots) := by
  have hmr : (30 : ℝ) ≤ Fintype.card Kinds := by exact_mod_cast hm
  by_cases hP : coeffA (Fintype.card Roots) ≤ M.toRGraph.edgePolynomial (Sum.elim z x)
  · have hF := S.edgePolynomial_fine_bound M h z x u hm hu hqu hLlo hLhi hz hx hnorm hP
    have hs : 0 ≤ ∑ r, z r := Finset.sum_nonneg fun r _ => hz r
    have ht : 0 ≤ ∑ d, x d := Finset.sum_nonneg fun d _ => hx d
    have hA := baseline_ambiguity_le (Fintype.card Kinds : ℝ) (∑ r, z r) (∑ d, x d)
      (S.codes.ambiguousWeight M x) hmr hs ht hnorm (S.ambiguousWeight_nonneg M x hx)
      (S.ambiguousWeight_le_total M x hx)
    rw [← hq] at hA
    have hRV : 0 ≤ (∑ r, z r) / 24 * rootVariance Finset.univ z :=
      mul_nonneg (div_nonneg hs (by norm_num)) (Finset.sum_nonneg fun r _ => sq_nonneg _)
    have hTV : 0 ≤ (∑ r, z r) / 4 * rootVariance Finset.univ ((S.partition M h.candidates).mass x) :=
      mul_nonneg (div_nonneg hs (by norm_num)) (Finset.sum_nonneg fun k _ => sq_nonneg _)
    linarith
  · have hb := (baselineMax_strict_bounds (Fintype.card Kinds : ℝ) hmr).1
    rw [← hq] at hb
    exact (le_of_not_ge hP).trans hb.le

/-- A complete weighted bound for the actual unmarked rooted models. -/
theorem unmarked_edgePolynomial_le_baseline
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (z : Roots → ℝ) (x : Data → ℝ) (u : ℝ)
    (hm : 30 ≤ Fintype.card Kinds) (hu : 100000 ≤ u)
    (hq : (Fintype.card Roots : ℝ) = rootCount (Fintype.card Kinds : ℝ))
    (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1)
    (hmarker : M.dataTriples = ∅) :
    M.toRGraph.edgePolynomial (Sum.elim z x) ≤
      baselineMax (Fintype.card Kinds) (Fintype.card Roots) := by
  apply S.edgePolynomial_le_baseline_of_marker_absorbed M h z x u hm hu hq hqu hLlo hLhi hz hx hnorm
  rw [M.contribution_zero_eq, hmarker, Finset.sum_empty]
  have hD := S.totalDefect_nonneg M h x
  have hw := S.ambiguousWeight_nonneg M x hx
  have hα : 0 ≤ 256 / u := div_nonneg (by norm_num) (by linarith)
  have hreward : 0 ≤ (S.codes.ambiguousWeight M x) ^ 3 / 27 := by positivity
  nlinarith

end TuranUniversality.Weighted.CompilerSignature
