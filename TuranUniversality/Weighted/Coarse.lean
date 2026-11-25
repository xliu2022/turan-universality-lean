module

public import TuranUniversality.Weighted.Incidence
public import TuranUniversality.Weighted.Marker

/-! # The coarse estimate from the actual rooted hypergraph -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v w
variable {Roots : Type u} {Data : Type v} {Code : Type w}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Data] [Fintype Data]
  [Fintype Code]

theorem triple_weight_le_total (p : Finset Data) (hp : p.card = 3)
    (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    (∏ d ∈ p, x d) ≤ (∑ d, x d) ^ 3 / 27 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hp
  have hs : x a + x b + x c ≤ ∑ d, x d := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({a, b, c} : Finset Data)) (f := x)
      (fun d _ _ => hx d)
    simpa [hab, hac, hbc, add_assoc] using hsub
  have hcube : (x a + x b + x c) ^ 3 ≤ (∑ d, x d) ^ 3 := by
    gcongr
    exact add_nonneg (add_nonneg (hx a) (hx b)) (hx c)
  have hAM := triple_product_le_cube (x a) (x b) (x c) (hx a) (hx b) (hx c)
  rw [Finset.prod_insert (by simp [hab, hac] : a ∉ ({b, c} : Finset Data)),
    Finset.prod_pair hbc]
  nlinarith

namespace RootedModel

omit [Fintype Roots] in
theorem contribution_zero_bound (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d)
    (hone : M.dataTriples.card ≤ 1) :
    M.contribution 0 z x ≤ (∑ d, x d) ^ 3 / 27 := by
  rw [M.contribution_zero_eq]
  by_cases hE : M.dataTriples = ∅
  · rw [hE, Finset.sum_empty]
    exact div_nonneg (pow_nonneg (Finset.sum_nonneg fun d _ => hx d) 3) (by norm_num)
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    have hsingle : M.dataTriples = {p} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hp, fun q hq => Finset.card_le_one.mp hone q hq p hp⟩
    rw [hsingle, Finset.sum_singleton]
    exact triple_weight_le_total p (M.dataTriples_uniform p hp) x hx

omit [Fintype Roots] in
theorem dataLink_coarse_bound (M : RootedModel Roots Data) (r : Roots)
    (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    (∑ p ∈ M.dataLink r, ∏ d ∈ p, x d) ≤ (∑ d, x d) ^ 2 / 2 := by
  have hmono : (∑ p ∈ M.dataLink r, ∏ d ∈ p, x d) ≤ elementary Finset.univ x 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, M.dataLink_uniform r p hp⟩
    · exact fun p hp hnot => Finset.prod_nonneg fun d hd => hx d
  exact hmono.trans (root_pairs_bound Finset.univ x)

theorem contribution_one_coarse_bound (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) :
    M.contribution 1 z x ≤ (∑ r, z r) * (∑ d, x d) ^ 2 / 2 := by
  rw [M.contribution_one_eq]
  calc
    _ ≤ ∑ r, z r * ((∑ d, x d) ^ 2 / 2) :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (M.dataLink_coarse_bound r x hx) (hz r)
    _ = _ := by rw [← Finset.sum_mul]; ring

end RootedModel

namespace CodeSystem

theorem contribution_two_coarse_bound (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (hcard : 0 < Fintype.card Roots)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hH1 : C.HasCandidates M) :
    M.contribution 2 z x ≤ coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 * (∑ d, x d) := by
  rw [M.contribution_two_eq]
  calc
    _ ≤ ∑ d, x d * (coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2) :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
        (C.rootLink_bound M z d hcard hz (hH1 d)) (hx d)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The graph polynomial itself satisfies the coarse estimate; the only
incidence assumptions used here are H1 and the single-marker condition. -/
theorem edgePolynomial_coarse_bound (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (hcard : 8 ≤ Fintype.card Roots)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hH1 : C.HasCandidates M)
    (hone : M.dataTriples.card ≤ 1) :
    M.toRGraph.edgePolynomial (Sum.elim z x) ≤
      coeffA (Fintype.card Roots) * (∑ r, z r) ^ 3 +
      coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 * (∑ d, x d) +
      (∑ r, z r) * (∑ d, x d) ^ 2 / 2 + (∑ d, x d) ^ 3 / 27 -
      (∑ r, z r) / 12 * rootVariance Finset.univ z := by
  rw [M.edgePolynomial_four_shapes]
  have h3 := M.contribution_three_variance_bound z x hcard hz
  have h2 := C.contribution_two_coarse_bound M z x (by omega) hz hx hH1
  have h1 := M.contribution_one_coarse_bound z x hz hx
  have h0 := M.contribution_zero_bound z x hx hone
  linarith

end CodeSystem

/-- A convenient relaxation of the exact cubic coarse estimate. -/
theorem coarse_cubic_relaxation (q t : ℝ) (hq : 0 < q) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    coeffA q * (1 - t) ^ 3 + coeffB q * (1 - t) ^ 2 * t +
      (1 - t) * t ^ 2 / 2 + t ^ 3 / 27 - coeffA q ≤
        t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54 := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hrem : 0 ≤ t * (3 * q * t ^ 2 + 3 * q * t + 2 * t ^ 2 + 6 * (1 - t)) := by
    positivity
  unfold coeffA coeffB
  have hident :
      (t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54 -
        ((q - 1) * (q - 2) / (6 * q ^ 2) * (1 - t) ^ 3 +
          (q - 2) / (2 * q) * (1 - t) ^ 2 * t +
          (1 - t) * t ^ 2 / 2 + t ^ 3 / 27 - (q - 1) * (q - 2) / (6 * q ^ 2))) =
        t * (3 * q * t ^ 2 + 3 * q * t + 2 * t ^ 2 + 6 * (1 - t)) / (6 * q ^ 2) := by
    field_simp
    ring
  have hn : 0 ≤ t / (2 * q) + t ^ 2 / q - 7 * t ^ 3 / 54 -
        ((q - 1) * (q - 2) / (6 * q ^ 2) * (1 - t) ^ 3 +
          (q - 2) / (2 * q) * (1 - t) ^ 2 * t +
          (1 - t) * t ^ 2 / 2 + t ^ 3 / 27 - (q - 1) * (q - 2) / (6 * q ^ 2)) := by
    rw [hident]
    exact div_nonneg hrem (by positivity)
  linarith

end TuranUniversality.Weighted
