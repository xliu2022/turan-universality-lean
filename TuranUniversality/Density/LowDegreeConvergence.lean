module

public import TuranUniversality.Density.LowDegree
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! # Vanishing low-degree mass for varying finite graphs

The low-degree threshold is fixed. The weight of vertices below it tends
to zero whenever the actual edge polynomials tend to their common global
upper bound. The uniform-weight specialization is the ordinary proportion
of low-degree vertices.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality

namespace Density

theorem low_link_mass_tendsto_zero {I : Type*} {V : I → Type*}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] {r : ℕ}
    (G : ∀ i, RGraph (V i) r) (x : ∀ i, V i → ℝ)
    (hx : ∀ i, ProbabilityWeights (x i)) {Λ δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ i y, ProbabilityWeights y → (G i).edgePolynomial y ≤ Λ)
    (l : Filter I) (hlim : Tendsto (fun i => (G i).edgePolynomial (x i)) l (𝓝 Λ)) :
    Tendsto (fun i => ∑ v ∈ Finset.univ.filter
      (fun v => (G i).linkPolynomial (x i) v ≤ (r : ℝ) * Λ - δ), x i v) l (𝓝 0) := by
  classical
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun i => ha.trans_le
      (Finset.sum_nonneg (fun v _ => (hx i).1 v)))
  · intro a ha
    let η := min δ (a / 2)
    have hη : 0 < η := lt_min hδ (by linarith)
    have htol := lowDegreeTolerance_pos r hη
    have he := (tendsto_order.1 hlim).1 (Λ - lowDegreeTolerance r η) (by linarith)
    filter_upwards [he] with i hi
    have hmass := (G i).low_link_mass_le (x i) (hx i) hη (hbound i) hi.le
    have hsub : Finset.univ.filter
        (fun v => (G i).linkPolynomial (x i) v ≤ (r : ℝ) * Λ - δ) ⊆
        Finset.univ.filter
        (fun v => (G i).linkPolynomial (x i) v ≤ (r : ℝ) * Λ - η) := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (Finset.mem_filter.mp hv).2.trans (sub_le_sub_left (min_le_left _ _) _)
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => (hx i).1 v)
    exact (hs.trans hmass).trans_lt ((min_le_right _ _).trans_lt (by linarith))

end Density

namespace RGraph

theorem lowDegreeSet_ratio_eq_mass {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}
    (G : RGraph V r) (hn : 0 < Fintype.card V) (Λ δ : ℝ) :
    ((G.lowDegreeSet Λ δ).card : ℝ) / Fintype.card V =
      ∑ v ∈ Finset.univ.filter
        (fun v => G.linkPolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) v ≤ (r : ℝ) * Λ - δ),
        (Fintype.card V : ℝ)⁻¹ := by
  classical
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have heq : G.lowDegreeSet Λ δ = Finset.univ.filter
      (fun v => G.linkPolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) v ≤ (r : ℝ) * Λ - δ) := by
    ext v
    simp only [lowDegreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [G.linkPolynomial_uniform, inv_pow, ← div_eq_mul_inv]
    exact (div_le_iff₀ (pow_pos hn0 _)).symm
  rw [← heq]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end RGraph

namespace Density

theorem lowDegreeSet_ratio_tendsto_zero {I : Type*} {V : I → Type*}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] {r : ℕ}
    (G : ∀ i, RGraph (V i) r) (hn : ∀ i, 0 < Fintype.card (V i))
    {Λ δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ i y, ProbabilityWeights y → (G i).edgePolynomial y ≤ Λ)
    (l : Filter I) (hlim : Tendsto
      (fun i => ((G i).edges.card : ℝ) / (Fintype.card (V i) : ℝ) ^ r) l (𝓝 Λ)) :
    Tendsto (fun i => (((G i).lowDegreeSet Λ δ).card : ℝ) / Fintype.card (V i)) l (𝓝 0) := by
  have hx (i : I) : ProbabilityWeights (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹) := by
    have hp : (0 : ℝ) < Fintype.card (V i) := by exact_mod_cast hn i
    exact ⟨fun _ => inv_nonneg.mpr hp.le, by simp [ne_of_gt hp]⟩
  have hpoly : Tendsto (fun i => (G i).edgePolynomial
      (fun _ => (Fintype.card (V i) : ℝ)⁻¹)) l (𝓝 Λ) := by
    simpa only [RGraph.edgePolynomial_uniform, inv_pow, ← div_eq_mul_inv] using hlim
  have h := low_link_mass_tendsto_zero G
    (fun i _ => (Fintype.card (V i) : ℝ)⁻¹) hx hδ hbound l hpoly
  simpa only [← RGraph.lowDegreeSet_ratio_eq_mass _ (hn _) Λ δ] using h

end Density
end TuranUniversality
