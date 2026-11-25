module

public import TuranUniversality.Structural.OrdinaryStability
public import TuranUniversality.Hypergraph.VertexDeletion

@[expose] public section

/-! # Actual edit approximation by canonical graphs of the same order

The graph supplied here has exactly the original vertex carrier, and its
edge set is a subset of the input edge set. The normalized cardinality of
their symmetric difference tends to zero. This is the finite edit version
of the low-degree deletion step; model completion and class-size rounding
are separate subsequent steps.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Stability

universe u v
variable {b t : ℕ}

theorem near_extremal_edit_approximation (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{u} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * b + 4)))
    (hG : ∀ i, familyFree (forbidden F Ω t) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * b + 4))) l (𝓝 (optimum F b t p q))) :
    ∃ H : ∀ i, RGraph (V i) (t + (3 * b + 4)),
      (∀ i, (H i).edges ⊆ (G i).edges) ∧
      Tendsto (fun i => (((G i).edgeSymmDifference (H i)).edges.card : ℝ) /
        (Fintype.card (V i) : ℝ) ^ (t + (3 * b + 4))) l (𝓝 0) ∧
      Tendsto (fun i => ((H i).edges.card : ℝ) /
        (Fintype.card (V i) : ℝ) ^ (t + (3 * b + 4))) l (𝓝 (optimum F b t p q)) ∧
      ∀ᶠ i in l, Canonical (homomorphicClosure F) Ω (H i) := by
  classical
  obtain ⟨δ, _, hsmall, hcan⟩ := eventually_canonical_induced F hedges Ω hdis t
    p q hp hpq hq hz hΩ hext G hG hn l hsize hlim
  let S i := goodVertices (G i) (optimum F b t p q) δ
  have hsmall' : Tendsto (fun i => ((Finset.univ \ S i).card : ℝ) /
      Fintype.card (V i)) l (𝓝 0) := by
    have heq i : Finset.univ \ S i = (G i).lowDegreeSet (optimum F b t p q) δ :=
      Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
    simpa only [heq] using hsmall
  refine ⟨fun i => (G i).keepVertices (S i), fun i => (G i).keepVertices_subset (S i),
    RGraph.keepVertices_edit_ratio_tendsto_zero G (by omega) hn S l hsmall',
    RGraph.keepVertices_edge_ratio_tendsto G (by omega) hn S l hsmall' hlim, ?_⟩
  filter_upwards [hcan] with i hi
  obtain ⟨f, hf⟩ := (G i).keepVertices_hom_induced (S i) (Finset.card_pos.mp hi.1)
  exact Canonical.of_hom F Ω hf hi.2

end TuranUniversality.Structural.Ordinary
