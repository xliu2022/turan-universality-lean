module

public import TuranUniversality.Density.UpperBridge
public import TuranUniversality.Hypergraph.Labeled

@[expose] public section

/-! # The ordinary Turán upper bound for a single product forbidden graph -/

namespace TuranUniversality

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
  {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- A bound on all core-free probability weightings controls every
hom-free host after the proved finite support compression. -/
theorem product_homFree_weighted_bound
    (A : ∀ i, RGraph (V i) 3) (c : ℝ)
    (hbound : ∀ n (G : RGraph (Fin n) 3) (x : Fin n → ℝ),
      ProbabilityWeights x → (∀ i, ¬ ∃ f, (A i).IsEmbedding G f) →
        6 * G.edgePolynomial x ≤ c)
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : RGraph W 3) (hfree : (RGraph.product fun i => (A i).pairExtension).HomFree G)
    (x : W → ℝ) (hx : ProbabilityWeights x) : 6 * G.edgePolynomial x ≤ c := by
  classical
  obtain ⟨y, hy, hpoly, _hcov, hcores⟩ := RGraph.product_free_compressed_support A G hfree x hx
  let J := G.supportGraph y
  let e : Fin (Fintype.card (WeightVertex y)) ≃ WeightVertex y := (Fintype.equivFin _).symm
  let K := J.pullback e.toEmbedding
  let z : WeightVertex y → ℝ := fun v => y v.val
  have hz : ProbabilityWeights z := support_probability y hy
  have hz' : ProbabilityWeights (z ∘ e) := probabilityWeights_equiv e z hz
  have hK : ∀ i, ¬ ∃ f, (A i).IsEmbedding K f := by
    intro i h
    obtain ⟨f, hf⟩ := h
    exact hcores i ⟨_, (J.pullback_equiv_embedding e).comp hf⟩
  have hb := hbound _ K (z ∘ e) hz' hK
  have hkeq : K.edgePolynomial (z ∘ e) = J.edgePolynomial z := J.pullback_equiv_polynomial e z
  rw [hkeq] at hb
  change G.edgePolynomial x ≤ J.edgePolynomial z at hpoly
  linarith

theorem product_homFree_uniform_bound
    (A : ∀ i, RGraph (V i) 3) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n (G : RGraph (Fin n) 3) (x : Fin n → ℝ),
      ProbabilityWeights x → (∀ i, ¬ ∃ f, (A i).IsEmbedding G f) →
        6 * G.edgePolynomial x ≤ c)
    (n : ℕ) (G : RGraph (Fin n) 3)
    (hfree : (RGraph.product fun i => (A i).pairExtension).HomFree G) :
    (RGraph.oneEdge 3).homDensity G ≤ c := by
  by_cases hn : n = 0
  · subst n
    simpa [RGraph.oneEdge_homDensity] using hc
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hx : ProbabilityWeights (fun _ : Fin n => (n : ℝ)⁻¹) := by
      refine ⟨fun _ => inv_nonneg.mpr hn0.le, ?_⟩
      simp [ne_of_gt hn0]
    have hb := product_homFree_weighted_bound A c hbound G hfree _ hx
    rw [G.oneEdge_homDensity_polynomial]
    norm_num [Nat.factorial]
    exact hb

/-- This is an ordinary forbidden-subgraph density statement. The sampled
density bridge, compression, and finite product construction are all proved
in the imported modules; only the mathematical bound for the chosen class
of core-free hosts is supplied here. -/
theorem product_turanDensity_upper [Nonempty I]
    (A : ∀ i, RGraph (V i) 3) (hedges : ∀ i, (A i).edges.Nonempty)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n (G : RGraph (Fin n) 3) (x : Fin n → ℝ),
      ProbabilityWeights x → (∀ i, ¬ ∃ f, (A i).IsEmbedding G f) →
        6 * G.edgePolynomial x ≤ c) :
    turanDensity (FiniteGraph.ofRGraph (RGraph.product fun i => (A i).pairExtension)).2 ≤ c := by
  classical
  let P := RGraph.product fun i => (A i).pairExtension
  have hp : P.edges.Nonempty := RGraph.product_edges_nonempty _
    (fun i => (A i).pairExtension_edges_nonempty (hedges i))
  have hF : 1 ≤ (FiniteGraph.ofRGraph P).2.edges.card :=
    Finset.card_pos.mpr (FiniteGraph.ofRGraph_edges_nonempty P hp)
  apply turanDensity_upper_of_homFree (FiniteGraph.ofRGraph P).2 hF c hc
  intro n G hfree
  exact product_homFree_uniform_bound A c hc hbound n G ((FiniteGraph.ofRGraph_homFree P G).mp hfree)

end TuranUniversality
