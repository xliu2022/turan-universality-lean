module

public import TuranUniversality.Hypergraph.Restriction
public import TuranUniversality.Hypergraph.Extension
public import TuranUniversality.Hypergraph.Product

@[expose] public section

/-!
# Weighted upper transfer for a product of pair-covering extensions

This proves the finite support assertion used in Lemma 5.10.  The theorem
uses actual embeddings and homomorphisms and constructs a pair-covered
forbidden-core-free support.  The separate ordinary-density bridge is required
before obtaining the asymptotic Turán inequality.
-/

namespace TuranUniversality.RGraph

universe u v w

variable {I : Type u} [Fintype I]
variable {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {W : Type w} [Fintype W] [DecidableEq W]

omit [Fintype W] in
/-- A pair-covered target that receives no homomorphism from the product
contains none of the cores as an ordinary subgraph. -/
theorem product_free_paircovered_core_free
    (A : ∀ i, RGraph (V i) 3) (G : RGraph W 3)
    (hfree : (product (fun i => (A i).pairExtension)).HomFree G)
    (hcover : G.CoversPairs) (i : I) :
    ¬ ∃ f, (A i).IsEmbedding G f := by
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, _⟩ := extension_hom_of_core_embedding (A i) G hcover hf
  exact (factor_homFree_of_product (fun i => (A i).pairExtension) G hfree i) ⟨g, hg⟩

/-- Compressing any weighting of a product-hom-free graph gives a genuinely
core-free induced support, without decreasing the polynomial. -/
theorem product_free_compressed_support
    (A : ∀ i, RGraph (V i) 3) (G : RGraph W 3)
    (hfree : (product (fun i => (A i).pairExtension)).HomFree G)
    (x : W → ℝ) (hx : ProbabilityWeights x) :
    ∃ y : W → ℝ, ProbabilityWeights y ∧
      G.edgePolynomial x ≤ (G.supportGraph y).edgePolynomial (fun v => y v.val) ∧
      (G.supportGraph y).CoversPairs ∧
      ∀ i, ¬ ∃ f, (A i).IsEmbedding (G.supportGraph y) f := by
  classical
  obtain ⟨y, hy, hxy, hc⟩ := G.exists_compressed_weights x hx
  have hcov := hc.support_covers_pairs G y
  have hsfree : (product (fun i => (A i).pairExtension)).HomFree
      (G.supportGraph y) := by
    rintro ⟨f, hf⟩
    exact hfree ⟨_, (G.supportGraph_isHom y).comp hf⟩
  refine ⟨y, hy, ?_, hcov, fun i =>
    product_free_paircovered_core_free A (G.supportGraph y) hsfree hcov i⟩
  simpa [G.supportGraph_polynomial] using hxy

end TuranUniversality.RGraph
