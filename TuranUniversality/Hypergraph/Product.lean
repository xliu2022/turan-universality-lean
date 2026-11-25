module

public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-! # Finite categorical products of simple uniform hypergraphs -/

namespace TuranUniversality.RGraph

universe u v w

/-- The categorical product: an r-set is an edge exactly when all projections
are edges. This definition also makes sense for an empty factor index type. -/
noncomputable def product {I : Type u} [Fintype I]
    {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {r : ℕ} (G : ∀ i, RGraph (V i) r) : RGraph (∀ i, V i) r := by
  classical
  exact ⟨(Finset.univ.powersetCard r).filter
    (fun e => ∀ i, e.image (fun x => x i) ∈ (G i).edges),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

theorem product_mem {I : Type u} [Fintype I]
    {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {r : ℕ} (G : ∀ i, RGraph (V i) r) (e : Finset (∀ i, V i)) :
    e ∈ (product G).edges ↔ e.card = r ∧
      ∀ i, e.image (fun x => x i) ∈ (G i).edges := by
  classical
  simp [product, Finset.mem_powersetCard]

theorem product_projection {I : Type u} [Fintype I]
    {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {r : ℕ} (G : ∀ i, RGraph (V i) r) (i : I) :
    (product G).IsHom (G i) (fun x => x i) := by
  intro e he
  exact ((product_mem G e).mp he).2 i

theorem factor_homFree_of_product {I : Type u} [Fintype I]
    {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {W : Type w} [DecidableEq W] {r : ℕ}
    (G : ∀ i, RGraph (V i) r) (T : RGraph W r)
    (h : (product G).HomFree T) (i : I) : (G i).HomFree T :=
  h.of_hom (product_projection G i)

end TuranUniversality.RGraph
