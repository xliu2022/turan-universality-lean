module

public import TuranUniversality.Hypergraph.Relabel
public import TuranUniversality.Hypergraph.FiniteBasis
public import TuranUniversality.Hypergraph.ProductTransfer
public import TuranUniversality.Selector.CompatibleProfiles

@[expose] public section

/-! # Labeled finite graphs and a single product of pair extensions -/

namespace TuranUniversality

namespace FiniteGraph

universe u v
variable {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
  [DecidableEq W] {r : ℕ}

noncomputable def ofRGraph (G : RGraph V r) : FiniteGraph r :=
  ⟨Fintype.card V, G.pullback (Fintype.equivFin V).symm.toEmbedding⟩

theorem ofRGraph_embedding (G : RGraph V r) :
    (ofRGraph G).2.IsEmbedding G (Fintype.equivFin V).symm :=
  G.pullback_equiv_embedding _

theorem embedding_ofRGraph (G : RGraph V r) :
    G.IsEmbedding (ofRGraph G).2 (Fintype.equivFin V) :=
  G.pullback_equiv_inverse _

theorem ofRGraph_homFree (G : RGraph V r) (H : RGraph W r) :
    (ofRGraph G).2.HomFree H ↔ G.HomFree H :=
  ⟨fun h => h.of_hom (ofRGraph_embedding G).isHom,
    fun h => h.of_hom (embedding_ofRGraph G).isHom⟩

theorem ofRGraph_edges_nonempty (G : RGraph V r) (h : G.edges.Nonempty) :
    (ofRGraph G).2.edges.Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨_, (embedding_ofRGraph G).2 e he⟩

end FiniteGraph

namespace RGraph

universe u v
variable {I : Type u} [Fintype I] [Nonempty I] [DecidableEq I]
  {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

theorem product_edges_nonempty (G : ∀ i, RGraph (V i) 3)
    (h : ∀ i, (G i).edges.Nonempty) : (product G).edges.Nonempty := by
  classical
  choose e he using h
  have hthree (i : I) : (e i).card = 3 := (G i).uniform _ (he i)
  choose a b c hab hac hbc heq using fun i => Finset.card_eq_three.mp (hthree i)
  have hedge (i : I) : {a i, b i, c i} ∈ (G i).edges := (heq i) ▸ he i
  exact ⟨{a, b, c}, Selector.triple_product_mem G a b c hedge⟩

theorem pairExtension_edges_nonempty {W : Type*} [Fintype W] [DecidableEq W]
    (G : RGraph W 3) (h : G.edges.Nonempty) : G.pairExtension.edges.Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨_, (core_isHom G) e he⟩

end RGraph

namespace FiniteGraph

noncomputable def singletonProduct (F : Finset (FiniteGraph 3)) : FiniteGraph 3 :=
  ofRGraph (RGraph.product fun A : F => A.val.2.pairExtension)

theorem singletonProduct_edges_nonempty (F : Finset (FiniteGraph 3)) (hF : F.Nonempty)
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) : (singletonProduct F).2.edges.Nonempty := by
  classical
  letI : Nonempty F := ⟨⟨hF.choose, hF.choose_spec⟩⟩
  apply ofRGraph_edges_nonempty
  apply RGraph.product_edges_nonempty
  intro A
  exact A.val.2.pairExtension_edges_nonempty (hedges A.val A.property)

end FiniteGraph

end TuranUniversality
