module

public import TuranUniversality.Hypergraph.InducedDegree
public import TuranUniversality.Density.WeightedHomRestriction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Embeddings between actual induced vertex sets -/

namespace TuranUniversality.RGraph

universe u v
variable {U : Type u} {V : Type v} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {r : ℕ}

theorem IsHom.into_induced {F : RGraph U r} {G : RGraph V r} {f : U → V}
    (hf : F.IsHom G f) (S : Finset V) (hs : ∀ u, f u ∈ S) :
    F.IsHom (G.induced S) (fun u => ⟨f u, hs u⟩) :=
  (isHom_pullback_iff F G (Function.Embedding.subtype _) _).mpr hf

theorem IsEmbedding.into_induced {F : RGraph U r} {G : RGraph V r} {f : U → V}
    (hf : F.IsEmbedding G f) (S : Finset V) (hs : ∀ u, f u ∈ S) :
    F.IsEmbedding (G.induced S) (fun u => ⟨f u, hs u⟩) :=
  ⟨fun _ _ h => hf.1 (congrArg Subtype.val h), hf.isHom.into_induced S hs⟩

theorem induced_subset_embedding (G : RGraph V r) {S T : Finset V} (hST : S ⊆ T) :
    (G.induced S).IsEmbedding (G.induced T) (fun v => ⟨v.val, hST v.property⟩) :=
  (G.induced_isEmbedding S).into_induced T (fun v => hST v.property)

theorem into_full_induced (G : RGraph V r) :
    G.IsEmbedding (G.induced Finset.univ) (fun v => ⟨v, Finset.mem_univ v⟩) :=
  (show G.IsEmbedding G id from ⟨Function.injective_id, G.isHom_id⟩).into_induced
    Finset.univ (fun v => Finset.mem_univ v)

theorem induced_agree_embedding (G H : RGraph V r) {S T : Finset V} (hST : S ⊆ T)
    (hsub : ∀ e ∈ G.edges, e ⊆ S → e ∈ H.edges) :
    (G.induced S).IsEmbedding (H.induced T) (fun v => ⟨v.val, hST v.property⟩) := by
  have h : (G.induced S).IsEmbedding H Subtype.val := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro e he
    apply hsub _ ((G.induced_isEmbedding S).2 e he)
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  exact h.into_induced T (fun v => hST v.property)

theorem exists_embedding_deleted_insert (G : RGraph V r) (S : Finset V) (v : V) :
    ∃ f, ((G.induced (insert v S)).induced
      (Finset.univ.erase (⟨v, Finset.mem_insert_self _ _⟩ : ↥(insert v S)))).IsEmbedding
      (G.induced S) f := by
  classical
  let v' : ↥(insert v S) := ⟨v, Finset.mem_insert_self _ _⟩
  let D := (Finset.univ : Finset ↥(insert v S)).erase v'
  have hrange (w : D) : w.val.val ∈ S := by
    have hne := (Finset.mem_erase.mp w.property).1
    rcases Finset.mem_insert.mp w.val.property with h | h
    · exact False.elim (hne (Subtype.ext h))
    · exact h
  have hh := ((G.induced_isEmbedding (insert v S)).comp
    ((G.induced (insert v S)).induced_isEmbedding D)).into_induced S hrange
  exact ⟨_, hh⟩

theorem induced_clone_away_embedding (G : RGraph V r) (u v : V)
    {S T : Finset V} (hST : S ⊆ T) (hu : u ∉ S) :
    (G.induced S).IsEmbedding ((G.clone u v).induced T)
      (fun w => ⟨w.val, hST w.property⟩) := by
  apply G.induced_agree_embedding (G.clone u v) hST
  intro e he hs
  exact (G.mem_clone_of_notMem u v (fun h => hu (hs h))).mpr he

end TuranUniversality.RGraph
