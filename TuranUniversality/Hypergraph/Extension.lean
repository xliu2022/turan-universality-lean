module

public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-!
# Private pair-covering extensions

We add a private vertex for every unordered core pair, including pairs already
covered. This harmless enlargement avoids a conditional vertex type. The
singleton theorem only asserts existence of a forbidden graph. Both properties
used in its proof remain valid: a homomorphism is injective on the core, and a
core embedding into a pair-covered target extends to a homomorphism.
-/

namespace TuranUniversality.RGraph

universe u v

/-- An unordered pair of distinct vertices. -/
abbrev VertexPair (V : Type u) [DecidableEq V] :=
  {p : Finset V // p.card = 2}

/-- Core vertices and one private vertex for every core pair. -/
abbrev ExtensionVertex (V : Type u) [DecidableEq V] := V ⊕ VertexPair V

variable {V : Type u} [DecidableEq V]

def privateEdge (p : VertexPair V) : Finset (ExtensionVertex V) :=
  insert (Sum.inr p) (p.val.image Sum.inl)

theorem privateEdge_card (p : VertexPair V) : (privateEdge p).card = 3 := by
  simp [privateEdge, Finset.card_image_of_injective, Sum.inl_injective, p.property]

/-- The private pair-covering extension of a three-uniform hypergraph. -/
noncomputable def pairExtension [Fintype V] (A : RGraph V 3) :
    RGraph (ExtensionVertex V) 3 := by
  classical
  refine ⟨A.edges.image (fun e => e.image Sum.inl) ∪
    Finset.univ.image privateEdge, ?_⟩
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact A.uniform d hd
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    exact privateEdge_card p

theorem core_isHom [Fintype V] (A : RGraph V 3) :
    A.IsHom A.pairExtension Sum.inl := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem core_isEmbedding [Fintype V] (A : RGraph V 3) :
    A.IsEmbedding A.pairExtension Sum.inl :=
  ⟨Sum.inl_injective, core_isHom A⟩

theorem privateEdge_mem [Fintype V] (A : RGraph V 3) (p : VertexPair V) :
    privateEdge p ∈ A.pairExtension.edges :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)

theorem core_pair_covered [Fintype V] (A : RGraph V 3)
    (x y : V) (hxy : x ≠ y) :
    ∃ e ∈ A.pairExtension.edges, Sum.inl x ∈ e ∧ Sum.inl y ∈ e := by
  let p : VertexPair V := ⟨{x, y}, by simp [hxy]⟩
  refine ⟨privateEdge p, privateEdge_mem A p, ?_, ?_⟩ <;>
    simp [privateEdge, p]

theorem extension_hom_core_embedding [Fintype V]
    {W : Type v} [DecidableEq W]
    (A : RGraph V 3) (G : RGraph W 3)
    {f : ExtensionVertex V → W} (hf : A.pairExtension.IsHom G f) :
    A.IsEmbedding G (f ∘ Sum.inl) := by
  refine ⟨?_, hf.comp (core_isHom A)⟩
  intro x y hxy
  by_contra hne
  obtain ⟨e, he, hx, hy⟩ := core_pair_covered A x y hne
  have h := hf.injOn_edge he hx hy hxy
  exact hne (Sum.inl.inj h)

/-- Pair coverage in a three-graph supplies a third vertex. -/
theorem CoversPairs.complete_three (G : RGraph V 3) (hG : G.CoversPairs)
    (u v : V) (huv : u ≠ v) : ∃ z : V, insert z {u, v} ∈ G.edges := by
  obtain ⟨e, he, hu, hv⟩ := hG u v huv
  have hpair : ({u, v} : Finset V) ⊆ e := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hv
  have hcard : ({u, v} : Finset V).card < e.card := by
    rw [G.uniform e he]
    simp [huv]
  have hnot : ¬ e ⊆ ({u, v} : Finset V) := by
    intro h
    exact (not_le_of_gt hcard) (Finset.card_le_card h)
  obtain ⟨z, hz, hznot⟩ := Finset.not_subset.mp hnot
  have heq : insert z ({u, v} : Finset V) = e := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset hz hpair
    · simp [Finset.card_insert_of_notMem hznot, huv, G.uniform e he]
  exact ⟨z, heq ▸ he⟩

theorem CoversPairs.complete_image_pair {W : Type v} [DecidableEq W]
    (G : RGraph W 3) (hG : G.CoversPairs)
    (f : V → W) (hf : Function.Injective f) (p : VertexPair V) :
    ∃ z : W, insert z (p.val.image f) ∈ G.edges := by
  obtain ⟨u, v, huv, hp⟩ := Finset.card_eq_two.mp p.property
  obtain ⟨z, hz⟩ := hG.complete_three G (f u) (f v) (fun h => huv (hf h))
  refine ⟨z, ?_⟩
  simpa [hp] using hz

/-- Every embedded core in a pair-covered target extends to a homomorphism. -/
theorem extension_hom_of_core_embedding [Fintype V]
    {W : Type v} [DecidableEq W]
    (A : RGraph V 3) (G : RGraph W 3) (hG : G.CoversPairs)
    {f : V → W} (hf : A.IsEmbedding G f) :
    ∃ g : ExtensionVertex V → W, A.pairExtension.IsHom G g ∧
      ∀ v, g (Sum.inl v) = f v := by
  classical
  have hc (p : VertexPair V) : ∃ z : W, insert z (p.val.image f) ∈ G.edges :=
    hG.complete_image_pair G f hf.1 p
  let g : ExtensionVertex V → W :=
    Sum.elim f (fun p => Classical.choose (hc p))
  refine ⟨g, ?_, fun _ => rfl⟩
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    simpa [g, Finset.image_image, Function.comp_def] using hf.2 d hd
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    simpa [privateEdge, g, Finset.image_image, Function.comp_def] using
      Classical.choose_spec (hc p)

end TuranUniversality.RGraph
