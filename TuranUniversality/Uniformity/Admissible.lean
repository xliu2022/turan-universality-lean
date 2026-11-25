module

public import TuranUniversality.Hypergraph.Relabel
public import TuranUniversality.Hypergraph.FiniteBasis

@[expose] public section

/-! # The monotone class of suspensions with a homomorphism-free link

The link retains every vertex outside the core, including isolated vertices.
Its definition does not require a proof that the proposed core is common.
-/

namespace TuranUniversality

universe u v w

namespace RGraph

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] {r : ℕ}

/-- The three-uniform link on the full complement of a proposed core. -/
def coreLink (G : RGraph V r) (S : Finset V) : RGraph {v // v ∉ S} 3 :=
  ⟨(Finset.univ.powersetCard 3).filter
    (fun e => S ∪ e.image Subtype.val ∈ G.edges),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

@[simp] theorem mem_coreLink (G : RGraph V r) (S : Finset V)
    (e : Finset {v // v ∉ S}) :
    e ∈ (G.coreLink S).edges ↔ e.card = 3 ∧ S ∪ e.image Subtype.val ∈ G.edges := by
  simp [coreLink, Finset.mem_powersetCard]

/-- A common core leaves exactly three vertices in every edge. -/
structure IsCore (G : RGraph V r) (S : Finset V) : Prop where
  card : S.card + 3 = r
  subset : ∀ e ∈ G.edges, S ⊆ e

instance (G : RGraph V r) (S : Finset V) : Decidable (G.IsCore S) :=
  decidable_of_iff (S.card + 3 = r ∧ ∀ e ∈ G.edges, S ⊆ e)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.card, h.subset⟩⟩

theorem IsCore.sdiff_card {G : RGraph V r} {S : Finset V} (h : G.IsCore S)
    {e : Finset V} (he : e ∈ G.edges) : (e \ S).card = 3 := by
  rw [Finset.card_sdiff_of_subset (h.subset e he), G.uniform e he]
  have := h.card
  omega

/-- An embedding that maps one proposed core exactly onto another induces
an embedding of their complete links. -/
theorem coreLink_embedding {F : RGraph V r} {G : RGraph W r}
    {f : V → W} (hf : F.IsEmbedding G f) {S : Finset V} {T : Finset W}
    (hST : S.image f = T) :
    ∃ g : {v // v ∉ S} → {w // w ∉ T},
      (F.coreLink S).IsEmbedding (G.coreLink T) g ∧
      ∀ v, (g v).val = f v.val := by
  classical
  have hnot (v : {v // v ∉ S}) : f v.val ∉ T := by
    rw [← hST]
    simpa only [Finset.mem_image, hf.1.eq_iff, exists_eq_right] using v.property
  let g : {v // v ∉ S} → {w // w ∉ T} := fun v => ⟨f v.val, hnot v⟩
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (hf.1 (congrArg Subtype.val hab))
  refine ⟨g, ⟨hg, ?_⟩, fun _ => rfl⟩
  intro e he
  obtain ⟨hcard, hedge⟩ := (F.mem_coreLink S e).mp he
  apply (G.mem_coreLink T _).mpr
  refine ⟨by rw [Finset.card_image_of_injective _ hg, hcard], ?_⟩
  have h := hf.2 _ hedge
  simpa [Finset.image_union, Finset.image_image, hST, Function.comp_def, g] using h

/-- Every edge contained in a retained vertex set is an edge of the induced
subgraph, with its complete vertex set preserved. -/
theorem exists_pullback_edge (G : RGraph V r) (T : Finset V)
    {e : Finset V} (he : e ∈ G.edges) (hT : e ⊆ T) :
    ∃ d ∈ (G.pullback (Function.Embedding.subtype (· ∈ T))).edges,
      d.image Subtype.val = e := by
  classical
  let d : Finset T := Finset.univ.filter (fun v => v.val ∈ e)
  have hd : d.image Subtype.val = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v, hT hv⟩, by simp [d, hv], rfl⟩
  refine ⟨d, (G.mem_pullback _ _).mpr ⟨?_, ?_⟩, hd⟩
  · have hc := congrArg Finset.card hd
    rw [Finset.card_image_of_injective _ Subtype.val_injective, G.uniform e he] at hc
    exact hc
  · rw [Finset.map_eq_image]
    change d.image Subtype.val ∈ G.edges
    rw [hd]
    exact he

/-- A homomorphism into a complete link survives an induced restriction
whenever its entire vertex image is retained. -/
theorem coreLink_hom_into_subset {X : Type w} [DecidableEq X]
    (P : RGraph X 3) (G : RGraph V r) (T : Finset V) (U : Finset T)
    {f : X → {v // v ∉ U.image Subtype.val}}
    (hf : P.IsHom (G.coreLink (U.image Subtype.val)) f)
    (hrange : ∀ x, (f x).val ∈ T) :
    ∃ g, P.IsHom
      ((G.pullback (Function.Embedding.subtype (· ∈ T))).coreLink U) g := by
  classical
  let g : X → {v : T // v ∉ U} := fun x =>
    ⟨⟨(f x).val, hrange x⟩, fun h => (f x).property
      (Finset.mem_image.mpr ⟨_, h, rfl⟩)⟩
  refine ⟨g, ?_⟩
  intro e he
  have hh := (G.mem_coreLink _ _).mp (hf e he)
  apply (mem_coreLink _ U _).mpr
  have hg : Set.InjOn g (e : Set X) := by
    intro a ha b hb hab
    apply hf.injOn_edge he ha hb
    exact Subtype.ext (congrArg (fun v : {v : T // v ∉ U} => v.val.val) hab)
  refine ⟨by rw [Finset.card_image_of_injOn hg, P.uniform e he], ?_⟩
  apply (G.mem_pullback _ _).mpr
  have hmap : (U ∪ (e.image g).image Subtype.val).map
      (Function.Embedding.subtype (· ∈ T)) ∈ G.edges := by
    simpa [Finset.map_eq_image, Finset.image_union, Finset.image_image,
      Function.comp_def, g] using hh.2
  exact ⟨by simpa only [Finset.card_map] using G.uniform _ hmap, hmap⟩

end RGraph

namespace Uniformity

variable {V : Type u} {W : Type v} {X : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq X]
  [Fintype V] [Fintype W] [Fintype X] {r : ℕ}

/-- Edgeless graphs and common-core suspensions whose complete link admits
no homomorphism from `P`. -/
def Admissible (P : RGraph X 3) (G : RGraph V r) : Prop :=
  G.edges = ∅ ∨ ∃ S : Finset V, G.IsCore S ∧ P.HomFree (G.coreLink S)

instance (P : RGraph X 3) (G : RGraph V r) : Decidable (Admissible P G) := by
  unfold Admissible RGraph.HomFree
  infer_instance

theorem Admissible.edgeless (P : RGraph X 3) (G : RGraph V r)
    (h : G.edges = ∅) : Admissible P G := Or.inl h

/-- The suspension class is hereditary for ordinary embeddings, including
the global injectivity condition on isolated vertices. -/
theorem Admissible.of_embedding {P : RGraph X 3} {F : RGraph V r}
    {G : RGraph W r} {f : V → W} (hG : Admissible P G)
    (hf : F.IsEmbedding G f) : Admissible P F := by
  classical
  by_cases hF : F.edges = ∅
  · exact Or.inl hF
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  rcases hG with hG | ⟨S, hS, hfree⟩
  · have h := hf.2 e₀ he₀
    rw [hG] at h
    exact False.elim (Finset.notMem_empty _ h)
  let T : Finset V := Finset.univ.filter (fun v => f v ∈ S)
  have hT (v : V) : v ∈ T ↔ f v ∈ S := by simp [T]
  have hTS : T.image f = S := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact (hT v).mp hv
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hS.subset _ (hf.2 _ he₀) hw)
      exact Finset.mem_image.mpr ⟨v, (hT v).mpr hw, rfl⟩
  have hcore : F.IsCore T := by
    refine ⟨?_, ?_⟩
    · have hc := congrArg Finset.card hTS
      rw [Finset.card_image_of_injective _ hf.1] at hc
      have := hS.card
      omega
    · intro e he v hv
      have hfv : f v ∈ e.image f := hS.subset _ (hf.2 e he) ((hT v).mp hv)
      simpa only [Finset.mem_image, hf.1.eq_iff, exists_eq_right] using hfv
  obtain ⟨g, hg, _⟩ := RGraph.coreLink_embedding hf hTS
  refine Or.inr ⟨T, hcore, ?_⟩
  rintro ⟨a, ha⟩
  exact hfree ⟨g ∘ a, hg.isHom.comp ha⟩

theorem admissible_classMonotone (P : RGraph X 3) (r : ℕ) :
    FiniteGraph.ClassMonotone (fun G : FiniteGraph r => Admissible P G.2) := by
  rintro A G ⟨f, hf⟩ hG
  exact hG.of_embedding hf

end Uniformity
end TuranUniversality
