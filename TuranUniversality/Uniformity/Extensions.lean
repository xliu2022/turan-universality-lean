module

public import TuranUniversality.Uniformity.Admissible
public import TuranUniversality.Density.FamilyBasic

@[expose] public section

/-! # All finite pair-covering extensions

Auxiliary vertices may be shared between covering edges. This is what makes
the extension obtained in a pair-covered host an ordinary embedded subgraph.
-/

namespace TuranUniversality.Uniformity

universe u v w
variable {V : Type u} {W : Type v} {X : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq X] {r : ℕ}

def NoIsolates (G : RGraph V r) : Prop := ∀ v, ∃ e ∈ G.edges, v ∈ e

def CoversImagePairs (G : RGraph W r) (f : V → W) : Prop :=
  ∀ u v, u ≠ v → ∃ e ∈ G.edges, f u ∈ e ∧ f v ∈ e

/-- An ordinary embedded core with all of its pairs covered. -/
def IsExtension (A : RGraph V r) (E : RGraph W r) : Prop :=
  NoIsolates E ∧ ∃ f, A.IsEmbedding E f ∧ CoversImagePairs E f

instance [Fintype V] [Fintype W] (A : RGraph V r) (E : RGraph W r) :
    Decidable (IsExtension A E) := by
  unfold IsExtension NoIsolates CoversImagePairs
  infer_instance

def extensionBound (r n : ℕ) : ℕ := n + (r - 2) * n.choose 2

/-- Every labeled extension within the proven order bound. -/
def extensions (A : FiniteGraph r) : Finset (FiniteGraph r) :=
  (FiniteGraph.bounded r (extensionBound r A.1)).filter
    (fun E => IsExtension A.2 E.2)

@[simp] theorem mem_extensions (A E : FiniteGraph r) :
    E ∈ extensions A ↔ E.1 ≤ extensionBound r A.1 ∧ IsExtension A.2 E.2 := by
  simp [extensions]

theorem IsExtension.core_embedding_of_hom {A : RGraph V r} {E : RGraph W r}
    {G : RGraph X r} (hext : IsExtension A E) {g : W → X} (hg : E.IsHom G g) :
    ∃ f, A.IsEmbedding G f := by
  obtain ⟨_, f, hf, hcover⟩ := hext
  refine ⟨g ∘ f, ⟨?_, hg.comp hf.isHom⟩⟩
  intro u v huv
  by_contra hne
  obtain ⟨e, he, hu, hv⟩ := hcover u v hne
  exact hne (hf.1 (hg.injOn_edge he hu hv huv))

theorem extensions_has_edges (A : FiniteGraph r) (hA : A.2.edges.Nonempty)
    {E : FiniteGraph r} (hE : E ∈ extensions A) : E.2.edges.Nonempty := by
  obtain ⟨e, he⟩ := hA
  obtain ⟨_, f, hf, _⟩ := ((mem_extensions A E).mp hE).2
  exact ⟨e.image f, hf.2 e he⟩

/-- A pair-covered host that contains a core contains an ordinary extension
of that core, with at most `r - 2` extra vertices for each unordered pair. -/
theorem exists_embedded_extension [Fintype V] (A : FiniteGraph r)
    (G : RGraph V r) (hr : 2 ≤ r) (hA : A.2.edges.Nonempty)
    (hG : G.CoversPairs) {f : Fin A.1 → V} (hf : A.2.IsEmbedding G f) :
    ∃ E ∈ extensions A, ∃ g, E.2.IsEmbedding G g := by
  classical
  have hcard : 2 ≤ A.1 := by
    obtain ⟨e, he⟩ := hA
    have h := Finset.card_le_univ e
    rw [A.2.uniform e he, Fintype.card_fin] at h
    omega
  haveI : Nontrivial (Fin A.1) :=
    ⟨Fintype.one_lt_card_iff.mp (by rw [Fintype.card_fin]; omega)⟩
  let pairs := (Finset.univ : Finset (Fin A.1)).powersetCard 2
  have hchoice (p : pairs) : ∃ e ∈ G.edges, p.val.image f ⊆ e := by
    obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp p.property).2
    obtain ⟨e, he, ha, hb⟩ := hG (f a) (f b) (fun h => hab (hf.1 h))
    refine ⟨e, he, ?_⟩
    simpa [hp, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
  choose edge hedge hpair using hchoice
  let extra (p : pairs) := edge p \ p.val.image f
  have hextra (p : pairs) : (extra p).card = r - 2 := by
    rw [Finset.card_sdiff_of_subset (hpair p), G.uniform _ (hedge p),
      Finset.card_image_of_injective _ hf.1, (Finset.mem_powersetCard.mp p.property).2]
  let T : Finset V := Finset.univ.image f ∪ Finset.univ.biUnion extra
  have hfT (a : Fin A.1) : f a ∈ T := Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  have hedgeT (p : pairs) : edge p ⊆ T := by
    intro v hv
    by_cases hp : v ∈ p.val.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact hfT a
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hv, hp⟩⟩)
  have hsize : T.card ≤ extensionBound r A.1 := by
    calc
      T.card ≤ (Finset.univ.image f).card + (Finset.univ.biUnion extra).card :=
        Finset.card_union_le _ _
      _ ≤ A.1 + (Finset.univ : Finset pairs).card * (r - 2) := by
        simp only [Finset.card_image_of_injective _ hf.1, Finset.card_univ,
          Fintype.card_fin]
        exact Nat.add_le_add_left
          (Finset.card_biUnion_le_card_mul _ _ _ (fun p _ => (hextra p).le)) _
      _ = extensionBound r A.1 := by
        simp [extensionBound, pairs, Finset.card_powersetCard, Nat.mul_comm]
  let J := G.pullback (Function.Embedding.subtype (· ∈ T))
  let fT : Fin A.1 → T := fun a => ⟨f a, hfT a⟩
  have hJ : A.2.IsEmbedding J fT := A.2.embedding_into_subset G T hf hfT
  have hpJ (p : pairs) : ∃ d ∈ J.edges, ∀ a ∈ p.val, fT a ∈ d := by
    obtain ⟨d, hd, hde⟩ := G.exists_pullback_edge T (hedge p) (hedgeT p)
    refine ⟨d, hd, ?_⟩
    intro a ha
    have hfa : f a ∈ d.image Subtype.val := hde ▸ hpair p (Finset.mem_image_of_mem f ha)
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hfa
    have heq' : v = fT a := Subtype.ext heq
    exact heq' ▸ hv
  have hcoverJ : CoversImagePairs J fT := by
    intro a b hab
    let p : pairs := ⟨{a, b}, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by simp [hab]⟩⟩
    obtain ⟨d, hd, hp⟩ := hpJ p
    exact ⟨d, hd, hp a (by simp [p]), hp b (by simp [p])⟩
  have hnoJ : NoIsolates J := by
    intro v
    rcases Finset.mem_union.mp v.property with hv | hv
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
      obtain ⟨b, hba⟩ := exists_ne a
      obtain ⟨d, hd, hda, _⟩ := hcoverJ a b (Ne.symm hba)
      refine ⟨d, hd, ?_⟩
      have heq : fT a = v := Subtype.ext ha
      exact heq ▸ hda
    · obtain ⟨p, _, hvp⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨d, hd, hde⟩ := G.exists_pullback_edge T (hedge p) (hedgeT p)
      have hvd : v.val ∈ d.image Subtype.val := hde ▸ (Finset.mem_sdiff.mp hvp).1
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hvd
      exact ⟨d, hd, (Subtype.ext hweq : w = v) ▸ hw⟩
  let e : Fin T.card ≃ T := Fintype.equivOfCardEq (by simp)
  let K := J.pullback e.toEmbedding
  have hi := J.pullback_equiv_inverse e
  have hnoK : NoIsolates K := by
    intro v
    obtain ⟨d, hd, hv⟩ := hnoJ (e v)
    exact ⟨d.image e.symm, hi.2 d hd,
      Finset.mem_image.mpr ⟨e v, hv, by simp⟩⟩
  have hcovK : CoversImagePairs K (e.symm ∘ fT) := by
    intro a b hab
    obtain ⟨d, hd, ha, hb⟩ := hcoverJ a b hab
    exact ⟨d.image e.symm, hi.2 d hd,
      Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩
  refine ⟨⟨T.card, K⟩, (mem_extensions _ _).mpr
    ⟨hsize, hnoK, e.symm ∘ fT, hi.comp hJ, hcovK⟩, ?_⟩
  exact ⟨Subtype.val ∘ e,
    (show J.IsEmbedding G Subtype.val from
      ⟨Subtype.val_injective, G.pullback_isHom _⟩).comp (J.pullback_equiv_embedding e)⟩

end TuranUniversality.Uniformity
