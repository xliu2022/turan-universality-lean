module

public import TuranUniversality.Uniformity.Admissible
public import TuranUniversality.Density.FamilyBasic

@[expose] public section

/-! # Explicit finite obstructions for the suspension class

One reference edge contains every candidate common core. Each candidate is
destroyed by one edge or by the image of a homomorphism from the three-graph.
-/

namespace TuranUniversality.Uniformity

open scoped BigOperators

universe u v
variable {V : Type u} {X : Type v} [DecidableEq V] [DecidableEq X]
  [Fintype V] [Fintype X] {r : ℕ}

def obstructionBound (r p : ℕ) : ℕ := r + r.choose 3 * max r p

/-- Retained vertices that rule out a particular proposed common core. -/
def CoreFailure (P : RGraph X 3) (G : RGraph V r) (S W : Finset V) : Prop :=
  (∃ e ∈ G.edges, e ⊆ W ∧ ¬ S ⊆ e) ∨
  ∃ f : X → {v // v ∉ S}, P.IsHom (G.coreLink S) f ∧
    ∀ x, (f x).val ∈ W

theorem exists_core_failure (P : RGraph X 3) (G : RGraph V r)
    (hG : ¬ Admissible P G) (S : Finset V) (hcard : S.card + 3 = r) :
    ∃ W : Finset V, W.card ≤ max r (Fintype.card X) ∧ CoreFailure P G S W := by
  classical
  by_cases hc : ∀ e ∈ G.edges, S ⊆ e
  · have hn : ¬ P.HomFree (G.coreLink S) :=
      fun h => hG (Or.inr ⟨S, ⟨hcard, hc⟩, h⟩)
    obtain ⟨f, hf⟩ : ∃ f, P.IsHom (G.coreLink S) f := not_not.mp hn
    refine ⟨Finset.univ.image (fun x => (f x).val), ?_, Or.inr ⟨f, hf, ?_⟩⟩
    · exact (Finset.card_image_le.trans (by simp)).trans (Nat.le_max_right _ _)
    · intro x
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · push Not at hc
    obtain ⟨e, he, hnot⟩ := hc
    exact ⟨e, by rw [G.uniform e he]; exact Nat.le_max_left _ _,
      Or.inl ⟨e, he, Finset.Subset.refl _, hnot⟩⟩

/-- The exact bounded induced obstruction from the suspension construction. -/
theorem small_nonadmissible_subgraph (P : RGraph X 3) (G : RGraph V r)
    (hr : 3 ≤ r) (hG : ¬ Admissible P G) :
    ∃ T : Finset V, T.card ≤ obstructionBound r (Fintype.card X) ∧
      ¬ Admissible P (G.pullback (Function.Embedding.subtype (· ∈ T))) := by
  classical
  have hne : G.edges ≠ ∅ := fun h => hG (Or.inl h)
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  let candidates := e₀.powersetCard (r - 3)
  have hw (S : candidates) : ∃ W : Finset V,
      W.card ≤ max r (Fintype.card X) ∧ CoreFailure P G S.val W := by
    apply exists_core_failure P G hG S.val
    have hc := (Finset.mem_powersetCard.mp S.property).2
    omega
  choose W hW using hw
  let T : Finset V := e₀ ∪ Finset.univ.biUnion W
  have heT : e₀ ⊆ T := Finset.subset_union_left
  have hWT (S : candidates) : W S ⊆ T := by
    intro v hv
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨S, Finset.mem_univ _, hv⟩)
  have hcandidates : Fintype.card candidates = r.choose 3 := by
    simp only [Fintype.card_coe, candidates, Finset.card_powersetCard,
      G.uniform e₀ he₀, Nat.choose_symm hr]
  have hsize : T.card ≤ obstructionBound r (Fintype.card X) := by
    calc
      T.card ≤ e₀.card + (Finset.univ.biUnion W).card := Finset.card_union_le _ _
      _ ≤ r + (Finset.univ : Finset candidates).card * max r (Fintype.card X) := by
        rw [G.uniform e₀ he₀]
        exact Nat.add_le_add_left
          (Finset.card_biUnion_le_card_mul _ _ _ (fun S _ => (hW S).1)) _
      _ = obstructionBound r (Fintype.card X) := by
        simp only [Finset.card_univ, hcandidates, obstructionBound]
  refine ⟨T, hsize, ?_⟩
  let K := G.pullback (Function.Embedding.subtype (· ∈ T))
  obtain ⟨d₀, hd₀, hde₀⟩ := G.exists_pullback_edge T he₀ heT
  rintro (hempty | ⟨U, hU, hfree⟩)
  · rw [hempty] at hd₀
    exact Finset.notMem_empty _ hd₀
  let S : Finset V := U.image Subtype.val
  have hScard : S.card + 3 = r := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hU.card
  have hSe : S ⊆ e₀ := by
    rw [← hde₀]
    exact Finset.image_mono _ (hU.subset d₀ hd₀)
  have hSmem : S ∈ candidates := Finset.mem_powersetCard.mpr ⟨hSe, by omega⟩
  let c : candidates := ⟨S, hSmem⟩
  rcases (hW c).2 with ⟨e, he, heW, hnot⟩ | ⟨f, hf, hfW⟩
  · obtain ⟨d, hd, hde⟩ := G.exists_pullback_edge T he (heW.trans (hWT c))
    apply hnot
    change U.image Subtype.val ⊆ e
    rw [← hde]
    exact Finset.image_mono _ (hU.subset d hd)
  · obtain ⟨g, hg⟩ := RGraph.coreLink_hom_into_subset P G T U hf
      (fun x => hWT c (hfW x))
    exact hfree ⟨g, hg⟩

/-- Relabel the actual induced witness onto its full finite vertex set. -/
theorem bounded_nonadmissible (P : RGraph X 3) (r : ℕ) (hr : 3 ≤ r)
    (G : FiniteGraph r) (hG : ¬ Admissible P G.2) :
    ∃ A : FiniteGraph r, A.1 ≤ obstructionBound r (Fintype.card X) ∧
      ¬ Admissible P A.2 ∧ A.Contains G := by
  classical
  obtain ⟨T, hT, hbad⟩ := small_nonadmissible_subgraph P G.2 hr hG
  let J := G.2.pullback (Function.Embedding.subtype (· ∈ T))
  let e : Fin T.card ≃ T := Fintype.equivOfCardEq (by simp)
  let K := J.pullback e.toEmbedding
  refine ⟨⟨T.card, K⟩, hT, ?_, ?_⟩
  · intro h
    exact hbad (h.of_embedding (J.pullback_equiv_inverse e))
  · exact ⟨Subtype.val ∘ e,
      (show J.IsEmbedding G.2 Subtype.val from
        ⟨Subtype.val_injective, G.2.pullback_isHom _⟩).comp
          (J.pullback_equiv_embedding e)⟩

/-- All bounded labeled nonmembers, with no isomorphism quotient required. -/
def basis (P : FiniteGraph 3) (r : ℕ) : Finset (FiniteGraph r) :=
  FiniteGraph.forbiddenBasis (fun G : FiniteGraph r => Admissible P.2 G.2)
    (obstructionBound r P.1)

@[simp] theorem mem_basis (P : FiniteGraph 3) (r : ℕ) (A : FiniteGraph r) :
    A ∈ basis P r ↔ A.1 ≤ obstructionBound r P.1 ∧ ¬ Admissible P.2 A.2 := by
  simp [basis]

theorem basis_has_edges (P : FiniteGraph 3) (r : ℕ)
    {A : FiniteGraph r} (hA : A ∈ basis P r) : A.2.edges.Nonempty := by
  by_contra h
  exact ((mem_basis P r A).mp hA).2
    (Or.inl (Finset.not_nonempty_iff_eq_empty.mp h))

theorem basis_spec (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r) (G : FiniteGraph r) :
    Admissible P.2 G.2 ↔ familyFree (basis P r) G.2 := by
  exact FiniteGraph.forbiddenBasis_spec _ _ (admissible_classMonotone P.2 r)
    (by simpa only [Fintype.card_fin] using bounded_nonadmissible P.2 r hr) G

/-- The finite-basis specification also holds on any finite vertex type. -/
theorem basis_spec_finite (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r)
    (G : RGraph V r) : Admissible P.2 G ↔ familyFree (basis P r) G := by
  classical
  let e := (Fintype.equivFin V).symm
  let K := G.pullback e.toEmbedding
  constructor
  · intro h A hA ⟨f, hf⟩
    exact ((mem_basis P r A).mp hA).2 (h.of_embedding hf)
  · intro h
    have hK : familyFree (basis P r) K :=
      familyFree_of_embedding _ _ G (G.pullback_equiv_embedding e) h
    have ha := (basis_spec P r hr ⟨Fintype.card V, K⟩).mpr hK
    exact ha.of_embedding (G.pullback_equiv_inverse e)

end TuranUniversality.Uniformity
