module

public import TuranUniversality.Hypergraph.Restriction

@[expose] public section

/-! # Finite relabeling and small subgraphs containing two embedded sources -/

namespace TuranUniversality

open scoped BigOperators

universe u v w z

namespace RGraph

variable {U : Type u} {V : Type v} {W : Type w} {X : Type z}
variable [DecidableEq U] [DecidableEq V] [DecidableEq W] [DecidableEq X] {r : ℕ}

theorem pullback_equiv_embedding [Fintype V] (G : RGraph W r) (e : V ≃ W) :
    (G.pullback e.toEmbedding).IsEmbedding G e :=
  ⟨e.injective, G.pullback_isHom e.toEmbedding⟩

theorem pullback_equiv_inverse [Fintype V] (G : RGraph W r) (e : V ≃ W) :
    G.IsEmbedding (G.pullback e.toEmbedding) e.symm := by
  refine ⟨e.symm.injective, ?_⟩
  intro d hd
  apply (G.mem_pullback _ _).mpr
  constructor
  · rw [Finset.card_image_of_injective _ e.symm.injective]
    exact G.uniform d hd
  · simpa [Finset.map_eq_image, Finset.image_image, Function.comp_def] using hd

theorem pullback_equiv_polynomial [Fintype V] (G : RGraph W r) (e : V ≃ W)
    (x : W → ℝ) :
    (G.pullback e.toEmbedding).edgePolynomial (x ∘ e) = G.edgePolynomial x := by
  apply G.edgePolynomial_pullback
  intro w hw
  exact False.elim (hw (e.surjective w))

theorem embedding_into_subset [Fintype V] (F : RGraph U r) (G : RGraph V r)
    (S : Finset V) {f : U → V} (hf : F.IsEmbedding G f) (hS : ∀ u, f u ∈ S) :
    F.IsEmbedding (G.pullback (Function.Embedding.subtype (· ∈ S)))
      (fun u => ⟨f u, hS u⟩) := by
  classical
  let g : U → S := fun u => ⟨f u, hS u⟩
  have hg : Function.Injective g := fun a b h => hf.1 (congrArg Subtype.val h)
  refine ⟨hg, ?_⟩
  intro d hd
  apply (G.mem_pullback _ _).mpr
  constructor
  · rw [Finset.card_image_of_injective _ hg]
    exact F.uniform d hd
  · simpa [Finset.map_eq_image, Finset.image_image, Function.comp_def] using hf.2 d hd

/-- The union of the two vertex images gives a subgraph of order at most the
sum of the two source orders, containing both embedded sources. -/
theorem joint_embedded_subgraph [Fintype U] [Fintype V] [Fintype W]
    (A : RGraph U r) (B : RGraph V r) (G : RGraph W r)
    {f : U → W} {g : V → W} (hf : A.IsEmbedding G f) (hg : B.IsEmbedding G g) :
    ∃ (k : ℕ) (K : RGraph (Fin k) r), k ≤ Fintype.card U + Fintype.card V ∧
      (∃ a, A.IsEmbedding K a) ∧ (∃ b, B.IsEmbedding K b) ∧
      (∃ t, K.IsEmbedding G t) := by
  classical
  let S := Finset.univ.image f ∪ Finset.univ.image g
  let J := G.pullback (Function.Embedding.subtype (· ∈ S))
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let K := J.pullback e.toEmbedding
  have hsize : S.card ≤ Fintype.card U + Fintype.card V := by
    calc
      S.card ≤ (Finset.univ.image f).card + (Finset.univ.image g).card := Finset.card_union_le _ _
      _ ≤ (Finset.univ : Finset U).card + (Finset.univ : Finset V).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = _ := by simp
  have hfa : ∀ a, f a ∈ S := fun a => Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  have hgb : ∀ b, g b ∈ S := fun b => Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  have ha := (J.pullback_equiv_inverse e).comp (A.embedding_into_subset G S hf hfa)
  have hb := (J.pullback_equiv_inverse e).comp (B.embedding_into_subset G S hg hgb)
  have ht : K.IsEmbedding G (Subtype.val ∘ e) :=
    ⟨Subtype.val_injective.comp e.injective,
      (G.pullback_isHom _).comp (J.pullback_isHom e.toEmbedding)⟩
  exact ⟨S.card, K, hsize, ⟨_, ha⟩, ⟨_, hb⟩, ⟨_, ht⟩⟩

end RGraph

theorem probabilityWeights_equiv {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (e : V ≃ W) (x : W → ℝ) (hx : ProbabilityWeights x) : ProbabilityWeights (x ∘ e) := by
  refine ⟨fun v => hx.1 (e v), ?_⟩
  calc
    (∑ v, (x ∘ e) v) = ∑ w, x w := Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = 1 := hx.2

end TuranUniversality
