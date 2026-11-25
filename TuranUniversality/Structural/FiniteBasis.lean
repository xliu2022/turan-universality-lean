module

public import TuranUniversality.Structural.RootedTransport

@[expose] public section

/-! # The finite ordinary forbidden basis for the structural admissible class

This module proves the mathematical finite-basis statement from actual
rooted failures and ordinary embeddings. Primitive-recursive numeric
checkers are a separate layer and are not assumed here.
-/

namespace TuranUniversality.Structural.Rooted

open Cube Support

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem edgeless_admits (B : Finset (FiniteGraph 3))
    (hedges : ∀ F ∈ B, F.2.edges.Nonempty) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (hG : G.edges = ∅) : Admits B Ω G := by
  refine ⟨Rooting.empty, ?_⟩
  refine ⟨?_, ?_⟩
  · simp [hG]
  · intro S hS hnone hcard
    refine ⟨LegalObject.empty B hedges ∅, ?_, ?_⟩
    · simp [LegalObject.empty]
    · simp [hG]

theorem admits_classMonotone (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ) :
    FiniteGraph.ClassMonotone (fun G : FiniteGraph (t + (3 * b + 4)) => Admits B Ω G.2) := by
  rintro F G ⟨f, hf⟩ hG
  exact Admits.of_embedding B Ω hdis hf hG

theorem bounded_nonadmissible (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : FiniteGraph (t + (3 * b + 4))) (hG : ¬ Admits B Ω G.2) :
    ∃ F : FiniteGraph (t + (3 * b + 4)), F.1 ≤ obstructionBound b t B ∧
      ¬ Admits B Ω F.2 ∧ F.Contains G := by
  classical
  obtain ⟨T, hT, hbad⟩ := bounded_nonadmissible_subgraph B Ω hdis G.2 hG
  let J := G.2.pullback (Function.Embedding.subtype (· ∈ T))
  let e : Fin T.card ≃ T := Fintype.equivOfCardEq (by simp)
  let K := J.pullback e.toEmbedding
  refine ⟨⟨T.card, K⟩, hT, ?_, ?_⟩
  · intro h
    exact hbad (Admits.of_embedding B Ω hdis (J.pullback_equiv_inverse e) h)
  · exact ⟨Subtype.val ∘ e,
      (show J.IsEmbedding G.2 Subtype.val from
        ⟨Subtype.val_injective, G.2.pullback_isHom _⟩).comp (J.pullback_equiv_embedding e)⟩

noncomputable def basis (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b)) (t : ℕ) :
    Finset (FiniteGraph (t + (3 * b + 4))) := by
  classical
  exact FiniteGraph.forbiddenBasis (fun G : FiniteGraph (t + (3 * b + 4)) => Admits B Ω G.2)
    (obstructionBound b t B)

@[simp] theorem mem_basis (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b)) (t : ℕ)
    (F : FiniteGraph (t + (3 * b + 4))) :
    F ∈ basis B Ω t ↔ F.1 ≤ obstructionBound b t B ∧ ¬ Admits B Ω F.2 := by
  classical
  simp [basis]

theorem basis_has_edges (B : Finset (FiniteGraph 3))
    (hedges : ∀ F ∈ B, F.2.edges.Nonempty) (Ω : Label → Finset (Word b)) (t : ℕ)
    {F : FiniteGraph (t + (3 * b + 4))} (hF : F ∈ basis B Ω t) : F.2.edges.Nonempty := by
  by_contra h
  exact ((mem_basis B Ω t F).mp hF).2
    (edgeless_admits B hedges Ω F.2 (Finset.not_nonempty_iff_eq_empty.mp h))

theorem basis_spec (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (G : FiniteGraph (t + (3 * b + 4))) :
    Admits B Ω G.2 ↔ familyFree (basis B Ω t) G.2 := by
  classical
  exact FiniteGraph.forbiddenBasis_spec _ _ (admits_classMonotone B Ω hdis t)
    (bounded_nonadmissible B Ω hdis) G

theorem basis_spec_finite (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (G : RGraph V (t + (3 * b + 4))) :
    Admits B Ω G ↔ familyFree (basis B Ω t) G := by
  classical
  let e := (Fintype.equivFin V).symm
  let K := G.pullback e.toEmbedding
  constructor
  · intro h F hF ⟨f, hf⟩
    exact ((mem_basis B Ω t F).mp hF).2 (Admits.of_embedding B Ω hdis hf h)
  · intro h
    have hK : familyFree (basis B Ω t) K :=
      familyFree_of_embedding _ _ G (G.pullback_equiv_embedding e) h
    have ha := (basis_spec B Ω hdis t ⟨Fintype.card V, K⟩).mpr hK
    exact Admits.of_embedding B Ω hdis (G.pullback_equiv_inverse e) ha

end TuranUniversality.Structural.Rooted
