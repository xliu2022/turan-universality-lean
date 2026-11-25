/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootingWitness
public import TuranUniversality.Hypergraph.GuardedBasis

/-! # The actual finite forbidden basis for legal partial rootings -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

variable {Roots Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Fintype Code] [DecidableEq Code]
    [Fintype Kinds] [DecidableEq Kinds] [Inhabited Alphabet] [DecidableEq Alphabet]

/-- Admissibility of a labeled finite graph means that an actual partial
rooting satisfies all incidence and computational rules. -/
def admissibleClass (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (spec : Specification Alphabet) (G : FiniteGraph 3) : Prop :=
  Admissible S color spec G.2

theorem admissibleClass_monotone (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) :
    FiniteGraph.ClassMonotone (admissibleClass S color spec) := by
  rintro A G ⟨f, hf⟩ hG
  exact Admissible.of_embedding S color spec A.2 G.2 hG f hf

/-- The finite search witness can be relabeled by its actual vertex count.
Thus it belongs to the finite enumeration used by the forbidden basis. -/
theorem admissibleClass_bounded (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (G : FiniteGraph 3)
    (hG : ¬ admissibleClass S color spec G) :
    ∃ A : FiniteGraph 3, A.1 ≤ admissibleWitnessBound Roots spec ∧
      ¬ admissibleClass S color spec A ∧ A.Contains G := by
  classical
  obtain ⟨T, hT, hbad⟩ := bounded_nonadmissible_subgraph S color spec G.2 hG
  let J := G.2.pullback (Function.Embedding.subtype (· ∈ T))
  let e : Fin T.card ≃ T := Fintype.equivOfCardEq (by simp)
  let K := J.pullback e.toEmbedding
  refine ⟨⟨T.card, K⟩, hT, ?_, ?_⟩
  · intro hK
    exact hbad (Admissible.of_embedding S color spec J K hK e.symm
      (J.pullback_equiv_inverse e))
  · exact ⟨Subtype.val ∘ e, Subtype.val_injective.comp e.injective,
      (G.2.pullback_isHom _).comp (J.pullback_isHom e.toEmbedding)⟩

/-- All inadmissible labeled graphs up to the proved search bound.
The separate encoding development supplies an effective decision procedure. -/
noncomputable def admissibleBasis (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) : Finset (FiniteGraph 3) := by
  classical
  exact FiniteGraph.forbiddenBasis (admissibleClass S color spec)
    (admissibleWitnessBound Roots spec)

theorem mem_admissibleBasis (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (A : FiniteGraph 3) :
    A ∈ admissibleBasis S color spec ↔ A.1 ≤ admissibleWitnessBound Roots spec ∧
      ¬ admissibleClass S color spec A := by
  classical
  exact FiniteGraph.mem_forbiddenBasis _ _ _

/-- Exact ordinary subgraph avoidance for the actual partial-rooting class. -/
theorem admissibleBasis_spec (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (G : FiniteGraph 3) :
    admissibleClass S color spec G ↔
      ∀ A ∈ admissibleBasis S color spec, ¬ A.Contains G := by
  classical
  exact FiniteGraph.forbiddenBasis_spec _ _ (admissibleClass_monotone S color spec)
    (admissibleClass_bounded S color spec) G

/-- Bounded forbidden cores each of which also contains the fixed guard. -/
noncomputable def guardedAdmissibleBasis (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (H : FiniteGraph 3) :
    Finset (FiniteGraph 3) := by
  classical
  exact FiniteGraph.guardedBasis (admissibleClass S color spec)
    (admissibleWitnessBound Roots spec) H

theorem mem_guardedAdmissibleBasis (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (H A : FiniteGraph 3) :
    A ∈ guardedAdmissibleBasis S color spec H ↔
      A.1 ≤ admissibleWitnessBound Roots spec + H.1 ∧
      ¬ admissibleClass S color spec A ∧ H.Contains A := by
  classical
  simp only [guardedAdmissibleBasis, FiniteGraph.guardedBasis,
    FiniteGraph.mem_forbiddenBasis, FiniteGraph.guardedClass, not_or, not_not]

theorem guardedAdmissibleBasis_contains_guard (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (H : FiniteGraph 3)
    {A : FiniteGraph 3} (hA : A ∈ guardedAdmissibleBasis S color spec H) :
    ¬ admissibleClass S color spec A ∧ H.Contains A :=
  ((mem_guardedAdmissibleBasis S color spec H A).mp hA).2

/-- A graph avoids every guarded core precisely when it has a legal
partial rooting or it avoids the guard. -/
theorem guardedAdmissibleBasis_spec (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (H G : FiniteGraph 3) :
    admissibleClass S color spec G ∨ ¬ H.Contains G ↔
      ∀ A ∈ guardedAdmissibleBasis S color spec H, ¬ A.Contains G := by
  classical
  exact FiniteGraph.guardedBasis_spec _ (admissibleClass_monotone S color spec) _
    (admissibleClass_bounded S color spec) H G

/-- Every guarded core has an edge whenever the fixed guard has an edge. -/
theorem guardedAdmissibleBasis_has_edges (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (H : FiniteGraph 3)
    (hH : H.2.edges.Nonempty) {A : FiniteGraph 3}
    (hA : A ∈ guardedAdmissibleBasis S color spec H) : A.2.edges.Nonempty := by
  obtain ⟨f, hf⟩ := (guardedAdmissibleBasis_contains_guard S color spec H hA).2
  obtain ⟨e, he⟩ := hH
  exact ⟨e.image f, hf.2 e he⟩

end TuranUniversality.Selector
