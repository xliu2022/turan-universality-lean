/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.IncidenceRecovery
public import TuranUniversality.Selector.Admissibility
public import TuranUniversality.Computation.Pullback

/-! # Pulling back the concrete Q1--Q4 computational rules -/

@[expose] public section

namespace TuranUniversality.Selector.RowRootingPlan

open Weighted Computation.MatchingSystem

variable {I X Roots Data Code Blocks Kinds Alphabet : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [Fintype Roots] [DecidableEq Roots] [Fintype Data] [DecidableEq Data]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet] {L : ℕ}
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

noncomputable def computationalPullback (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hlegal : S.IncidenceLegal target)
    (hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j)
    (color : Code → Alphabet) :
    Realization.Pullback
      (rootedRealization S (P.model A) color
        (P.incidenceLegal S A target hdeclared hcross hinside hlegal hprivacy).matching)
      (rootedRealization S target color hlegal.matching) where
  domain := P.recoveredDomain
  map := P.recoveredMap
  injective := P.recoveredMap_injective hprivacy
  J_domain := P.unionRelation_domain S A target hdeclared hcross hinside hlegal.matching 0
  R_domain := P.unionRelation_domain S A target hdeclared hcross hinside hlegal.matching 1
  S_domain := P.unionRelation_domain S A target hdeclared hcross hinside hlegal.matching 2
  marks_domain := P.marks_domain S A target hcross hlegal.oneMarker
  J_preserve := P.recoveredMap_unionRelation S A target hdeclared hcross hinside hlegal.matching 0
  R_preserve := P.recoveredMap_unionRelation S A target hdeclared hcross hinside hlegal.matching 1
  S_preserve := P.recoveredMap_unionRelation S A target hdeclared hcross hinside hlegal.matching 2
  label_preserve := by
    intro x hx
    obtain ⟨c, hc, _⟩ := (S.codes.mem_typeVertices (P.model A) S.physical S.colorKind x.val).mp hx
    change decodedLabel S target color (P.recoveredMap x) = decodedLabel S (P.model A) color x.val
    rw [decodedLabel_of_declared S target color _ _ (hdeclared (P.recoveredMap x)),
      decodedLabel_of_declared S (P.model A) color _ _ hc, P.recoveredMap_code x,
      P.declared_selectedCode S.codes A target hdeclared hcross hinside x.val c hc]
  marks_preserve := P.recoveredMap_marks S A target hdeclared hcross hinside hlegal.oneMarker

/-- Full rooted legality, including the actual Q1--Q4 rules, transfers
through the reconstructed partial injection. -/
theorem rootedLegal (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j)
    (color : Code → Alphabet) (spec : Specification Alphabet) (hlegal : RootedLegal S target color spec) :
    RootedLegal S (P.model A) color spec := by
  obtain ⟨hinc, hcomputation⟩ := hlegal
  refine ⟨P.incidenceLegal S A target hdeclared hcross hinside hinc hprivacy, ?_⟩
  exact (P.computationalPullback S A target hdeclared hcross hinside hinc hprivacy color).legal
    spec hcomputation

theorem admissible (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j)
    (color : Code → Alphabet) (spec : Specification Alphabet) (hlegal : RootedLegal S target color spec) :
    Admissible S color spec A :=
  ⟨⟨P.assignment, P.root_injective⟩,
    P.rootedLegal S A target hdeclared hcross hinside hprivacy color spec hlegal⟩

end TuranUniversality.Selector.RowRootingPlan
