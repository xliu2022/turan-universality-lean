/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.MarkerRecovery

/-! # Pulling back all concrete rooted incidence rules -/

@[expose] public section

namespace TuranUniversality.Selector.RowRootingPlan

open Weighted

variable {I X Roots Data Code Blocks Kinds : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [Fintype Roots] [DecidableEq Roots] [Fintype Data] [DecidableEq Data]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds] {L : ℕ}
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

omit [Fintype Kinds] in
theorem unionRelation_domain (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmatching : ∀ e, S.IsMatching target e) (e : Fin 3) (x y : X)
    (hp : (x, y) ∈ S.unionRelation (P.model A) e) :
    x ∈ P.recoveredDomain ∧ y ∈ P.recoveredDomain := by
  obtain ⟨ℓ, hℓ⟩ := (S.mem_unionRelation (P.model A) e (x, y)).mp hp
  exact P.relation_copy_domain S A target hdeclared hcross hinside hmatching e ℓ x y hℓ

omit [Fintype Kinds] in
theorem recoveredMap_unionRelation (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmatching : ∀ e, S.IsMatching target e) (e : Fin 3) (x y : P.recoveredDomain)
    (hp : (x.val, y.val) ∈ S.unionRelation (P.model A) e) :
    (P.recoveredMap x, P.recoveredMap y) ∈ S.unionRelation target e := by
  obtain ⟨ℓ, hℓ⟩ := (S.mem_unionRelation (P.model A) e (x.val, y.val)).mp hp
  exact (S.mem_unionRelation target e _).mpr ⟨ℓ,
    P.recoveredMap_relationCopy S A target hdeclared hcross hinside hmatching e ℓ x y hℓ⟩

theorem matching (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmatching : ∀ e, S.IsMatching target e)
    (hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j) (e : Fin 3) :
    S.IsMatching (P.model A) e := by
  have hdomain := P.unionRelation_domain S A target hdeclared hcross hinside hmatching e
  have hpreserve := P.recoveredMap_unionRelation S A target hdeclared hcross hinside hmatching e
  have hinj := P.recoveredMap_injective hprivacy
  constructor
  · intro p hp q hq heq
    obtain ⟨hp1, hp2⟩ := hdomain p.1 p.2 hp
    obtain ⟨hq1, hq2⟩ := hdomain q.1 q.2 hq
    have hpt := hpreserve ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ hp
    have hqt := hpreserve ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hq
    have he1 : P.recoveredMap ⟨p.1, hp1⟩ = P.recoveredMap ⟨q.1, hq1⟩ :=
      congrArg P.recoveredMap (Subtype.ext heq)
    have hpair := (hmatching e).1 hpt hqt he1
    have he2 := hinj (congrArg Prod.snd hpair)
    exact Prod.ext heq (congrArg Subtype.val he2)
  · intro p hp q hq heq
    obtain ⟨hp1, hp2⟩ := hdomain p.1 p.2 hp
    obtain ⟨hq1, hq2⟩ := hdomain q.1 q.2 hq
    have hpt := hpreserve ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ hp
    have hqt := hpreserve ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hq
    have he2 : P.recoveredMap ⟨p.2, hp2⟩ = P.recoveredMap ⟨q.2, hq2⟩ :=
      congrArg P.recoveredMap (Subtype.ext heq)
    have hpair := (hmatching e).2 hpt hqt he2
    have he1 := hinj (congrArg Prod.fst hpair)
    exact Prod.ext (congrArg Subtype.val he1) heq

/-- Every H1--H4 incidence field is proved for the actual reconstructed
image graph. The computational rules are handled by the partial injection. -/
theorem incidenceLegal (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hlegal : S.IncidenceLegal target)
    (hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j) :
    S.IncidenceLegal (P.model A) where
  candidates := P.hasCandidates S.codes A target hdeclared hcross hinside
  oneRoot := P.oneRootRules S A target hdeclared hcross hinside hlegal.oneRoot
  matching := P.matching S A target hdeclared hcross hinside hlegal.matching hprivacy
  oneMarker := P.oneMarker A target hcross hlegal.oneMarker hprivacy
  markerTypes := P.markerTypes S A target hdeclared hcross hinside hlegal.markerTypes

omit [Fintype Kinds] in
theorem recoveredMap_typeClass (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (x : P.recoveredDomain) (kind : Kinds) (hx : x.val ∈ S.typeClass (P.model A) kind) :
    P.recoveredMap x ∈ S.typeClass target kind := by
  obtain ⟨c, hc, hkind⟩ := (S.codes.mem_typeVertices (P.model A) S.physical kind x.val).mp hx
  have hcode := (P.recoveredMap_code x).trans
    (P.declared_selectedCode S.codes A target hdeclared hcross hinside x.val c hc)
  apply (S.codes.mem_typeVertices target S.physical kind (P.recoveredMap x)).mpr
  exact ⟨code (P.recoveredMap x), hdeclared _, by rw [hcode]; exact hkind⟩

omit [Fintype Data] [Fintype Kinds] in
theorem marks_domain (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hcross : CrossEdges A target row) (hone : target.dataTriples.card ≤ 1) :
    S.marks (P.model A) ⊆ P.recoveredDomain := by
  intro x hx
  obtain ⟨_, p, hp, hxp⟩ := (Finset.mem_filter.mp hx).2
  exact P.dataTriple_domain A target hcross hone p hp hxp

omit [Fintype Kinds] in
theorem recoveredMap_marks (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hone : target.dataTriples.card ≤ 1) (x : P.recoveredDomain)
    (hx : x.val ∈ S.marks (P.model A)) : P.recoveredMap x ∈ S.marks target := by
  classical
  obtain ⟨hxType, p, hp, hxp⟩ := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, P.recoveredMap_typeClass S A target hdeclared hcross hinside
    x S.cellKind hxType, P.recoveredEdge p, P.recoveredEdge_mem A target hcross hone p hp, ?_⟩
  exact Finset.mem_image.mpr ⟨x, Finset.mem_subtype.mpr hxp, rfl⟩

end TuranUniversality.Selector.RowRootingPlan
