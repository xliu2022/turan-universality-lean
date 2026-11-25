/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ConstraintRigidity

/-! # Recovering every declared indexed matching constraint -/

@[expose] public section

namespace TuranUniversality.Selector.RowRootingPlan

open Weighted

variable {I X Roots Data Code Blocks Kinds : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [Fintype Roots] [DecidableEq Roots] [Fintype Data] [DecidableEq Data]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds] {L : ℕ}
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

omit [DecidableEq I] [Fintype Kinds] in
theorem occurrence_typeClass (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (x : X) (kind : Kinds) (hx : x ∈ S.typeClass (P.model A) kind)
    (i : I) (hi : i ∈ codeOccurrences (row x) code (P.selectedCode x)) :
    ∃ d, row x i = Sum.inr d ∧ d ∈ S.typeClass target kind := by
  obtain ⟨c, hc, hkind⟩ := (S.codes.mem_typeVertices (P.model A) S.physical kind x).mp hx
  obtain ⟨d, hd, hcode⟩ := (mem_codeOccurrences (row x) code (P.selectedCode x) i).mp hi
  have hselected := P.declared_selectedCode S.codes A target hdeclared hcross hinside x c hc
  refine ⟨d, hd, ?_⟩
  apply (S.codes.mem_typeVertices target S.physical kind d).mpr
  exact ⟨code d, hdeclared d, by rw [hcode, hselected]; exact hkind⟩

omit [Fintype Kinds] in
/-- Binary transversal rigidity produces genuine target values for the
endpoints of an actual indexed source relation. -/
theorem relation_copy_stable (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmatching : ∀ e, S.IsMatching target e) (e : Fin 3) (ℓ : Fin L) (x y : X)
    (hp : (x, y) ∈ S.relationCopy (P.model A) e ℓ) :
    P.assignment x = none ∧ P.assignment y = none ∧
      ∃ u v, (u, v) ∈ S.relationCopy target e ℓ ∧ P.StableValue x u ∧ P.StableValue y v := by
  classical
  obtain ⟨hxtype, hytype, hedge⟩ := (S.mem_relationCopy (P.model A) e ℓ (x, y)).mp hp
  obtain ⟨z, hz, hxnone, hynone, heSource⟩ :=
    one_root_edge_witness A P.assignment P.root_injective (S.copyRoot (e, ℓ)) x y hedge
  obtain ⟨k, hk⟩ := P.root_occurs z (S.copyRoot (e, ℓ)) hz
  let allowed : Fin 2 → Finset I :=
    ![(codeOccurrences (row x) code (P.selectedCode x)).erase k,
      (codeOccurrences (row y) code (P.selectedCode y)).erase k]
  let rows : Fin 2 → I → Roots ⊕ Data := ![row x, row y]
  let E := S.relationCopy target e ℓ
  have hcard (j : Fin 2) : 3 ≤ (allowed j).card := by
    fin_cases j
    · exact three_le_card_erase _ (P.data_frequent x hxnone) k
    · exact three_le_card_erase _ (P.data_frequent y hynone) k
  have hunique : UniqueCompletion (matchingTuple (Roots := Roots) E) :=
    matchingTuple_unique E (S.copyMatching target e ℓ (hmatching e)).left_injective
      (S.copyMatching target e ℓ (hmatching e)).right_injective
  have htrans (f : Fin 2 → I) (hf : ∀ j, f j ∈ allowed j) (hfinj : Function.Injective f) :
      matchingTuple E (fun j => rows j (f j)) := by
    have hxocc : f 0 ∈ (codeOccurrences (row x) code (P.selectedCode x)).erase k := hf 0
    have hyocc : f 1 ∈ (codeOccurrences (row y) code (P.selectedCode y)).erase k := hf 1
    obtain ⟨u, hu, huType⟩ := P.occurrence_typeClass S A target hdeclared hcross hinside
      x (S.sourceKind e) hxtype (f 0) (Finset.mem_of_mem_erase hxocc)
    obtain ⟨v, hv, hvType⟩ := P.occurrence_typeClass S A target hdeclared hcross hinside
      y (S.targetKind e) hytype (f 1) (Finset.mem_of_mem_erase hyocc)
    have h01 : f 0 ≠ f 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (hfinj he)
    have htarget := hcross z x y heSource k (f 0) (f 1)
      (Ne.symm (Finset.mem_erase.mp hxocc).1) (Ne.symm (Finset.mem_erase.mp hyocc).1) h01
    have hsplit : ({S.copyRoot (e, ℓ)}, {u, v}) ∈ target.edges := by
      apply (split_edge_mem_iff target _ _).mpr
      simpa only [one_root_disjSum, hk, hu, hv] using htarget
    refine ⟨u, v, (S.mem_relationCopy target e ℓ (u, v)).mpr ⟨huType, hvType, hsplit⟩, ?_, ?_⟩
    · exact hu
    · exact hv
  obtain ⟨c, hc, hconstant⟩ := binary_transversal_rigidity
    (matchingTuple (Roots := Roots) E) allowed rows hcard hunique htrans
  obtain ⟨u, v, huv, hcu, hcv⟩ := hc
  refine ⟨hxnone, hynone, u, v, huv, ⟨k, ?_⟩, ⟨k, ?_⟩⟩
  · intro i hi
    exact (hconstant 0 i hi).trans hcu
  · intro i hi
    exact (hconstant 1 i hi).trans hcv

omit [Fintype Kinds] in
theorem relation_copy_domain (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmatching : ∀ e, S.IsMatching target e) (e : Fin 3) (ℓ : Fin L) (x y : X)
    (hp : (x, y) ∈ S.relationCopy (P.model A) e ℓ) :
    x ∈ P.recoveredDomain ∧ y ∈ P.recoveredDomain := by
  obtain ⟨hx, hy, u, v, _, hu, hv⟩ :=
    P.relation_copy_stable S A target hdeclared hcross hinside hmatching e ℓ x y hp
  exact ⟨(P.mem_recoveredDomain x).mpr ⟨hx, u, hu⟩,
    (P.mem_recoveredDomain y).mpr ⟨hy, v, hv⟩⟩

omit [Fintype Kinds] in
theorem recoveredMap_relationCopy (P : RowRootingPlan row code block)
    (S : CompilerSignature Roots Code Kinds L) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmatching : ∀ e, S.IsMatching target e) (e : Fin 3) (ℓ : Fin L)
    (x y : P.recoveredDomain) (hp : (x.val, y.val) ∈ S.relationCopy (P.model A) e ℓ) :
    (P.recoveredMap x, P.recoveredMap y) ∈ S.relationCopy target e ℓ := by
  obtain ⟨_, _, u, v, huv, hu, hv⟩ :=
    P.relation_copy_stable S A target hdeclared hcross hinside hmatching e ℓ x.val y.val hp
  rw [P.recoveredMap_eq x u hu, P.recoveredMap_eq y v hv]
  exact huv

end TuranUniversality.Selector.RowRootingPlan
