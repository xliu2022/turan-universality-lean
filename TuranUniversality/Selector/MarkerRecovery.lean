/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.MatchingRecovery

/-! # Recovering the unique data-only edge and its vertices -/

@[expose] public section

namespace TuranUniversality.Selector.RowRootingPlan

open Weighted

variable {I X Roots Data Code Blocks : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [DecidableEq Roots] [DecidableEq Data]
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

omit [Fintype X] in
theorem data_edge_stable (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hcross : CrossEdges A target row) (hone : target.dataTriples.card ≤ 1)
    (x y z : X) (hp : (∅, {x, y, z}) ∈ (P.model A).edges) :
    P.assignment x = none ∧ P.assignment y = none ∧ P.assignment z = none ∧
      ∃ u v w, (∅, {u, v, w}) ∈ target.edges ∧
        P.StableValue x u ∧ P.StableValue y v ∧ P.StableValue z w := by
  classical
  obtain ⟨hx, hy, hz, heSource⟩ := data_edge_witness A P.assignment P.root_injective x y z hp
  let allowed : Fin 3 → Finset I :=
    ![codeOccurrences (row x) code (P.selectedCode x),
      codeOccurrences (row y) code (P.selectedCode y),
      codeOccurrences (row z) code (P.selectedCode z)]
  let rows : Fin 3 → I → Roots ⊕ Data := ![row x, row y, row z]
  have hcard (j : Fin 3) : 4 ≤ (allowed j).card := by
    fin_cases j
    · exact P.data_frequent x hx
    · exact P.data_frequent y hy
    · exact P.data_frequent z hz
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have htrans (f : Fin 3 → I) (hf : ∀ j, f j ∈ allowed j) (hfinj : Function.Injective f) :
      Finset.univ.image (fun j => rows j (f j)) ∈ pureDataEdges target := by
    obtain ⟨u, hu, _⟩ := (mem_codeOccurrences (row x) code (P.selectedCode x) (f 0)).mp (hf 0)
    obtain ⟨v, hv, _⟩ := (mem_codeOccurrences (row y) code (P.selectedCode y) (f 1)).mp (hf 1)
    obtain ⟨w, hw, _⟩ := (mem_codeOccurrences (row z) code (P.selectedCode z) (f 2)).mp (hf 2)
    have h01 : f 0 ≠ f 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (hfinj he)
    have h02 : f 0 ≠ f 2 := fun he => (by decide : (0 : Fin 3) ≠ 2) (hfinj he)
    have h12 : f 1 ≠ f 2 := fun he => (by decide : (1 : Fin 3) ≠ 2) (hfinj he)
    have htarget := hcross x y z heSource (f 0) (f 1) (f 2) h01 h02 h12
    have hsplit : (∅, {u, v, w}) ∈ target.edges := by
      apply (split_edge_mem_iff target _ _).mpr
      simpa only [zero_root_disjSum, hu, hv, hw] using htarget
    simpa [huniv, rows, hu, hv, hw] using (pureDataEdges_triple target u v w).mpr hsplit
  obtain ⟨c, hc, hconstant⟩ := ternary_transversal_rigidity
    (fun a : Fin 3 → Roots ⊕ Data => Finset.univ.image a ∈ pureDataEdges target)
    allowed rows hcard (pureDataEdges_unique target hone) htrans
  obtain ⟨u, hcu⟩ := pureDataEdges_inr target hc (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  obtain ⟨v, hcv⟩ := pureDataEdges_inr target hc (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
  obtain ⟨w, hcw⟩ := pureDataEdges_inr target hc (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
  have heTarget : (∅, {u, v, w}) ∈ target.edges := by
    apply (pureDataEdges_triple target u v w).mp
    simpa only [huniv, Finset.image_insert, Finset.image_singleton, hcu, hcv, hcw] using hc
  obtain ⟨k, _⟩ := Finset.card_pos.mp (by have := hcard 0; omega : 0 < (allowed 0).card)
  refine ⟨hx, hy, hz, u, v, w, heTarget, ⟨k, ?_⟩, ⟨k, ?_⟩, ⟨k, ?_⟩⟩
  · intro i hi
    exact (hconstant 0 i (Finset.mem_of_mem_erase hi)).trans hcu
  · intro i hi
    exact (hconstant 1 i (Finset.mem_of_mem_erase hi)).trans hcv
  · intro i hi
    exact (hconstant 2 i (Finset.mem_of_mem_erase hi)).trans hcw

theorem dataTriple_domain (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hcross : CrossEdges A target row) (hone : target.dataTriples.card ≤ 1)
    (p : Finset X) (hp : p ∈ (P.model A).dataTriples) : p ⊆ P.recoveredDomain := by
  obtain ⟨x, y, z, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((P.model A).dataTriples_uniform p hp)
  have he := ((P.model A).mem_dataTriples {x, y, z}).mp hp
  obtain ⟨hx, hy, hz, u, v, w, _, hu, hv, hw⟩ := P.data_edge_stable A target hcross hone x y z he
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact (P.mem_recoveredDomain _).mpr ⟨hx, u, hu⟩
  · exact (P.mem_recoveredDomain _).mpr ⟨hy, v, hv⟩
  · exact (P.mem_recoveredDomain _).mpr ⟨hz, w, hw⟩

theorem recoveredMap_dataTriple (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hcross : CrossEdges A target row) (hone : target.dataTriples.card ≤ 1)
    (x y z : P.recoveredDomain) (hp : (∅, {x.val, y.val, z.val}) ∈ (P.model A).edges) :
    (∅, {P.recoveredMap x, P.recoveredMap y, P.recoveredMap z}) ∈ target.edges := by
  obtain ⟨_, _, _, u, v, w, he, hu, hv, hw⟩ :=
    P.data_edge_stable A target hcross hone x.val y.val z.val hp
  rw [P.recoveredMap_eq x u hu, P.recoveredMap_eq y v hv, P.recoveredMap_eq z w hw]
  exact he

noncomputable def recoveredEdge (P : RowRootingPlan row code block) (p : Finset X) : Finset Data := by
  classical
  exact (p.subtype (· ∈ P.recoveredDomain)).image P.recoveredMap

omit [DecidableEq Roots] in
theorem recoveredEdge_triple (P : RowRootingPlan row code block) (x y z : P.recoveredDomain) :
    P.recoveredEdge {x.val, y.val, z.val} = {P.recoveredMap x, P.recoveredMap y, P.recoveredMap z} := by
  classical
  have heq : ({x.val, y.val, z.val} : Finset X).subtype (· ∈ P.recoveredDomain) = {x, y, z} := by
    ext a
    simp only [Finset.mem_subtype, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
  simp [recoveredEdge, heq]

omit [DecidableEq Roots] in
theorem recoveredEdge_injective_on (P : RowRootingPlan row code block)
    (hinj : Function.Injective P.recoveredMap) (p q : Finset X)
    (hp : p ⊆ P.recoveredDomain) (hq : q ⊆ P.recoveredDomain)
    (heq : P.recoveredEdge p = P.recoveredEdge q) : p = q := by
  classical
  have he : p.subtype (· ∈ P.recoveredDomain) = q.subtype (· ∈ P.recoveredDomain) :=
    Finset.image_injective hinj heq
  have hm := congrArg (fun s => s.map (Function.Embedding.subtype (· ∈ P.recoveredDomain))) he
  simpa only [Finset.subtype_map_of_mem (fun x hx => hp hx),
    Finset.subtype_map_of_mem (fun x hx => hq hx)] using hm

theorem recoveredEdge_mem (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hcross : CrossEdges A target row) (hone : target.dataTriples.card ≤ 1)
    (p : Finset X) (hp : p ∈ (P.model A).dataTriples) : P.recoveredEdge p ∈ target.dataTriples := by
  have hdom := P.dataTriple_domain A target hcross hone p hp
  obtain ⟨x, y, z, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((P.model A).dataTriples_uniform p hp)
  let x' : P.recoveredDomain := ⟨x, hdom (by simp)⟩
  let y' : P.recoveredDomain := ⟨y, hdom (by simp)⟩
  let z' : P.recoveredDomain := ⟨z, hdom (by simp)⟩
  have he := P.recoveredMap_dataTriple A target hcross hone x' y' z'
    (((P.model A).mem_dataTriples {x, y, z}).mp hp)
  have heq : P.recoveredEdge {x, y, z} = {P.recoveredMap x', P.recoveredMap y', P.recoveredMap z'} :=
    P.recoveredEdge_triple x' y' z'
  rw [heq]
  exact (target.mem_dataTriples _).mpr he

theorem oneMarker (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hcross : CrossEdges A target row) (hone : target.dataTriples.card ≤ 1)
    (hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j) :
    (P.model A).dataTriples.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  apply P.recoveredEdge_injective_on (P.recoveredMap_injective hprivacy) p q
    (P.dataTriple_domain A target hcross hone p hp) (P.dataTriple_domain A target hcross hone q hq)
  exact Finset.card_le_one.mp hone _ (P.recoveredEdge_mem A target hcross hone p hp)
    _ (P.recoveredEdge_mem A target hcross hone q hq)

end TuranUniversality.Selector.RowRootingPlan
