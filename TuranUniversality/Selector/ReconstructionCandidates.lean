/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootedWitnesses
public import TuranUniversality.Weighted.Codes

/-! # Reconstructing nonempty candidate sets from compatible rows -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted

variable {I X Roots Data Code Blocks : Type*}

def CrossEdges [DecidableEq X] [DecidableEq Roots] [DecidableEq Data]
    (A : RGraph X 3) (target : RootedModel Roots Data) (row : X → I → Roots ⊕ Data) : Prop :=
  ∀ x y z, {x, y, z} ∈ A.edges → ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    {row x i, row y j, row z k} ∈ target.toRGraph.edges

theorem exists_mem_avoiding_two [DecidableEq I] (S : Finset I) (hS : 3 ≤ S.card)
    (i j : I) : ∃ k ∈ S, k ≠ i ∧ k ≠ j := by
  have hlt : ({i, j} : Finset I).card < S.card := by
    have := Finset.card_le_two (a := i) (b := j)
    omega
  obtain ⟨k, hk, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨k, hk, by simpa using hnot⟩

namespace RowRootingPlan

variable [Fintype I] [DecidableEq X] [DecidableEq Roots] [DecidableEq Data]
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

def model (P : RowRootingPlan row code block) (A : RGraph X 3) : RootedModel Roots X :=
  rootedImage A P.assignment P.root_injective

omit [DecidableEq X] [DecidableEq Roots] [DecidableEq Data] in
theorem root_pair_occurrences (P : RowRootingPlan row code block)
    (y z : X) (r s : Roots) (hy : P.assignment y = some r) (hz : P.assignment z = some s)
    (hrep : RepeatsValue (row y) (Sum.inl r) ∨ RepeatsValue (row z) (Sum.inl s)) :
    ∃ i j, i ≠ j ∧ row y i = Sum.inl r ∧ row z j = Sum.inl s := by
  rcases hrep with ⟨a, b, hab, ha, hb⟩ | ⟨a, b, hab, ha, hb⟩
  · obtain ⟨j, hj⟩ := P.root_occurs z s hz
    obtain ⟨i, hij, hi⟩ := two_occurrences_avoid (row y) (Sum.inl r) hab ha hb j
    exact ⟨i, j, hij, hi, hj⟩
  · obtain ⟨i, hi⟩ := P.root_occurs y r hy
    obtain ⟨j, hji, hj⟩ := two_occurrences_avoid (row z) (Sum.inl s) hab ha hb i
    exact ⟨i, j, Ne.symm hji, hi, hj⟩

theorem two_root_target_edge (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data) (hcross : CrossEdges A target row)
    (y z x : X) (he : {y, z, x} ∈ A.edges) (r s : Roots)
    (hy : P.assignment y = some r) (hz : P.assignment z = some s) (hx : P.assignment x = none)
    (hrep : RepeatsValue (row y) (Sum.inl r) ∨ RepeatsValue (row z) (Sum.inl s)) :
    ∃ d, code d = P.selectedCode x ∧ ({r, s}, {d}) ∈ target.edges := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := P.root_pair_occurrences y z r s hy hz hrep
  obtain ⟨k, hk, hki, hkj⟩ := exists_mem_avoiding_two
    (codeOccurrences (row x) code (P.selectedCode x)) (by have := P.data_frequent x hx; omega) i j
  obtain ⟨d, hd, hc⟩ := (mem_codeOccurrences (row x) code (P.selectedCode x) k).mp hk
  refine ⟨d, hc, ?_⟩
  apply (split_edge_mem_iff target {r, s} {d}).mpr
  rw [two_root_disjSum]
  simpa only [hi, hj, hd] using hcross y z x he i j k hij (Ne.symm hki) (Ne.symm hkj)

theorem selected_code_candidate [Fintype Roots] [Fintype Code]
    (P : RowRootingPlan row code block) (C : CodeSystem Roots Code)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, C.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (C.missing c).pairs → block r = block s)
    (x : X) : P.selectedCode x ∈ C.candidates (P.model A) x := by
  classical
  apply (C.mem_candidates (P.model A) x (P.selectedCode x)).mpr
  apply Finset.disjoint_left.mpr
  intro p hp hpm
  obtain ⟨r, s, hrs, hpdef⟩ := Finset.card_eq_two.mp ((P.model A).rootLink_uniform x p hp)
  subst p
  have he := ((P.model A).mem_rootLink x {r, s}).mp hp
  obtain ⟨y, z, hy, hz, hx, heSource⟩ :=
    two_root_edge_witness A P.assignment P.root_injective r s x he
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact hrs (Option.some.inj (hy.symm.trans hz))
  have hrep : RepeatsValue (row y) (Sum.inl r) ∨ RepeatsValue (row z) (Sum.inl s) := by
    rcases P.root_pair y z hyz r s hy hz with hr | hs | hb
    · exact Or.inl hr
    · exact Or.inr hs
    · exact False.elim (hb (hinside (P.selectedCode x) r s hpm))
  obtain ⟨d, hc, hd⟩ := P.two_root_target_edge A target hcross y z x heSource r s hy hz hx hrep
  have hcand : P.selectedCode x ∈ C.candidates target d := by
    rw [hdeclared d, hc]
    simp
  have hdis := (C.mem_candidates target d (P.selectedCode x)).mp hcand
  exact Finset.disjoint_left.mp hdis ((target.mem_rootLink d {r, s}).mpr hd) hpm

theorem hasCandidates [Fintype Roots] [Fintype Code]
    (P : RowRootingPlan row code block) (C : CodeSystem Roots Code)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, C.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (C.missing c).pairs → block r = block s) :
    C.HasCandidates (P.model A) :=
  fun x => ⟨P.selectedCode x, P.selected_code_candidate C A target hdeclared hcross hinside x⟩

theorem declared_selectedCode [Fintype Roots] [Fintype Code]
    (P : RowRootingPlan row code block) (C : CodeSystem Roots Code)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, C.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (C.missing c).pairs → block r = block s)
    (x : X) (c : Code) (hc : C.Declared (P.model A) x c) : P.selectedCode x = c := by
  have hm := P.selected_code_candidate C A target hdeclared hcross hinside x
  rw [hc] at hm
  exact Finset.mem_singleton.mp hm

end RowRootingPlan

end TuranUniversality.Selector
