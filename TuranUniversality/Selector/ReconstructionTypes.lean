/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ReconstructionCandidates
public import TuranUniversality.Weighted.Incidence

/-! # Recovering the one-root and marker type rules -/

@[expose] public section

namespace TuranUniversality.Selector.RowRootingPlan

open Weighted

variable {I X Roots Data Code Blocks Kinds : Type*}
    [Fintype I] [DecidableEq X] [DecidableEq Roots] [DecidableEq Data]
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

theorem one_root_target_edge (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data) (hcross : CrossEdges A target row)
    (z x y : X) (he : {z, x, y} ∈ A.edges) (r : Roots)
    (hz : P.assignment z = some r) (hx : P.assignment x = none) (hy : P.assignment y = none) :
    ∃ u v, code u = P.selectedCode x ∧ code v = P.selectedCode y ∧ ({r}, {u, v}) ∈ target.edges := by
  classical
  obtain ⟨i, hi⟩ := P.root_occurs z r hz
  obtain ⟨j, hj, hji, _⟩ := exists_mem_avoiding_two
    (codeOccurrences (row x) code (P.selectedCode x)) (by have := P.data_frequent x hx; omega) i i
  obtain ⟨k, hk, hki, hkj⟩ := exists_mem_avoiding_two
    (codeOccurrences (row y) code (P.selectedCode y)) (by have := P.data_frequent y hy; omega) i j
  obtain ⟨u, hu, hcu⟩ := (mem_codeOccurrences (row x) code (P.selectedCode x) j).mp hj
  obtain ⟨v, hv, hcv⟩ := (mem_codeOccurrences (row y) code (P.selectedCode y) k).mp hk
  refine ⟨u, v, hcu, hcv, ?_⟩
  apply (split_edge_mem_iff target {r} {u, v}).mpr
  rw [one_root_disjSum]
  simpa only [hi, hu, hv] using hcross z x y he i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj)

theorem data_target_edge (P : RowRootingPlan row code block)
    (A : RGraph X 3) (target : RootedModel Roots Data) (hcross : CrossEdges A target row)
    (x y z : X) (he : {x, y, z} ∈ A.edges)
    (hx : P.assignment x = none) (hy : P.assignment y = none) (hz : P.assignment z = none) :
    ∃ u v w, code u = P.selectedCode x ∧ code v = P.selectedCode y ∧
      code w = P.selectedCode z ∧ (∅, {u, v, w}) ∈ target.edges := by
  classical
  have hpos : (codeOccurrences (row x) code (P.selectedCode x)).Nonempty :=
    Finset.card_pos.mp (by have := P.data_frequent x hx; omega)
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj, hji, _⟩ := exists_mem_avoiding_two
    (codeOccurrences (row y) code (P.selectedCode y)) (by have := P.data_frequent y hy; omega) i i
  obtain ⟨k, hk, hki, hkj⟩ := exists_mem_avoiding_two
    (codeOccurrences (row z) code (P.selectedCode z)) (by have := P.data_frequent z hz; omega) i j
  obtain ⟨u, hu, hcu⟩ := (mem_codeOccurrences (row x) code (P.selectedCode x) i).mp hi
  obtain ⟨v, hv, hcv⟩ := (mem_codeOccurrences (row y) code (P.selectedCode y) j).mp hj
  obtain ⟨w, hw, hcw⟩ := (mem_codeOccurrences (row z) code (P.selectedCode z) k).mp hk
  refine ⟨u, v, w, hcu, hcv, hcw, ?_⟩
  apply (split_edge_mem_iff target ∅ {u, v, w}).mpr
  rw [zero_root_disjSum]
  simpa only [hu, hv, hw] using hcross x y z he i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj)

theorem oneRootRules [Fintype X] [Fintype Data] [Fintype Roots]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds] {L : ℕ}
    (P : RowRootingPlan row code block) (S : CompilerSignature Roots Code Kinds L)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hH2 : S.OneRootRules target) : S.OneRootRules (P.model A) := by
  intro r p hp x hx y hy hxy c d hc hd hphysical
  have hpair : ({x, y} : Finset X) = p := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [(P.model A).dataLink_uniform r p hp]
      simp [hxy]
  rw [← hpair] at hp
  have he := ((P.model A).mem_dataLink r {x, y}).mp hp
  obtain ⟨z, hz, hxnone, hynone, heSource⟩ :=
    one_root_edge_witness A P.assignment P.root_injective r x y he
  obtain ⟨u, v, hcu, hcv, heTarget⟩ :=
    P.one_root_target_edge A target hcross z x y heSource r hz hxnone hynone
  have hu : S.codes.Declared target u c := by
    have heq := hcu.trans (P.declared_selectedCode S.codes A target hdeclared hcross hinside x c hc)
    exact heq ▸ hdeclared u
  have hv : S.codes.Declared target v d := by
    have heq := hcv.trans (P.declared_selectedCode S.codes A target hdeclared hcross hinside y d hd)
    exact heq ▸ hdeclared v
  have huv : u ≠ v := by
    have hcard := target.uniform ({r}, {u, v}) heTarget
    have htwo : ({u, v} : Finset Data).card = 2 := by simp only [Finset.card_singleton] at hcard; omega
    exact Finset.card_pair_eq_two_iff.mp htwo
  exact hH2 r {u, v} ((target.mem_dataLink r {u, v}).mpr heTarget)
    u (by simp) v (by simp) huv c d hu hv hphysical

theorem markerTypes [Fintype X] [Fintype Data] [Fintype Roots]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds] {L : ℕ}
    (P : RowRootingPlan row code block) (S : CompilerSignature Roots Code Kinds L)
    (A : RGraph X 3) (target : RootedModel Roots Data)
    (hdeclared : ∀ d, S.codes.Declared target d (code d)) (hcross : CrossEdges A target row)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hmarker : S.MarkerTypes target) : S.MarkerTypes (P.model A) := by
  intro p hp x hx c hc
  obtain ⟨a, b, z, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((P.model A).dataTriples_uniform p hp)
  have he := ((P.model A).mem_dataTriples {a, b, z}).mp hp
  obtain ⟨ha, hb, hz, heSource⟩ := data_edge_witness A P.assignment P.root_injective a b z he
  obtain ⟨u, v, w, hcu, hcv, hcw, heTarget⟩ := P.data_target_edge A target hcross a b z heSource ha hb hz
  have hpTarget := (target.mem_dataTriples {u, v, w}).mpr heTarget
  have htu := hmarker {u, v, w} hpTarget u (by simp) (code u) (hdeclared u)
  have htv := hmarker {u, v, w} hpTarget v (by simp) (code v) (hdeclared v)
  have htw := hmarker {u, v, w} hpTarget w (by simp) (code w) (hdeclared w)
  have hxcode := P.declared_selectedCode S.codes A target hdeclared hcross hinside x c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · simpa only [hcu, hxcode] using htu
  · simpa only [hcv, hxcode] using htv
  · simpa only [hcw, hxcode] using htw

end TuranUniversality.Selector.RowRootingPlan
