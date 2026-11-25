/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.StableValues

/-! # Unique completion for actual matchings and the unique data edge -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted

variable {Roots Data : Type*}

def matchingTuple (E : Finset (Data × Data)) (a : Fin 2 → Roots ⊕ Data) : Prop :=
  ∃ x y, (x, y) ∈ E ∧ a 0 = Sum.inr x ∧ a 1 = Sum.inr y

theorem matchingTuple_unique (E : Finset (Data × Data))
    (hfst : Set.InjOn Prod.fst (E : Set (Data × Data)))
    (hsnd : Set.InjOn Prod.snd (E : Set (Data × Data))) :
    UniqueCompletion (matchingTuple (Roots := Roots) E) := by
  intro j a b ha hb hagree
  obtain ⟨x, y, hxy, ha0, ha1⟩ := ha
  obtain ⟨x', y', hx'y', hb0, hb1⟩ := hb
  fin_cases j
  · have hy : y = y' := Sum.inr.inj (ha1.symm.trans ((hagree 1 (by decide)).trans hb1))
    have hp := hsnd hxy hx'y' hy
    exact ha0.trans ((congrArg Sum.inr (congrArg Prod.fst hp)).trans hb0.symm)
  · have hx : x = x' := Sum.inr.inj (ha0.symm.trans ((hagree 0 (by decide)).trans hb0))
    have hp := hfst hxy hx'y' hx
    exact ha1.trans ((congrArg Sum.inr (congrArg Prod.snd hp)).trans hb1.symm)

/-- An edge relation has unique completion if it has at most one edge,
and every edge has exactly as many vertices as tuple coordinates. -/
theorem unique_edge_completion {J T : Type*} [Fintype J] [DecidableEq J] [DecidableEq T]
    (E : Finset (Finset T)) (hone : E.card ≤ 1)
    (huniform : ∀ e ∈ E, e.card = Fintype.card J) :
    UniqueCompletion (fun a : J → T => Finset.univ.image a ∈ E) := by
  intro j a b ha hb hagree
  have himage : Finset.univ.image a = Finset.univ.image b := Finset.card_le_one.mp hone _ ha _ hb
  have hinj : Set.InjOn a (Finset.univ : Finset J) := by
    apply Finset.card_image_iff.mp
    simpa using huniform _ ha
  have hmem : a j ∈ Finset.univ.image b := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
  by_cases hkj : k = j
  · subst k
    exact hk.symm
  · have heq : a j = a k := hk.symm.trans (hagree k hkj).symm
    exact False.elim (hkj (hinj (Finset.mem_univ j) (Finset.mem_univ k) heq).symm)

def pureDataEdges [DecidableEq Roots] [DecidableEq Data]
    (M : RootedModel Roots Data) : Finset (Finset (Roots ⊕ Data)) :=
  M.dataTriples.image fun e => e.image Sum.inr

theorem pureDataEdges_card_le [DecidableEq Roots] [DecidableEq Data]
    (M : RootedModel Roots Data) (hone : M.dataTriples.card ≤ 1) :
    (pureDataEdges M).card ≤ 1 := Finset.card_image_le.trans hone

theorem pureDataEdges_uniform [DecidableEq Roots] [DecidableEq Data]
    (M : RootedModel Roots Data) (e : Finset (Roots ⊕ Data)) (he : e ∈ pureDataEdges M) : e.card = 3 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  rw [Finset.card_image_of_injective _ Sum.inr_injective]
  exact M.dataTriples_uniform d hd

theorem pureDataEdges_inr [DecidableEq Roots] [DecidableEq Data]
    (M : RootedModel Roots Data) {e : Finset (Roots ⊕ Data)} (he : e ∈ pureDataEdges M)
    {v : Roots ⊕ Data} (hv : v ∈ e) : ∃ d, v = Sum.inr d := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
  exact ⟨x, hx.symm⟩

@[simp] theorem pureDataEdges_triple [DecidableEq Roots] [DecidableEq Data]
    (M : RootedModel Roots Data) (u v w : Data) :
    {Sum.inr u, Sum.inr v, Sum.inr w} ∈ pureDataEdges M ↔ (∅, {u, v, w}) ∈ M.edges := by
  constructor
  · intro he
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp he
    have heq' : d.image (Sum.inr : Data → Roots ⊕ Data) =
        ({u, v, w} : Finset Data).image Sum.inr := by simpa using heq
    have hd' : d = {u, v, w} := Finset.image_injective Sum.inr_injective heq'
    exact (M.mem_dataTriples _).mp (hd' ▸ hd)
  · intro he
    apply Finset.mem_image.mpr
    exact ⟨{u, v, w}, (M.mem_dataTriples _).mpr he, by simp⟩

theorem pureDataEdges_unique [DecidableEq Roots] [DecidableEq Data]
    (M : RootedModel Roots Data) (hone : M.dataTriples.card ≤ 1) :
    UniqueCompletion (fun a : Fin 3 → Roots ⊕ Data => Finset.univ.image a ∈ pureDataEdges M) :=
  unique_edge_completion (pureDataEdges M) (pureDataEdges_card_le M hone)
    (fun e he => by simpa using pureDataEdges_uniform M e he)

end TuranUniversality.Selector
