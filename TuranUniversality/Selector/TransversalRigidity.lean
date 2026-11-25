/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Function.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Transversal rigidity for relations with unique completion

This file proves the finite transversal-rigidity lemma used in the singleton
reduction in `turan_universality_V4.tex` (label `lem:transversal-rigidity`).

The sets of allowed indices need not be disjoint. The hypothesis concerns
only choices of pairwise distinct indices. Unique completion then forces
each coordinate function to be constant on its allowed set.
-/

@[expose] public section

namespace TuranUniversality.Selector

open Function

variable {I J : Type*}

/-- Updating an injective choice preserves injectivity if its new value
avoids all previous choices. -/
theorem update_injOn_finset [DecidableEq I] [DecidableEq J]
    (s : Finset J) (j : J) (f : J → I)
    (hf : Set.InjOn f (s : Set J)) (x : I) (hx : x ∉ s.image f) :
    Set.InjOn (Function.update f j x) (insert j s : Finset J) := by
  intro u hu v hv huv
  by_cases huj : u = j
  · subst u
    by_cases hvj : v = j
    · exact hvj.symm
    · have hvs : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hvj
      have heq : x = f v := by simpa [Function.update_apply, hvj] using huv
      exact False.elim (hx (Finset.mem_image.mpr ⟨v, hvs, heq.symm⟩))
  · by_cases hvj : v = j
    · subst v
      have hus : u ∈ s := (Finset.mem_insert.mp hu).resolve_left huj
      have heq : f u = x := by simpa [Function.update_apply, huj] using huv
      exact False.elim (hx (Finset.mem_image.mpr ⟨u, hus, heq⟩))
    · have hus : u ∈ s := (Finset.mem_insert.mp hu).resolve_left huj
      have hvs : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hvj
      apply hf hus hvs
      simpa [Function.update_apply, huj, hvj] using huv

/-- Greedy distinct representatives: if every allowed set has at least as
many elements as there are coordinates, distinct choices exist. -/
theorem exists_injOn_selection [DecidableEq I] [DecidableEq J] [Nonempty I]
    (s : Finset J) (S : J → Finset I) :
    (∀ j ∈ s, s.card ≤ (S j).card) →
      ∃ f : J → I, (∀ j ∈ s, f j ∈ S j) ∧ Set.InjOn f (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨fun _ => Classical.arbitrary I, ?_, ?_⟩
      · simp
      · intro i hi
        simp at hi
  | @insert j s hj ih =>
      intro hcard
      have hsmall : ∀ k ∈ s, s.card ≤ (S k).card := by
        intro k hk
        exact (Finset.card_le_card (Finset.subset_insert j s)).trans
          (hcard k (Finset.mem_insert_of_mem hk))
      obtain ⟨f, hf, hfinj⟩ := ih hsmall
      have hlt : (s.image f).card < (S j).card := by
        calc
          (s.image f).card ≤ s.card := Finset.card_image_le
          _ < (insert j s).card := by simp [Finset.card_insert_of_notMem hj]
          _ ≤ (S j).card := hcard j (Finset.mem_insert_self j s)
      obtain ⟨x, hx, havoid⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨Function.update f j x, ?_, update_injOn_finset s j f hfinj x havoid⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simpa using hx
      · have hkj : k ≠ j := by
          intro heq
          exact hj (heq ▸ hk)
        simpa [Function.update_apply, hkj] using hf k hk

/-- In a relation with unique completion, fixing all but one coordinate
determines the remaining coordinate. -/
def UniqueCompletion {X : J → Type*} (R : ((j : J) → X j) → Prop) : Prop :=
  ∀ (j : J) (u v : (j : J) → X j),
    R u → R v → (∀ k, k ≠ j → u k = v k) → u j = v j

/-- The coordinatewise constancy conclusion of transversal rigidity.

The bound `card J + 1` leaves room to avoid the two indices being compared
and to choose distinct indices in all the other coordinates. -/
theorem transversal_constant [Fintype J] [DecidableEq J] [DecidableEq I]
    {X : J → Type*} (R : ((j : J) → X j) → Prop)
    (S : J → Finset I) (a : (j : J) → I → X j)
    (hcard : ∀ j, Fintype.card J + 1 ≤ (S j).card)
    (hunique : UniqueCompletion R)
    (htrans : ∀ f : J → I, (∀ j, f j ∈ S j) → Function.Injective f →
      R (fun j => a j (f j))) :
    ∀ j, ∀ i ∈ S j, ∀ i' ∈ S j, a j i = a j i' := by
  classical
  intro j i hi i' hi'
  let : Nonempty I := ⟨i⟩
  let t : Finset J := Finset.univ.erase j
  let A : J → Finset I := fun k => S k \ {i, i'}
  have ht : t.card + 1 = Fintype.card J := by
    simpa [t] using (Finset.card_erase_add_one (Finset.mem_univ j))
  have hA : ∀ k ∈ t, t.card ≤ (A k).card := by
    intro k _
    have hcover : (S k).card ≤ (A k).card + ({i, i'} : Finset I).card := by
      calc
        (S k).card ≤ ((S k \ {i, i'}) ∪ {i, i'}).card := by
          apply Finset.card_le_card
          intro x hx
          by_cases hxi : x ∈ ({i, i'} : Finset I)
          · exact Finset.mem_union_right _ hxi
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxi⟩)
        _ ≤ (A k).card + ({i, i'} : Finset I).card := Finset.card_union_le _ _
    have hpair : ({i, i'} : Finset I).card ≤ 2 := Finset.card_le_two
    have hk := hcard k
    omega
  obtain ⟨f, hf, hfinj⟩ := exists_injOn_selection t A hA
  have havoid : ∀ x ∈ ({i, i'} : Finset I), x ∉ t.image f := by
    intro x hx hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
    have hfk := (Finset.mem_sdiff.mp (hf k hk)).2
    exact hfk (heq.symm ▸ hx)
  have hfirst : i ∉ t.image f := havoid i (by simp)
  have hsecond : i' ∉ t.image f := havoid i' (by simp)
  have hupdate_mem (x : I) (hx : x ∈ S j) :
      ∀ k, Function.update f j x k ∈ S k := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa using hx
    · have hkt : k ∈ t := by simp [t, hkj]
      have hfk := (Finset.mem_sdiff.mp (hf k hkt)).1
      simpa [Function.update_apply, hkj] using hfk
  have hupdate_inj (x : I) (hx : x ∉ t.image f) :
      Function.Injective (Function.update f j x) := by
    have hinj := update_injOn_finset t j f hfinj x hx
    intro k l hkl
    apply hinj (by simp [t]) (by simp [t]) hkl
  have hRi := htrans (Function.update f j i) (hupdate_mem i hi)
    (hupdate_inj i hfirst)
  have hRi' := htrans (Function.update f j i') (hupdate_mem i' hi')
    (hupdate_inj i' hsecond)
  have heq := hunique j _ _ hRi hRi' (by
    intro k hkj
    simp [hkj])
  simpa using heq

/-- Transversal rigidity, including membership of the tuple of constants.

This is the general finite-coordinate version of the lemma from the paper.
The hypothesis `2 ≤ card J` matches its stated range. -/
theorem transversal_rigidity [Fintype J] [DecidableEq J] [DecidableEq I]
    {X : J → Type*} (R : ((j : J) → X j) → Prop)
    (S : J → Finset I) (a : (j : J) → I → X j)
    (hr : 2 ≤ Fintype.card J)
    (hcard : ∀ j, Fintype.card J + 1 ≤ (S j).card)
    (hunique : UniqueCompletion R)
    (htrans : ∀ f : J → I, (∀ j, f j ∈ S j) → Function.Injective f →
      R (fun j => a j (f j))) :
    ∃ c : (j : J) → X j, R c ∧ ∀ j, ∀ i ∈ S j, a j i = c j := by
  classical
  have hJ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  let j₀ : J := Classical.choice hJ
  have hS : (S j₀).Nonempty := Finset.card_pos.mp (by
    have := hcard j₀
    omega)
  obtain ⟨i₀, _⟩ := hS
  let : Nonempty I := ⟨i₀⟩
  have hlarge : ∀ j ∈ (Finset.univ : Finset J),
      (Finset.univ : Finset J).card ≤ (S j).card := by
    intro j _
    simpa using (Nat.le_succ (Fintype.card J)).trans (hcard j)
  obtain ⟨f, hf, hfinj⟩ := exists_injOn_selection Finset.univ S hlarge
  have hf_mem : ∀ j, f j ∈ S j := fun j => hf j (Finset.mem_univ j)
  have hf_inj : Function.Injective f := by
    intro j k hjk
    exact hfinj (Finset.mem_univ j) (Finset.mem_univ k) hjk
  refine ⟨fun j => a j (f j), htrans f hf_mem hf_inj, ?_⟩
  intro j i hi
  exact transversal_constant R S a hcard hunique htrans j i hi (f j) (hf_mem j)

/-- The binary case used for the target partial matchings. -/
theorem binary_transversal_rigidity [DecidableEq I]
    {X : Fin 2 → Type*} (R : ((j : Fin 2) → X j) → Prop)
    (S : Fin 2 → Finset I) (a : (j : Fin 2) → I → X j)
    (hcard : ∀ j, 3 ≤ (S j).card)
    (hunique : UniqueCompletion R)
    (htrans : ∀ f : Fin 2 → I, (∀ j, f j ∈ S j) → Function.Injective f →
      R (fun j => a j (f j))) :
    ∃ c : (j : Fin 2) → X j, R c ∧ ∀ j, ∀ i ∈ S j, a j i = c j := by
  apply transversal_rigidity R S a (by decide) _ hunique htrans
  simpa using hcard

/-- The ternary case used for the unique data-only edge. -/
theorem ternary_transversal_rigidity [DecidableEq I]
    {X : Fin 3 → Type*} (R : ((j : Fin 3) → X j) → Prop)
    (S : Fin 3 → Finset I) (a : (j : Fin 3) → I → X j)
    (hcard : ∀ j, 4 ≤ (S j).card)
    (hunique : UniqueCompletion R)
    (htrans : ∀ f : Fin 3 → I, (∀ j, f j ∈ S j) → Function.Injective f →
      R (fun j => a j (f j))) :
    ∃ c : (j : Fin 3) → X j, R c ∧ ∀ j, ∀ i ∈ S j, a j i = c j := by
  apply transversal_rigidity R S a (by decide) _ hunique htrans
  simpa using hcard

end TuranUniversality.Selector
