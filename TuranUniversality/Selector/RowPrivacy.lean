/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.CompatibleProfiles
public import TuranUniversality.Selector.TransversalRigidity

/-! # Separation of rows in compatible profiles -/

@[expose] public section

namespace TuranUniversality.Selector

open RGraph

theorem exists_third_index {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I) (a b : I) : ∃ c, c ≠ a ∧ c ≠ b := by
  have hlt : ({a, b} : Finset I).card < (Finset.univ : Finset I).card := by
    have := Finset.card_le_two (a := a) (b := b)
    simpa only [Finset.card_univ] using (lt_of_le_of_lt this (by omega))
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨c, by simpa using hc⟩

/-- Pair coverage and the cross-edge condition separate different core
rows at different profile indices. -/
theorem profile_cross_privacy {X T I : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq T] [Fintype I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I) (A : RGraph X 3) (target : RGraph T 3)
    (f : I → ExtensionVertex X → T)
    (hcross : ∀ x y z, {x, y, z} ∈ A.pairExtension.edges →
      ∀ a b c, a ≠ b → a ≠ c → b ≠ c → {f a x, f b y, f c z} ∈ target.edges)
    (x y : X) (hxy : x ≠ y) (a b : I) (hab : a ≠ b) :
    f a (Sum.inl x) ≠ f b (Sum.inl y) := by
  obtain ⟨c, hca, hcb⟩ := exists_third_index hcard a b
  let p : VertexPair X := ⟨{x, y}, by simp [hxy]⟩
  have hedge : {Sum.inl x, Sum.inl y, Sum.inr p} ∈ A.pairExtension.edges := by
    have heq : privateEdge p = {Sum.inl x, Sum.inl y, Sum.inr p} := by
      ext v
      simp [privateEdge, p, or_comm, or_assoc]
    exact heq ▸ privateEdge_mem A p
  have htarget := hcross (Sum.inl x) (Sum.inl y) (Sum.inr p) hedge a b c hab (Ne.symm hca) (Ne.symm hcb)
  exact (Finset.card_triple_eq_three_iff.mp (target.uniform _ htarget)).1

/-- A designated root cannot occur in two different rows, even at equal
profile indices. -/
theorem root_occurrences_disjoint {X Roots T I : Type*}
    (row : X → I → T) (root : Roots → T)
    (hcross : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j)
    (hwithin : ∀ i r x y, row x i = root r → row y i = root r → x = y)
    {x y : X} (hxy : x ≠ y) {i j : I} {r : Roots}
    (hx : row x i = root r) (hy : row y j = root r) : False := by
  by_cases hij : i = j
  · subst j
    exact hxy (hwithin i r x y hx hy)
  · exact hcross x y hxy i j hij (hx.trans hy.symm)

/-- Values occurring at least twice in their respective rows define an
injective map as soon as different rows have cross-index privacy. -/
theorem repeated_row_values_injective {X T I : Type*}
    (row : X → I → T)
    (hcross : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j)
    (g : X → T)
    (hrepeat : ∀ x, ∃ i j, i ≠ j ∧ row x i = g x ∧ row x j = g x) :
    Function.Injective g := by
  intro x y hxy
  by_contra hne
  obtain ⟨a, b, hab, ha, hb⟩ := hrepeat x
  obtain ⟨c, _, _, hc, _⟩ := hrepeat y
  obtain ⟨i, hic, hi⟩ := two_occurrences_avoid (row x) (g x) hab ha hb c
  exact hcross x y hne i c hic (hi.trans (hxy.trans hc.symm))

/-- Constants obtained after deleting at most one index agree on their
overlap. This glues the binary and ternary rigidity conclusions. -/
theorem punctured_constants_agree {I T : Type*} [DecidableEq I]
    (S : Finset I) (hS : 3 ≤ S.card) (row : I → T)
    (i j : I) (a b : T)
    (ha : ∀ k ∈ S.erase i, row k = a) (hb : ∀ k ∈ S.erase j, row k = b) : a = b := by
  have hlt : ({i, j} : Finset I).card < S.card := by
    have := Finset.card_le_two (a := i) (b := j)
    omega
  obtain ⟨k, hk, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hki : k ≠ i := by simpa using fun h => hnot (by simp [h])
  have hkj : k ≠ j := by simpa using fun h => hnot (by simp [h])
  exact (ha k (Finset.mem_erase.mpr ⟨hki, hk⟩)).symm.trans (hb k (Finset.mem_erase.mpr ⟨hkj, hk⟩))

end TuranUniversality.Selector
