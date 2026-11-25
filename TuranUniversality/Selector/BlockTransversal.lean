/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-! # Distinct block representatives for disjoint root lists -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

/-- Disjoint lists at least as large as any block admit representatives
in pairwise distinct blocks. This is the Hall argument in the block-code
lemma, separated from the construction of the perfect matchings. -/
theorem disjoint_lists_distinct_blocks {Rows Roots Blocks : Type*}
    [Fintype Rows] [Fintype Roots] [DecidableEq Roots] [DecidableEq Blocks]
    (block : Roots → Blocks) (bound : ℕ) (hbound : 0 < bound)
    (hblocks : ∀ b, (Finset.univ.filter fun r => block r = b).card ≤ bound)
    (L : Rows → Finset Roots) (hlarge : ∀ x, bound ≤ (L x).card)
    (hdisjoint : Pairwise fun x y => Disjoint (L x) (L y)) :
    ∃ choose : Rows → Roots, (∀ x, choose x ∈ L x) ∧
      Function.Injective (fun x => block (choose x)) := by
  classical
  let neighbors : Rows → Finset Blocks := fun x => (L x).image block
  have hHall (S : Finset Rows) : S.card ≤ (S.biUnion neighbors).card := by
    let U : Finset Roots := S.biUnion L
    let N : Finset Blocks := S.biUnion neighbors
    have hlow : S.card * bound ≤ U.card := by
      calc
        S.card * bound = ∑ _ ∈ S, bound := by simp
        _ ≤ ∑ x ∈ S, (L x).card := Finset.sum_le_sum (fun x _ => hlarge x)
        _ = U.card := (Finset.card_biUnion (fun x _ y _ hxy => hdisjoint hxy)).symm
    have hcover : U ⊆ N.biUnion (fun b => Finset.univ.filter fun r => block r = b) := by
      intro r hr
      obtain ⟨x, hx, hrx⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨block r,
        Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨r, hrx, rfl⟩⟩, by simp⟩
    have hupp : U.card ≤ N.card * bound :=
      (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul N _ bound (fun b _ => hblocks b))
    have hmul := hlow.trans hupp
    exact Nat.le_of_mul_le_mul_right hmul hbound
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hHall
  have hex (x : Rows) : ∃ r ∈ L x, block r = f x := Finset.mem_image.mp (hmem x)
  choose choose hchoose hblock using hex
  refine ⟨choose, hchoose, ?_⟩
  intro x y hxy
  exact hf (by simpa only [hblock] using hxy)

end TuranUniversality.Selector
