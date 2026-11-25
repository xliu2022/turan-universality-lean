/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RowCounts

/-! # The three-step rooting reconstructed from profile rows -/

@[expose] public section

namespace TuranUniversality.Selector

variable {I X Roots Data Code Blocks : Type*}

def RepeatsValue (row : I → Roots ⊕ Data) (v : Roots ⊕ Data) : Prop :=
  ∃ i j, i ≠ j ∧ row i = v ∧ row j = v

/-- The finite output of the three-step row construction. The selected
data code occurs at least four times. For two chosen roots, either one
label is repeated or their blocks differ. -/
structure RowRootingPlan [Fintype I]
    (row : X → I → Roots ⊕ Data) (code : Data → Code) (block : Roots → Blocks) where
  assignment : X → Option Roots
  selectedCode : X → Code
  root_occurs : ∀ x r, assignment x = some r → ∃ i, row x i = Sum.inl r
  root_injective : ∀ x y r, assignment x = some r → assignment y = some r → x = y
  data_frequent : ∀ x, assignment x = none → 4 ≤ (codeOccurrences (row x) code (selectedCode x)).card
  root_pair : ∀ x y, x ≠ y → ∀ r s, assignment x = some r → assignment y = some s →
    RepeatsValue (row x) (Sum.inl r) ∨ RepeatsValue (row y) (Sum.inl s) ∨ block r ≠ block s

theorem exists_row_rooting [Fintype I] [Fintype X] [Fintype Roots]
    [Fintype Code] [Nonempty Code] [DecidableEq Roots] [DecidableEq Blocks]
    (row : X → I → Roots ⊕ Data) (code : Data → Code) (block : Roots → Blocks)
    (bound : ℕ) (hbound : 0 < bound)
    (hblocks : ∀ b, (Finset.univ.filter fun r => block r = b).card ≤ bound)
    (hI : 3 * Fintype.card Code + bound ≤ Fintype.card I)
    (hcross : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j)
    (hwithin : ∀ i r x y, row x i = Sum.inl r → row y i = Sum.inl r → x = y) :
    Nonempty (RowRootingPlan row code block) := by
  classical
  have hrep (x : {x : X // RepeatedRoot (row x)}) :
      ∃ r, RepeatsValue (row x.val) (Sum.inl r) := by
    obtain ⟨r, i, j, hij, hi, hj⟩ := x.property
    exact ⟨r, i, j, hij, hi, hj⟩
  choose repeatedRoot hrepeated using hrep
  have hfreq (x : {x : X // FrequentCode (row x) code}) :
      ∃ c, 4 ≤ (codeOccurrences (row x.val) code c).card := x.property
  choose frequent hfrequent using hfreq
  let Late := {x : X // ¬ RepeatedRoot (row x) ∧ ¬ FrequentCode (row x) code}
  have hlarge (x : Late) : bound ≤ (rowRoots (row x.val)).card :=
    sparse_row_many_roots (row x.val) code bound hI x.property.1 x.property.2
  have hdisjoint : Pairwise fun x y : Late => Disjoint (rowRoots (row x.val)) (rowRoots (row y.val)) := by
    intro x y hxy
    apply Finset.disjoint_left.mpr
    intro r hrx hry
    obtain ⟨i, hi⟩ := (mem_rowRoots (row x.val) r).mp hrx
    obtain ⟨j, hj⟩ := (mem_rowRoots (row y.val) r).mp hry
    exact root_occurrences_disjoint row Sum.inl hcross hwithin
      (fun heq => hxy (Subtype.ext heq)) hi hj
  obtain ⟨lateRoot, hlateRoot, hlateBlocks⟩ :=
    disjoint_lists_distinct_blocks block bound hbound hblocks (fun x : Late => rowRoots (row x.val)) hlarge hdisjoint
  let assignment : X → Option Roots := fun x =>
    if hr : RepeatedRoot (row x) then some (repeatedRoot ⟨x, hr⟩)
    else if hd : FrequentCode (row x) code then none
    else some (lateRoot ⟨x, hr, hd⟩)
  let selectedCode : X → Code := fun x =>
    if hd : FrequentCode (row x) code then frequent ⟨x, hd⟩ else Classical.choice inferInstance
  have hroot_occurs (x : X) (r : Roots) (ha : assignment x = some r) :
      ∃ i, row x i = Sum.inl r := by
    by_cases hr : RepeatedRoot (row x)
    · have heq : repeatedRoot ⟨x, hr⟩ = r := by simpa [assignment, hr] using ha
      obtain ⟨i, _, _, hi, _⟩ := hrepeated ⟨x, hr⟩
      exact ⟨i, heq ▸ hi⟩
    · by_cases hd : FrequentCode (row x) code
      · simp [assignment, hr, hd] at ha
      · have heq : lateRoot ⟨x, hr, hd⟩ = r := by simpa [assignment, hr, hd] using ha
        have hm := hlateRoot ⟨x, hr, hd⟩
        rw [heq] at hm
        exact (mem_rowRoots (row x) r).mp hm
  refine ⟨⟨assignment, selectedCode, hroot_occurs, ?_, ?_, ?_⟩⟩
  · intro x y r hx hy
    by_contra hxy
    obtain ⟨i, hi⟩ := hroot_occurs x r hx
    obtain ⟨j, hj⟩ := hroot_occurs y r hy
    exact root_occurrences_disjoint row Sum.inl hcross hwithin hxy hi hj
  · intro x hx
    by_cases hr : RepeatedRoot (row x)
    · simp [assignment, hr] at hx
    · by_cases hd : FrequentCode (row x) code
      · simpa [selectedCode, hd] using hfrequent ⟨x, hd⟩
      · simp [assignment, hr, hd] at hx
  · intro x y hxy r s hx hy
    by_cases hrx : RepeatedRoot (row x)
    · have heq : repeatedRoot ⟨x, hrx⟩ = r := by simpa [assignment, hrx] using hx
      exact Or.inl (heq ▸ hrepeated ⟨x, hrx⟩)
    · by_cases hry : RepeatedRoot (row y)
      · have heq : repeatedRoot ⟨y, hry⟩ = s := by simpa [assignment, hry] using hy
        exact Or.inr (Or.inl (heq ▸ hrepeated ⟨y, hry⟩))
      · have hdx : ¬ FrequentCode (row x) code := by
          intro hd
          simp [assignment, hrx, hd] at hx
        have hdy : ¬ FrequentCode (row y) code := by
          intro hd
          simp [assignment, hry, hd] at hy
        have hex : lateRoot ⟨x, hrx, hdx⟩ = r := by simpa [assignment, hrx, hdx] using hx
        have hey : lateRoot ⟨y, hry, hdy⟩ = s := by simpa [assignment, hry, hdy] using hy
        refine Or.inr (Or.inr ?_)
        intro heq
        have he : (⟨x, hrx, hdx⟩ : Late) = ⟨y, hry, hdy⟩ :=
          hlateBlocks (by simpa only [hex, hey] using heq)
        exact hxy (congrArg Subtype.val he)

end TuranUniversality.Selector
