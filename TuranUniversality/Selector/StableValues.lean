/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ReconstructionTypes

/-! # Gluing the constants obtained from local constraints -/

@[expose] public section

namespace TuranUniversality.Selector

variable {I X Roots Data Code Blocks : Type*}

theorem three_le_card_erase [DecidableEq I] (S : Finset I) (hS : 4 ≤ S.card) (i : I) :
    3 ≤ (S.erase i).card := by
  by_cases hi : i ∈ S
  · have := Finset.card_erase_add_one hi
    omega
  · simpa [Finset.erase_eq_of_notMem hi] using (show 3 ≤ S.card by omega)

namespace RowRootingPlan

variable [Fintype I] [DecidableEq I]
    {row : X → I → Roots ⊕ Data} {code : Data → Code} {block : Roots → Blocks}

/-- A recovered value is constant on the chosen code occurrences after
at most one index has been removed. -/
def StableValue (P : RowRootingPlan row code block) (x : X) (d : Data) : Prop :=
  ∃ k, ∀ i ∈ (codeOccurrences (row x) code (P.selectedCode x)).erase k, row x i = Sum.inr d

theorem stableValue_unique (P : RowRootingPlan row code block) (x : X)
    (hx : P.assignment x = none) (u v : Data)
    (hu : P.StableValue x u) (hv : P.StableValue x v) : u = v := by
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := hv
  apply Sum.inr.inj
  exact punctured_constants_agree _ (by have := P.data_frequent x hx; omega) (row x) i j
    (Sum.inr u) (Sum.inr v) hi hj

theorem stableValue_code (P : RowRootingPlan row code block) (x : X)
    (hx : P.assignment x = none) (d : Data) (hd : P.StableValue x d) :
    code d = P.selectedCode x := by
  obtain ⟨k, hk⟩ := hd
  have hsize := three_le_card_erase _ (P.data_frequent x hx) k
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega :
    0 < ((codeOccurrences (row x) code (P.selectedCode x)).erase k).card)
  obtain ⟨d', hrow, hcode⟩ := (mem_codeOccurrences (row x) code (P.selectedCode x) i).mp
    (Finset.mem_of_mem_erase hi)
  have hdd' : d = d' := Sum.inr.inj ((hk i hi).symm.trans hrow)
  exact hdd'.symm ▸ hcode

theorem stableValue_repeats (P : RowRootingPlan row code block) (x : X)
    (hx : P.assignment x = none) (d : Data) (hd : P.StableValue x d) :
    RepeatsValue (row x) (Sum.inr d) := by
  obtain ⟨k, hk⟩ := hd
  have hsize := three_le_card_erase _ (P.data_frequent x hx) k
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega :
    1 < ((codeOccurrences (row x) code (P.selectedCode x)).erase k).card)
  exact ⟨i, j, hij, hk i hi, hk j hj⟩

/-- The domain contains precisely unrooted rows with a recovered stable
data value. Isolated or unconstrained rows need not be mapped. -/
noncomputable def recoveredDomain [Fintype X] (P : RowRootingPlan row code block) : Finset X := by
  classical
  exact Finset.univ.filter fun x => P.assignment x = none ∧ ∃ d, P.StableValue x d

@[simp] theorem mem_recoveredDomain [Fintype X] (P : RowRootingPlan row code block) (x : X) :
    x ∈ P.recoveredDomain ↔ P.assignment x = none ∧ ∃ d, P.StableValue x d := by
  classical
  simp [recoveredDomain]

noncomputable def recoveredMap [Fintype X] (P : RowRootingPlan row code block)
    (x : P.recoveredDomain) : Data :=
  Classical.choose (((P.mem_recoveredDomain x.val).mp x.property).2)

theorem recoveredMap_stable [Fintype X] (P : RowRootingPlan row code block)
    (x : P.recoveredDomain) : P.StableValue x.val (P.recoveredMap x) :=
  Classical.choose_spec (((P.mem_recoveredDomain x.val).mp x.property).2)

theorem recoveredMap_code [Fintype X] (P : RowRootingPlan row code block)
    (x : P.recoveredDomain) : code (P.recoveredMap x) = P.selectedCode x.val :=
  P.stableValue_code x.val (((P.mem_recoveredDomain x.val).mp x.property).1)
    (P.recoveredMap x) (P.recoveredMap_stable x)

theorem recoveredMap_eq [Fintype X] (P : RowRootingPlan row code block)
    (x : P.recoveredDomain) (d : Data) (hd : P.StableValue x.val d) : P.recoveredMap x = d :=
  P.stableValue_unique x.val (((P.mem_recoveredDomain x.val).mp x.property).1)
    (P.recoveredMap x) d (P.recoveredMap_stable x) hd

theorem recoveredMap_injective [Fintype X] (P : RowRootingPlan row code block)
    (hcross : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j) :
    Function.Injective P.recoveredMap := by
  have hrep (x : P.recoveredDomain) := P.stableValue_repeats x.val
    (((P.mem_recoveredDomain x.val).mp x.property).1) (P.recoveredMap x) (P.recoveredMap_stable x)
  have hinj := repeated_row_values_injective (fun x : P.recoveredDomain => row x.val)
    (by
      intro x y hxy i j hij
      exact hcross x.val y.val (fun he => hxy (Subtype.ext he)) i j hij)
    (fun x => Sum.inr (P.recoveredMap x)) hrep
  intro x y hxy
  exact hinj (congrArg Sum.inr hxy)

end RowRootingPlan

end TuranUniversality.Selector
