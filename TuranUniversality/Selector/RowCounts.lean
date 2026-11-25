/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RowPrivacy
public import TuranUniversality.Selector.BlockTransversal

/-! # Root and code counts in a profile row -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

variable {I Roots Data Code : Type*}

noncomputable def rowRoots [Fintype Roots] (row : I → Roots ⊕ Data) : Finset Roots := by
  classical
  exact Finset.univ.filter fun r => ∃ i, row i = Sum.inl r

noncomputable def codeOccurrences [Fintype I]
    (row : I → Roots ⊕ Data) (code : Data → Code) (c : Code) : Finset I := by
  classical
  exact Finset.univ.filter fun i => ∃ d, row i = Sum.inr d ∧ code d = c

@[simp] theorem mem_rowRoots [Fintype Roots] (row : I → Roots ⊕ Data) (r : Roots) :
    r ∈ rowRoots row ↔ ∃ i, row i = Sum.inl r := by
  classical
  simp [rowRoots]

@[simp] theorem mem_codeOccurrences [Fintype I]
    (row : I → Roots ⊕ Data) (code : Data → Code) (c : Code) (i : I) :
    i ∈ codeOccurrences row code c ↔ ∃ d, row i = Sum.inr d ∧ code d = c := by
  classical
  simp [codeOccurrences]

/-- If root labels do not repeat and every data code occurs at most three
times, all remaining profile positions contribute distinct root labels. -/
theorem sparse_row_root_count [Fintype I] [Fintype Roots] [Fintype Code]
    (row : I → Roots ⊕ Data) (code : Data → Code)
    (hroot : ∀ r i j, row i = Sum.inl r → row j = Sum.inl r → i = j)
    (hcode : ∀ c, (codeOccurrences row code c).card ≤ 3) :
    Fintype.card I ≤ (rowRoots row).card + 3 * Fintype.card Code := by
  classical
  let tag : I → Roots ⊕ Code := fun i => (row i).map id code
  have hleft (i : I) (r : Roots) : tag i = Sum.inl r ↔ row i = Sum.inl r := by
    cases hi : row i <;> simp [tag, hi]
  have hright (c : Code) : (Finset.univ.filter fun i => tag i = Sum.inr c) =
      codeOccurrences row code c := by
    ext i
    cases hi : row i <;> simp [tag, hi]
  have htotal : Fintype.card I =
      (∑ r : Roots, (Finset.univ.filter fun i => tag i = Sum.inl r).card) +
        ∑ c : Code, (codeOccurrences row code c).card := by
    have h := sum_fiber_card tag (Finset.univ : Finset I)
    rw [Fintype.sum_sum_type] at h
    simpa only [hright, Finset.card_univ] using h.symm
  have hrootpoint (r : Roots) : (Finset.univ.filter fun i => tag i = Sum.inl r).card ≤
      if r ∈ rowRoots row then 1 else 0 := by
    by_cases hr : r ∈ rowRoots row
    · rw [ite_eq_left hr]
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact hroot r i j ((hleft i r).mp (Finset.mem_filter.mp hi).2)
        ((hleft j r).mp (Finset.mem_filter.mp hj).2)
    · rw [ite_eq_right hr]
      apply Nat.le_zero.mpr
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hr ((mem_rowRoots row r).mpr ⟨i, (hleft i r).mp (Finset.mem_filter.mp hi).2⟩)
  rw [htotal]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ r : Roots, if r ∈ rowRoots row then 1 else 0 :=
        Finset.sum_le_sum (fun r _ => hrootpoint r)
      _ = (rowRoots row).card := by
        simp [rowRoots]
        congr 1
        ext r
        simp
  · calc
      _ ≤ ∑ _ : Code, 3 := Finset.sum_le_sum (fun c _ => hcode c)
      _ = 3 * Fintype.card Code := by simp [Nat.mul_comm]

def RepeatedRoot (row : I → Roots ⊕ Data) : Prop :=
  ∃ r i j, i ≠ j ∧ row i = Sum.inl r ∧ row j = Sum.inl r

def FrequentCode [Fintype I] (row : I → Roots ⊕ Data) (code : Data → Code) : Prop :=
  ∃ c, 4 ≤ (codeOccurrences row code c).card

theorem sparse_row_many_roots [Fintype I] [Fintype Roots] [Fintype Code]
    (row : I → Roots ⊕ Data) (code : Data → Code)
    (bound : ℕ) (hI : 3 * Fintype.card Code + bound ≤ Fintype.card I)
    (hroot : ¬ RepeatedRoot row) (hcode : ¬ FrequentCode row code) :
    bound ≤ (rowRoots row).card := by
  have hcount := sparse_row_root_count row code (by
    intro r i j hi hj
    by_contra hij
    exact hroot ⟨r, i, j, hij, hi, hj⟩) (by
    intro c
    by_contra hc
    exact hcode ⟨c, by omega⟩)
  omega

end TuranUniversality.Selector
