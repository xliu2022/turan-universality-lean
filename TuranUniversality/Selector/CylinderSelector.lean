/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.DirectionSwitch

/-! # Simultaneous avoidance of intersecting bad-line cylinders -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

/-- The quantitative combinatorial selector. The number `h` of good rows
is independent of the number of coordinates. -/
theorem select_good_cylinder_rows {I V R B : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    (q : ℝ) (hq : 0 < q) (hroots : (Fintype.card R : ℝ) ≤ q)
    (hn : 1048576 ≤ Fintype.card V) (hnq : 19 * q / 20 < Fintype.card V)
    (h t : ℕ) (hh : 0 < h) (ht : 8 * h ≤ t)
    (block : V → B) (hblock : ∀ b, (blockFiber block b).card = t)
    (Z : I → R → Finset (I → V))
    (hself : ∀ j r, ∀ x ∈ Z j r, ∀ y ∈ Z j r, ∃ i, i ≠ j ∧ x i = y i)
    (hcross : ∀ j k, j ≠ k → ∀ r, ∀ x ∈ Z j r, ∀ y ∈ Z k r,
      ∃ i, i ≠ j ∧ i ≠ k ∧ x i = y i) :
    ∃ j : I, ∃ w : Fin h → I → V,
      (∀ a r, w a ∉ Z j r) ∧
        (∀ i, Function.Injective (fun a => w a i)) ∧
          ∀ i a b, block (w a i) = block (w b i) := by
  classical
  obtain ⟨j, Marked, hcap, hbudget, hresidual⟩ :=
    select_direction q hroots hn Z hself hcross
  let residual : R → Finset (I → V) := fun r =>
    (Z j r).filter fun w => ∀ i, w i ∉ Marked i
  let Bad : Finset (I → V) := Finset.univ.biUnion residual
  have hBad : density Bad ≤ q / (64 * Fintype.card V) := by
    calc
      density Bad ≤ ∑ r, density (residual r) := density_biUnion_le residual
      _ ≤ ∑ _ : R, 1 / (64 * (Fintype.card V : ℝ)) :=
        Finset.sum_le_sum (fun r _ => hresidual r)
      _ = (Fintype.card R : ℝ) / (64 * Fintype.card V) := by simp [div_eq_mul_inv]
      _ ≤ q / (64 * Fintype.card V) := div_le_div_of_nonneg_right hroots (by positivity)
  obtain ⟨w, hw, hmarks, hinj, hsame⟩ :=
    choose_good_guard_rows q hq hnq h t hh ht block hblock Marked hcap hbudget Bad hBad
  refine ⟨j, w, ?_, hinj, hsame⟩
  intro a r har
  apply hw a
  exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, Finset.mem_filter.mpr ⟨har, hmarks a⟩⟩

end TuranUniversality.Selector
