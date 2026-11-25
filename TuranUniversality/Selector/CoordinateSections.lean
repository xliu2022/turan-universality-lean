/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.LargeSection

/-! # Coordinate sections and their uniform densities -/

@[expose] public section

namespace TuranUniversality.Selector

variable {α : Type*}

def swapFirstTwo (α β : Type*) : α × (α × β) ≃ α × (α × β) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Insert a letter at a selected coordinate, as a bijection from a letter
and the remaining word. -/
def insertionEquiv (α : Type*) : (d : ℕ) → Fin (d + 1) →
    (α × Words α d) ≃ Words α (d + 1)
  | 0, _ => Equiv.refl _
  | d + 1, j => Fin.cases (Equiv.refl _)
      (fun k => (swapFirstTwo α (Words α d)).trans
        ((Equiv.refl α).prodCongr (insertionEquiv α d k))) j

def insertWord {d : ℕ} (j : Fin (d + 1)) (b : α) (w : Words α d) : Words α (d + 1) :=
  insertionEquiv α d j (b, w)

@[simp] theorem insertWord_zero (d : ℕ) (b : α) (w : Words α d) :
    insertWord (0 : Fin (d + 1)) b w = (b, w) := by
  cases d <;> rfl

@[simp] theorem insertWord_succ {d : ℕ} (j : Fin (d + 1))
    (b : α) (w : Words α (d + 1)) :
    insertWord j.succ b w = (w.1, insertWord j b w.2) := rfl

/-- Read the selected coordinate. -/
def wordCoordinate {d : ℕ} (j : Fin (d + 1)) (w : Words α (d + 1)) : α :=
  ((insertionEquiv α d j).symm w).1

@[simp] theorem wordCoordinate_insertWord {d : ℕ} (j : Fin (d + 1))
    (b : α) (w : Words α d) : wordCoordinate j (insertWord j b w) = b := by
  simp [wordCoordinate, insertWord]

theorem allDifferent_insertWord {d : ℕ} (j : Fin (d + 1))
    (b c : α) (x y : Words α d) :
    AllDifferent (insertWord j b x) (insertWord j c y) ↔ b ≠ c ∧ AllDifferent x y := by
  induction d with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
  | succ d ih =>
      refine Fin.cases ?_ ?_ j
      · simp only [insertWord_zero, AllDifferent]
      · intro k
        rw [insertWord_succ, insertWord_succ]
        change (x.1 ≠ y.1 ∧ AllDifferent (insertWord k b x.2) (insertWord k c y.2)) ↔
          b ≠ c ∧ (x.1 ≠ y.1 ∧ AllDifferent x.2 y.2)
        rw [ih]
        tauto

theorem sectionAverage_eq_insertWord [Fintype α] (d : ℕ)
    (f : Words α (d + 1) → ℝ) (j : Fin (d + 1)) (b : α) :
    sectionAverage (d + 1) f j b = mean (fun w => f (insertWord j b w)) := by
  induction d with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp
  | succ d ih =>
      refine Fin.cases ?_ ?_ j
      · simp
      · intro k
        rw [sectionAverage_succ, ih]
        simp only [insertWord_succ]
        rw [mean_prod, mean_comm]

theorem mean_insertion [Fintype α] {d : ℕ}
    (f : Words α (d + 1) → ℝ) (j : Fin (d + 1)) :
    mean f = mean (fun b => mean (fun w => f (insertWord j b w))) := by
  have h := Fintype.expect_equiv (insertionEquiv α d j)
    (fun p => f (insertionEquiv α d j p)) f (fun _ => rfl)
  change mean (fun p : α × Words α d => f (insertionEquiv α d j p)) = mean f at h
  rw [mean_prod] at h
  exact h.symm

/-- The family obtained by fixing one coordinate and deleting it. -/
noncomputable def wordSection [Fintype α] {d : ℕ}
    (F : Finset (Words α (d + 1))) (j : Fin (d + 1)) (b : α) : Finset (Words α d) := by
  classical
  exact Finset.univ.filter fun w => insertWord j b w ∈ F

/-- The part of a family outside the specified coordinate slice. -/
noncomputable def outsideSlice {d : ℕ}
    (F : Finset (Words α (d + 1))) (j : Fin (d + 1)) (b : α) :
    Finset (Words α (d + 1)) := by
  classical
  exact F.filter fun w => wordCoordinate j w ≠ b

@[simp] theorem mem_wordSection [Fintype α] {d : ℕ}
    (F : Finset (Words α (d + 1))) (j : Fin (d + 1)) (b : α) (w : Words α d) :
    w ∈ wordSection F j b ↔ insertWord j b w ∈ F := by
  classical
  simp [wordSection]

theorem density_wordSection [Fintype α] {d : ℕ}
    (F : Finset (Words α (d + 1))) (j : Fin (d + 1)) (b : α) :
    density (wordSection F j b) = mean (fun w => indicator F (insertWord j b w)) := by
  classical
  apply mean_congr
  intro w
  simp [indicator]

theorem density_wordSection_eq_average [Fintype α] {d : ℕ}
    (F : Finset (Words α (d + 1))) (j : Fin (d + 1)) (b : α) :
    density (wordSection F j b) = sectionAverage (d + 1) (indicator F) j b := by
  rw [density_wordSection, sectionAverage_eq_insertWord]

theorem sections_cross_intersecting [Fintype α] {d : ℕ}
    (F : Finset (Words α (d + 1))) (hF : CrossIntersecting F F)
    (j : Fin (d + 1)) {b c : α} (hbc : b ≠ c) :
    CrossIntersecting (wordSection F j b) (wordSection F j c) := by
  intro x hx y hy hxy
  exact hF (insertWord j b x) ((mem_wordSection F j b x).mp hx)
    (insertWord j c y) ((mem_wordSection F j c y).mp hy)
    ((allDifferent_insertWord j b c x y).mpr ⟨hbc, hxy⟩)

theorem density_outsideSlice [Fintype α] [DecidableEq α] {d : ℕ}
    (F : Finset (Words α (d + 1))) (j : Fin (d + 1)) (b : α) :
    density (outsideSlice F j b) =
      mean (fun c => if c = b then 0 else density (wordSection F j c)) := by
  classical
  unfold density
  rw [mean_insertion _ j]
  apply mean_congr
  intro c
  by_cases hcb : c = b
  · subst c
    simp [indicator, outsideSlice]
  · simp only [ite_eq_right hcb]
    rw [show mean (indicator (wordSection F j c)) =
      mean (fun w => indicator F (insertWord j c w)) from density_wordSection F j c]
    apply mean_congr
    intro w
    simp [indicator, outsideSlice, hcb]

end TuranUniversality.Selector
