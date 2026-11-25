module

public import TuranUniversality.Computation.RowFrame
public import TuranUniversality.Computation.CyclicHistory

/-! # Constructing finite wall frames from legal static and dynamic rows -/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem

open Turing Cellular ResetProtocol

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def framedLabel {n : ℕ} (s : Fin n → StaticInput.Symbol Γ) (r : Segment n Γ Λ)
    (i : Fin (n + 2)) : Label Γ Λ :=
  if h0 : i.val = 0 then .leftWall
  else if hn : i.val = n + 1 then .rightWall
  else .cell (s ⟨i.val - 1, by omega⟩) (r ⟨i.val - 1, by omega⟩)

@[simp] theorem framedLabel_zero {n : ℕ} (s : Fin n → StaticInput.Symbol Γ)
    (r : Segment n Γ Λ) : framedLabel s r 0 = .leftWall := by
  simp [framedLabel]

@[simp] theorem framedLabel_last {n : ℕ} (s : Fin n → StaticInput.Symbol Γ)
    (r : Segment n Γ Λ) : framedLabel s r (Fin.last (n + 1)) = .rightWall := by
  simp [framedLabel]

@[simp] theorem framedLabel_center {n : ℕ} (s : Fin n → StaticInput.Symbol Γ)
    (r : Segment n Γ Λ) (i : Fin n) :
    framedLabel s r (centerIndex i) = .cell (s i) (r i) := by
  simp [framedLabel, centerIndex, ne_of_lt i.isLt]

/-- The two local word grammars give every horizontal check of the frame. -/
def frameOfRows {m : ℕ} (M : TM0.Machine Γ Λ)
    (s : Fin (m + 1) → StaticInput.Symbol Γ) (r : Segment (m + 1) Γ Λ)
    (hs : StaticInput.Accepted (List.ofFn s)) (hr : Admissible M r) : Frame M (m + 1) where
  label := framedLabel s r
  left_wall := framedLabel_zero s r
  right_wall := framedLabel_last s r
  interior := fun i => ⟨s i, r i, framedLabel_center s r i⟩
  horizontal := by
    have hs' := (StaticInput.accepted_ofFn_iff s).mp hs
    have hr' := (ResetGrammar.accepted_ofFn_iff (fun i => (r i).1)).mp hr.1
    intro i
    by_cases h0 : i.val = 0
    · have hi : i = 0 := Fin.ext h0
      subst i
      change Horizontal M (framedLabel s r 0) (framedLabel s r (centerIndex 0))
      rw [framedLabel_zero, framedLabel_center]
      exact ⟨trivial, hr.2 0, hs'.1, hr'.1⟩
    · by_cases hn : i.val = m + 1
      · have hi : i = Fin.last (m + 1) := Fin.ext hn
        subst i
        change Horizontal M (framedLabel s r (centerIndex (Fin.last m)))
          (framedLabel s r (Fin.last (m + 2)))
        rw [framedLabel_center, framedLabel_last]
        exact ⟨hr.2 _, trivial, hs'.2.2, hr'.2.2⟩
      · let j : Fin (m + 1) := ⟨i.val - 1, by omega⟩
        let k : Fin (m + 1) := ⟨i.val, by omega⟩
        have hj : i.castSucc = centerIndex j := by
          apply Fin.ext
          simp only [centerIndex, j, Fin.val_castSucc]
          omega
        have hk : i.succ = centerIndex k := rfl
        rw [hj, hk, framedLabel_center, framedLabel_center]
        have hadd : i.val - 1 + 1 = i.val := by omega
        have hlt : i.val - 1 + 1 < m + 1 := by omega
        have hsadj : StaticInput.Adjacent (s j) (s k) := by
          simpa only [j, k, hadd] using hs'.2.1 (i.val - 1) hlt
        have hradj : ResetGrammar.Adjacent (r j).1 (r k).1 := by
          simpa only [j, k, hadd] using hr'.2.1 (i.val - 1) hlt
        exact ⟨hr.2 j, hr.2 k, hsadj, hradj⟩

@[simp] theorem frameOfRows_static {m : ℕ} (M : TM0.Machine Γ Λ)
    (s : Fin (m + 1) → StaticInput.Symbol Γ) (r : Segment (m + 1) Γ Λ)
    (hs : StaticInput.Accepted (List.ofFn s)) (hr : Admissible M r) :
    (frameOfRows M s r hs hr).static = s := by
  funext i
  simp [Frame.static, frameOfRows, staticOf]

@[simp] theorem frameOfRows_dynamic {m : ℕ} (M : TM0.Machine Γ Λ)
    (s : Fin (m + 1) → StaticInput.Symbol Γ) (r : Segment (m + 1) Γ Λ)
    (hs : StaticInput.Accepted (List.ofFn s)) (hr : Admissible M r) :
    (frameOfRows M s r hs hr).dynamic = r := by
  funext i
  simp [Frame.dynamic, frameOfRows, dynamicPart]

theorem rotate_center {n : ℕ} (i : Fin n) :
    finRotate (n + 2) (centerIndex i) = rightIndex i := by
  exact finRotate_of_lt (show i.val + 1 < n + 1 by omega)

theorem rotate_symm_center {n : ℕ} (i : Fin n) :
    (finRotate (n + 2)).symm (centerIndex i) = leftIndex i := by
  apply (finRotate (n + 2)).injective
  rw [Equiv.apply_symm_apply]
  exact (finRotate_of_lt (show i.val < n + 1 by omega)).symm

theorem Frame.horizontal_cyclic {n : ℕ} {M : TM0.Machine Γ Λ} (F : Frame M n)
    (i : Fin (n + 2)) : Horizontal M (F.label i) (F.label (finRotate (n + 2) i)) := by
  by_cases hi : i.val = n + 1
  · have heq : i = Fin.last (n + 1) := Fin.ext hi
    subst i
    rw [finRotate_last, F.right_wall, F.left_wall]
    trivial
  · have hlt : i.val < n + 1 := by omega
    have hrot := finRotate_of_lt hlt
    have hi' : (⟨i.val, hlt.trans_le (n + 1).le_succ⟩ : Fin (n + 2)) = i := rfl
    rw [hi'] at hrot
    rw [hrot]
    exact F.horizontal ⟨i.val, hlt⟩

/-- An actual reset step gives the full cyclic radius-one evolution table;
the added walls keep their labels through the temporal seam as well. -/
theorem frameOfRows_evolution {m : ℕ} (M : TM0.Machine Γ Λ)
    (s : Fin (m + 1) → StaticInput.Symbol Γ) (r r' : Segment (m + 1) Γ Λ)
    (hs : StaticInput.Accepted (List.ofFn s))
    (h : Step M (fun i => StaticInput.frozen (s i)) r r') (i : Fin (m + 3)) :
    Evolution M (framedLabel s r ((finRotate (m + 3)).symm i))
      (framedLabel s r i) (framedLabel s r (finRotate (m + 3) i))
      (framedLabel s r' i) := by
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    simp only [hi, framedLabel_zero, Evolution]
  · by_cases hn : i.val = m + 2
    · have hi : i = Fin.last (m + 2) := Fin.ext hn
      simp only [hi, framedLabel_last, Evolution]
    · let j : Fin (m + 1) := ⟨i.val - 1, by omega⟩
      have hi : i = centerIndex j := by
        apply Fin.ext
        simp only [centerIndex, j]
        omega
      rw [hi, rotate_center, rotate_symm_center, framedLabel_center, framedLabel_center]
      let F := frameOfRows M s r hs h.1
      have hl := F.left_dynamic j
      have hr := F.right_dynamic j
      change dynamicPart (framedLabel s r (leftIndex j)) = _ at hl
      change dynamicPart (framedLabel s r (rightIndex j)) = _ at hr
      simp only [F, frameOfRows_dynamic] at hl hr
      exact ⟨r' j, rfl, by simpa only [hl, hr] using h.2.2 j⟩

end TuranUniversality.Computation.LocalSystem
