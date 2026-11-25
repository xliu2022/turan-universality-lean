module

public import TuranUniversality.Computation.LocalSystem
public import TuranUniversality.Computation.GrammarChecks

/-! # Finite wall frames and the actual reset segment checks -/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem

open Turing Cellular ResetProtocol

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def staticOf : Label Γ Λ → StaticInput.Symbol Γ
  | .cell s _ => s
  | _ => .before

def centerIndex {n : ℕ} (i : Fin n) : Fin (n + 2) := ⟨i.val + 1, by omega⟩
def leftIndex {n : ℕ} (i : Fin n) : Fin (n + 2) := ⟨i.val, by omega⟩
def rightIndex {n : ℕ} (i : Fin n) : Fin (n + 2) := ⟨i.val + 2, by omega⟩

/-- A finite wall segment with all its actual horizontal local checks. -/
structure Frame (M : TM0.Machine Γ Λ) (n : ℕ) where
  label : Fin (n + 2) → Label Γ Λ
  left_wall : label 0 = .leftWall
  right_wall : label (Fin.last (n + 1)) = .rightWall
  interior : ∀ i : Fin n, ∃ s d, label (centerIndex i) = .cell s d
  horizontal : ∀ i : Fin (n + 1), Horizontal M (label i.castSucc) (label i.succ)

namespace Frame

variable {M : TM0.Machine Γ Λ} {n : ℕ} (F : Frame M n)

def static : Fin n → StaticInput.Symbol Γ := fun i => staticOf (F.label (centerIndex i))
def dynamic : Segment n Γ Λ := fun i => dynamicPart (F.label (centerIndex i))

theorem cell_at (i : Fin n) :
    F.label (centerIndex i) = .cell (F.static i) (F.dynamic i) := by
  obtain ⟨s, d, h⟩ := F.interior i
  simp only [static, dynamic, h, staticOf, dynamicPart]

theorem width_pos (F : Frame M n) : 0 < n := by
  cases n with
  | zero =>
    have h := F.horizontal 0
    have h0 : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
    have h1 : (0 : Fin 1).succ = Fin.last 1 := rfl
    rw [h0, h1, F.left_wall, F.right_wall] at h
    exact h.2.2.elim
  | succ n => omega

theorem unary (i : Fin n) : ValidSymbol M (F.dynamic i) := by
  have h := F.horizontal ⟨i.val + 1, by omega⟩
  have hc : (⟨i.val + 1, by omega⟩ : Fin (n + 1)).castSucc = centerIndex i := rfl
  rw [hc, F.cell_at] at h
  exact h.1

theorem starts {m : ℕ} (F : Frame M (m + 1)) :
    StaticInput.Starts (F.static 0) ∧ ResetGrammar.Starts (F.dynamic 0).1 := by
  have h := F.horizontal 0
  have h0 : (0 : Fin (m + 2)).castSucc = (0 : Fin (m + 3)) := rfl
  have h1 : (0 : Fin (m + 2)).succ = centerIndex (0 : Fin (m + 1)) := rfl
  rw [h0, h1, F.left_wall, F.cell_at] at h
  exact h.2.2

theorem ends {m : ℕ} (F : Frame M (m + 1)) :
    StaticInput.Ends (F.static (Fin.last m)) ∧ ResetGrammar.Ends (F.dynamic (Fin.last m)).1 := by
  have h := F.horizontal (Fin.last (m + 1))
  have h0 : (Fin.last (m + 1)).castSucc = centerIndex (Fin.last m) := rfl
  have h1 : (Fin.last (m + 1)).succ = Fin.last (m + 2) := rfl
  rw [h0, h1, F.right_wall, F.cell_at] at h
  exact h.2.2

theorem adjacent (i : ℕ) (hi : i + 1 < n) :
    StaticInput.Adjacent (F.static ⟨i, by omega⟩) (F.static ⟨i + 1, hi⟩) ∧
      ResetGrammar.Adjacent (F.dynamic ⟨i, by omega⟩).1 (F.dynamic ⟨i + 1, hi⟩).1 := by
  have h := F.horizontal ⟨i + 1, by omega⟩
  have h0 : (⟨i + 1, by omega⟩ : Fin (n + 1)).castSucc = centerIndex ⟨i, by omega⟩ := rfl
  have h1 : (⟨i + 1, by omega⟩ : Fin (n + 1)).succ = centerIndex ⟨i + 1, hi⟩ := rfl
  rw [h0, h1, F.cell_at, F.cell_at] at h
  exact h.2.2

theorem static_accepted : StaticInput.Accepted (List.ofFn F.static) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.width_pos)
  exact (StaticInput.accepted_ofFn_iff F.static).mpr
    ⟨F.starts.1, fun i hi => (F.adjacent i hi).1, F.ends.1⟩

theorem dynamic_admissible : Admissible M F.dynamic := by
  refine ⟨?_, F.unary⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt F.width_pos)
  exact (ResetGrammar.accepted_ofFn_iff (fun i => (F.dynamic i).1)).mpr
    ⟨F.starts.2, fun i hi => (F.adjacent i hi).2, F.ends.2⟩

/-- The left old neighbor agrees with the segment's blank boundary convention. -/
theorem left_dynamic (i : Fin n) :
    dynamicPart (F.label (leftIndex i)) = extendSymbol F.dynamic ((i : ℤ) - 1) := by
  by_cases hi : i.val = 0
  · have hindex : leftIndex i = 0 := Fin.ext hi
    have hb : ¬InBounds n ((i : ℤ) - 1) := by simp only [InBounds]; omega
    rw [hindex, F.left_wall]
    simp [dynamicPart, extendSymbol, hb]
  · have hb : InBounds n ((i : ℤ) - 1) := by simp only [InBounds]; omega
    let j : Fin n := ⟨i.val - 1, by omega⟩
    have hindex : leftIndex i = centerIndex j := by apply Fin.ext; simp [leftIndex, centerIndex, j]; omega
    have hj : (⟨((i : ℤ) - 1).toNat, by obtain ⟨_, _⟩ := hb; omega⟩ : Fin n) = j := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex]
    simp only [extendSymbol, hb, dite_true, hj, dynamic]

theorem right_dynamic (i : Fin n) :
    dynamicPart (F.label (rightIndex i)) = extendSymbol F.dynamic ((i : ℤ) + 1) := by
  by_cases hi : i.val + 1 = n
  · have hindex : rightIndex i = Fin.last (n + 1) := by
      apply Fin.ext; simp [rightIndex]; omega
    have hb : ¬InBounds n ((i : ℤ) + 1) := by simp only [InBounds]; omega
    rw [hindex, F.right_wall]
    simp [dynamicPart, extendSymbol, hb]
  · have hb : InBounds n ((i : ℤ) + 1) := by simp only [InBounds]; omega
    let j : Fin n := ⟨i.val + 1, by omega⟩
    have hindex : rightIndex i = centerIndex j := rfl
    have hj : (⟨((i : ℤ) + 1).toNat, by obtain ⟨_, _⟩ := hb; omega⟩ : Fin n) = j := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex]
    simp only [extendSymbol, hb, dite_true, hj, dynamic]

/-- Radius-one evolution on the framed labels is exactly the already proved
finite reset transition on their dynamic segments. -/
theorem step (G : Frame M n)
    (h : ∀ i : Fin n, Evolution M (F.label (leftIndex i)) (F.label (centerIndex i))
      (F.label (rightIndex i)) (G.label (centerIndex i))) :
    Step M (fun i => StaticInput.frozen (F.static i)) F.dynamic G.dynamic := by
  refine ⟨F.dynamic_admissible, G.dynamic_admissible, ?_⟩
  intro i
  have hi := h i
  rw [F.cell_at, G.cell_at] at hi
  obtain ⟨d, heq, hd⟩ := hi
  have hdyn : G.dynamic i = d := (Label.cell.inj heq).2
  rw [F.left_dynamic, F.right_dynamic, ← hdyn] at hd
  exact hd

theorem static_eq_of_evolution (G : Frame M n)
    (h : ∀ i : Fin n, Evolution M (F.label (leftIndex i)) (F.label (centerIndex i))
      (F.label (rightIndex i)) (G.label (centerIndex i))) : G.static = F.static := by
  funext i
  have hi := h i
  rw [F.cell_at, G.cell_at] at hi
  obtain ⟨d, heq, _⟩ := hi
  exact (Label.cell.inj heq).1

end Frame

end TuranUniversality.Computation.LocalSystem
