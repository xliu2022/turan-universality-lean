module

public import TuranUniversality.Computation.StaticInput
public import Mathlib.Data.List.ChainOfFn

/-! # Equivalence between finite-array neighbor checks and the row grammars -/

@[expose] public section

namespace TuranUniversality.Computation.ResetGrammar

theorem tail_chain (p : Tag) (s : List Tag) :
    Tail p s ↔ (p :: s).IsChain Adjacent ∧ Ends ((p :: s).getLast (by simp)) := by
  induction s generalizing p with
  | nil => simp [Tail]
  | cons q s ih => simp [Tail, ih, List.isChain_cons_cons, and_assoc]

theorem accepted_ofFn_iff {n : ℕ} (f : Fin (n + 1) → Tag) :
    Accepted (List.ofFn f) ↔ Starts (f 0) ∧
      (∀ i (hi : i + 1 < n + 1),
        Adjacent (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) ∧ Ends (f (Fin.last n)) := by
  have h := tail_chain (f 0) (List.ofFn fun i : Fin n => f i.succ)
  simp only [← List.ofFn_succ, List.isChain_ofFn, List.getLast_ofFn_succ] at h
  rw [List.ofFn_succ]
  change (Starts (f 0) ∧ Tail (f 0) (List.ofFn fun i : Fin n => f i.succ)) ↔ _
  rw [h]

end TuranUniversality.Computation.ResetGrammar

namespace TuranUniversality.Computation.StaticInput

variable {Γ : Type*}

theorem tail_chain (p : Symbol Γ) (s : List (Symbol Γ)) :
    Tail p s ↔ (p :: s).IsChain Adjacent ∧ Ends ((p :: s).getLast (by simp)) := by
  induction s generalizing p with
  | nil => simp [Tail]
  | cons q s ih => simp [Tail, ih, List.isChain_cons_cons, and_assoc]

theorem accepted_ofFn_iff {n : ℕ} (f : Fin (n + 1) → Symbol Γ) :
    Accepted (List.ofFn f) ↔ Starts (f 0) ∧
      (∀ i (hi : i + 1 < n + 1),
        Adjacent (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) ∧ Ends (f (Fin.last n)) := by
  have h := tail_chain (f 0) (List.ofFn fun i : Fin n => f i.succ)
  simp only [← List.ofFn_succ, List.isChain_ofFn, List.getLast_ofFn_succ] at h
  rw [List.ofFn_succ]
  change (Starts (f 0) ∧ Tail (f 0) (List.ofFn fun i : Fin n => f i.succ)) ↔ _
  rw [h]

end TuranUniversality.Computation.StaticInput
