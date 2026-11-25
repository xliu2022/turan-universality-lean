module

public import TuranUniversality.Computation.ResetProtocol
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # A positive return gives an actual finite cyclic history -/

@[expose] public section

namespace TuranUniversality.Computation

variable {X : Type*} {r : X → X → Prop}

theorem transGen_finite_history {a b : X} (h : Relation.TransGen r a b) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : ℕ → X,
      f 0 = a ∧ f n = b ∧ ∀ i, i < n → r (f i) (f (i + 1)) := by
  induction h with
  | @single b hab =>
    refine ⟨1, by omega, fun i => if i = 0 then a else b, by simp, by simp, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    simpa [hi0] using hab
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn, f, hf0, hfn, hf⟩ := ih
    refine ⟨n + 1, by omega, fun i => if i ≤ n then f i else c, ?_, ?_, ?_⟩
    · simpa using hf0
    · simp
    · intro i hi
      by_cases hin : i < n
      · simpa [Nat.le_of_lt hin, show i + 1 ≤ n by omega] using hf i hin
      · have heq : i = n := by omega
        simpa [heq, hfn] using hbc

/-- A return is represented by a positive-size index cycle, with every edge
including the seam satisfying the original transition relation. -/
theorem finite_cycle_of_return {a : X} (h : Relation.TransGen r a a) :
    ∃ (p : ℕ) (hp : 0 < p) (f : Fin p → X),
      f ⟨0, hp⟩ = a ∧ ∀ i, r (f i) (f (finRotate p i)) := by
  obtain ⟨p, hp, f, hf0, hfp, hf⟩ := transGen_finite_history h
  refine ⟨p, hp, fun i => f i.val, hf0, ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  intro i
  by_cases hi : i.val = m
  · have heq : i = Fin.last m := Fin.ext hi
    subst i
    simp only [finRotate_last, Fin.val_zero, Fin.val_last, hf0]
    simpa only [hfp] using hf m (by omega)
  · have him : i.val < m := by omega
    have hrot := finRotate_of_lt him
    have hi' : (⟨i.val, him.trans_le m.le_succ⟩ : Fin (m + 1)) = i := rfl
    rw [hi'] at hrot
    rw [hrot]
    exact hf i.val i.isLt

/-- Before reaching the end of a finite cycle, its iterates are ordinary
addition of indices. -/
theorem finRotate_iterate_of_lt {n : ℕ} (i : Fin (n + 1)) (j : ℕ)
    (h : i.val + j < n + 1) :
    (finRotate (n + 1))^[j] i = ⟨i.val + j, h⟩ := by
  induction j with
  | zero => apply Fin.ext; simp
  | succ j ih =>
    have hj : i.val + j < n + 1 := by omega
    rw [Function.iterate_succ_apply', ih hj]
    have hlt : i.val + j < n := by omega
    exact finRotate_of_lt hlt

end TuranUniversality.Computation
