module

public import TuranUniversality.Effective.UniformPrimrec

@[expose] public section

/-! # Joint primitive recursion for the approximation denominators

The uniformity is a varying input, so fixed-exponent or fixed-binomial
computability statements would not suffice here.
-/

namespace TuranUniversality.Effective.FiniteApproximation

theorem factorial_primrec : Primrec Nat.factorial := by
  have h : Primrec₂ (fun n k : ℕ => (n + 1) * k) :=
    Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  exact (Primrec.nat_rec₁ 1 h).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Nat.factorial_succ, ih])

theorem descFactorial_primrec : Primrec₂ Nat.descFactorial := by
  have h : Primrec₂ (fun n (p : ℕ × ℕ) => (n - p.1) * p.2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.nat_rec (Primrec.const 1) h).of_eq (fun n k => by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Nat.descFactorial_succ, ih])

theorem choose_primrec : Primrec₂ Nat.choose :=
  (Primrec.nat_div.comp descFactorial_primrec
    (factorial_primrec.comp Primrec.snd)).of_eq
      (fun p => (Nat.choose_eq_descFactorial_div_factorial p.1 p.2).symm)

theorem power_primrec : Primrec₂ (fun n k : ℕ => n ^ k) := by
  have h : Primrec₂ (fun n (p : ℕ × ℕ) => p.2 * n) :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  exact (Primrec.nat_rec (Primrec.const 1) h).of_eq (fun n k => by
    induction k with
    | zero => rfl
    | succ k ih => simp only [pow_succ, ih])

end TuranUniversality.Effective.FiniteApproximation
