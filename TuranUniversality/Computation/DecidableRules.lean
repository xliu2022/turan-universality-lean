module

public import TuranUniversality.Computation.MatchingSystem

/-! # Finite decision procedures for all local rules

These instances enumerate finite carriers and the explicitly bounded prefix
positions.  They do not use a classical decision procedure for propositions.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

variable {D Alphabet : Type*} [DecidableEq D] [Fintype D]

instance decidablePath (r : D → D → Prop) [DecidableRel r] (n : ℕ) (x y : D) :
    Decidable (Path r n x y) := by
  induction n generalizing x with
  | zero => exact inferInstanceAs (Decidable (x = y))
  | succ n ih =>
    letI (x : D) : Decidable (Path r n x y) := ih x
    exact inferInstanceAs (Decidable (∃ z, r x z ∧ Path r n z y))

namespace Realization

variable (A : Realization D Alphabet)

instance decidableH (x y : D) : Decidable (A.H x y) :=
  inferInstanceAs (Decidable (∃ b, (x, b) ∈ A.J.pairs ∧ (b, y) ∈ A.R.pairs))

instance decidableV (x y : D) : Decidable (A.V x y) :=
  inferInstanceAs (Decidable (∃ b, (x, b) ∈ A.J.pairs ∧ (b, y) ∈ A.S.pairs))

variable [DecidableEq Alphabet] [Fintype Alphabet]

instance decidableLab (x : D) (a : Alphabet) : Decidable (A.Lab x a) :=
  inferInstanceAs (Decidable (∃ b, (x, b) ∈ A.J.pairs ∧ A.label b = a))

instance decidableQ1 : Decidable A.Q1 := by unfold Q1; infer_instance

variable (P : Specification Alphabet)

instance decidableQ2 : Decidable (A.Q2 P) := by unfold Q2; infer_instance
instance decidableQ3 : Decidable (A.Q3 P) := by unfold Q3; infer_instance
instance decidableQ4Marked : Decidable (A.Q4Marked P) := by
  unfold Q4Marked
  infer_instance

instance decidableQ4Prefix : Decidable (A.Q4Prefix P) := by
  unfold Q4Prefix
  infer_instance

instance decidableLegal : Decidable (A.Legal P) := by unfold Legal; infer_instance

end Realization
end TuranUniversality.Computation.MatchingSystem
