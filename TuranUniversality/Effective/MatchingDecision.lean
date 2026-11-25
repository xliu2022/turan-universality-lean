module

public import TuranUniversality.Effective.MatchingRulesPrimrec

/-! # The actual Boolean decision procedure for the encoded local rules -/

@[expose] public section

namespace TuranUniversality.Effective.MatchingCode

open Computation.MatchingSystem

variable {Alphabet : Type*} [Primcodable Alphabet] [Fintype Alphabet]
  [Inhabited Alphabet] [DecidableEq Alphabet]

set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000

instance (c : MatchingCode Alphabet) (x y : ℕ) : Decidable (c.H x y) :=
  inferInstanceAs (Decidable ((x, y) ∈ c.horizontal))
instance (c : MatchingCode Alphabet) (x y : ℕ) : Decidable (c.V x y) :=
  inferInstanceAs (Decidable ((x, y) ∈ c.vertical))
instance (c : MatchingCode Alphabet) (n x z : ℕ) : Decidable (c.HasPath n x z) :=
  inferInstanceAs (Decidable (CodePath c.horizontal n x z))

instance (c : MatchingCode Alphabet) : Decidable c.Q1 := by unfold Q1; infer_instance
instance (c : MatchingCode Alphabet) (P : Specification Alphabet) : Decidable (c.Q2 P) := by
  unfold Q2
  refine @Nat.decidableBallLT c.size _ (fun l hl => ?_)
  refine @Nat.decidableBallLT c.size _ (fun x hx => ?_)
  refine @Nat.decidableBallLT c.size _ (fun r hr => ?_)
  refine @Nat.decidableBallLT c.size _ (fun x' hx' => ?_)
  refine @Fintype.decidableForallFintype Alphabet _ (fun al => ?_) _
  refine @Fintype.decidableForallFintype Alphabet _ (fun ax => ?_) _
  refine @Fintype.decidableForallFintype Alphabet _ (fun ar => ?_) _
  refine @Fintype.decidableForallFintype Alphabet _ (fun b => ?_) _
  infer_instance
instance (c : MatchingCode Alphabet) (P : Specification Alphabet) : Decidable (c.Q3 P) := by
  unfold Q3
  infer_instance
instance (c : MatchingCode Alphabet) (P : Specification Alphabet) : Decidable (c.Q4Marked P) := by
  unfold Q4Marked
  infer_instance
instance (c : MatchingCode Alphabet) (P : Specification Alphabet) : Decidable (c.Q4Prefix P) := by
  unfold Q4Prefix
  infer_instance
instance (c : MatchingCode Alphabet) (P : Specification Alphabet) : Decidable (c.Legal P) := by
  unfold Legal
  infer_instance

def check (c : MatchingCode Alphabet) (P : Specification Alphabet) : Bool := decide (c.Legal P)

theorem check_primrec : Primrec₂ (check (Alphabet := Alphabet)) := legal_primrec.decide

@[simp] theorem check_eq_true (c : MatchingCode Alphabet) (P : Specification Alphabet) :
    c.check P = true ↔ c.Legal P := by simp [check]

/-- The executable bounded checker accepts precisely the actual local rules. -/
theorem check_correct {c : MatchingCode Alphabet} {A : Realization (Fin c.size) Alphabet}
    (h : c.Represents A) (P : Specification Alphabet) : c.check P = true ↔ A.Legal P :=
  (c.check_eq_true P).trans (h.legal_iff P)

end TuranUniversality.Effective.MatchingCode
