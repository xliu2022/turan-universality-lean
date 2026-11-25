module

public import TuranUniversality.Computation.Program
public import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# A proved bridge to a finite-support stack Turing machine

Mathlib proves a compilation from partial-recursive functions into its TM2
stack-machine model.  Here the compilation is instantiated for a single fixed
universal evaluator.  The accessible state set is finite and independent of
the program input.

This does not yet normalize the machine into the paper's one-sided
read-only-input/work-track model or prove the local reset-tableau equivalence.
The theorem names and signatures keep that boundary explicit.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Nat.Partrec (Code)
open Turing

/-- A run of a compiled finite-support TM2 stack program on a single natural input. -/
def stackRun (c : ToPartrec.Code) (n : ℕ) : Part PartrecToTM2.Cfg' :=
  StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c [n])

set_option backward.isDefEq.respectTransparency false in
/-- Every partial-recursive function has a stack program with the same domain.
This is a semantic bridge to Mathlib's actual state-transition machine. -/
theorem exists_stackProgram (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ c : ToPartrec.Code, ∀ n, (stackRun c n).Dom ↔ (f n).Dom := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨c, fun n => ?_⟩
  have hcn := hc (⟨[n], rfl⟩ : List.Vector ℕ 1)
  unfold stackRun
  rw [PartrecToTM2.tr_eval c [n]]
  change (c.eval [n]).Dom ↔ (f n).Dom
  rw [hcn]
  rfl

/-- The actual finite accessible-state support of a compiled stack program. -/
def stackStateSupport (c : ToPartrec.Code) : Finset PartrecToTM2.Λ' :=
  PartrecToTM2.codeSupp c PartrecToTM2.Cont'.halt

/-- All transitions from the finite support stay in the support, with the
correct initial label included. -/
theorem stackStateSupport_closed (c : ToPartrec.Code) :
    @TM2.Supports _ _ _ _
      ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
      PartrecToTM2.tr (stackStateSupport c) :=
  PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt

/-- One fixed finite-support stack program simulates every standard program.
The program `c` is chosen before the quantified input program `e`. -/
theorem exists_universal_stackProgram :
    ∃ c : ToPartrec.Code, ∀ e : Code,
      (stackRun c (Encodable.encode e)).Dom ↔ Halts e := by
  have hf : Partrec (fun n : ℕ => (Denumerable.ofNat Code n).eval 0) :=
    Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0)
  obtain ⟨c, hc⟩ := exists_stackProgram _ hf
  refine ⟨c, fun e => ?_⟩
  simpa [Halts] using hc (Encodable.encode e)

/-- A single fixed stack program realizes the exact literal binary-word
evaluator, including its reserved nonhalting input. -/
theorem exists_word_stackProgram :
    ∃ c : ToPartrec.Code, ∀ w : BinaryWord,
      (stackRun c (encodeWord w)).Dom ↔ WordHalts w := by
  obtain ⟨c, hc⟩ := exists_stackProgram encodedWordEval encodedWordEval_partrec
  refine ⟨c, fun w => ?_⟩
  simpa [WordHalts] using hc (encodeWord w)

end TuranUniversality.Computation
