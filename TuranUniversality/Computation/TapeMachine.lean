module

public import TuranUniversality.Computation.StackMachine

/-!
# A finite-support ordinary tape-machine interpreter

The proved Mathlib simulations TM2 → TM1 → TM0 carry the universal stack
interpreter to an actual deterministic two-sided tape machine with a finite
alphabet and a finite closed set of accessible states.  Its input is an explicit
finite tape word encoding a natural number.

This is an alternative universal-machine model.  It is not yet identified with
the manuscript's one-sided, common-head read-only/work-track machine, and the
finite-window/reset-tableau theorem is not asserted here.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Nat.Partrec (Code)
open Turing

/-- The stack simulator has exactly four stack indices. -/
instance stackIndexFintype : Fintype PartrecToTM2.K' where
  elems := {PartrecToTM2.K'.main, .rev, .aux, .stack}
  complete k := by cases k <;> simp

/-- The finite alphabet of the ordinary tape simulator. -/
abbrev TapeAlphabet :=
  TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')

/-- The Post-machine simulator of the stack evaluator. -/
def postProgram := TM2to1.tr PartrecToTM2.tr

/-- State labels for the ordinary tape-machine simulator. -/
abbrev TapeLabel := TM1to0.Λ' postProgram

/-- The deterministic TM0 transition function.  A compiled program selects its
initial state; this transition function is otherwise fixed. -/
def tapeProgram [Inhabited PartrecToTM2.Λ'] : TM0.Machine TapeAlphabet TapeLabel :=
  TM1to0.tr postProgram

/-- The concrete finite initial tape word for a natural input. -/
def tapeInput (n : ℕ) : List TapeAlphabet :=
  TM2to1.trInit (Γ := fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
    PartrecToTM2.K'.main (PartrecToTM2.trList [n])

/-- Run the ordinary tape simulator with the fixed start state determined by `c`. -/
def tapeRun (c : ToPartrec.Code) (n : ℕ) : Part (ListBlank TapeAlphabet) :=
  letI : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  TM0.eval tapeProgram (tapeInput n)

set_option backward.isDefEq.respectTransparency false in
theorem tapeRun_dom_iff_stackRun (c : ToPartrec.Code) (n : ℕ) :
    (tapeRun c n).Dom ↔ (stackRun c n).Dom := by
  let _ : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  unfold tapeRun tapeProgram
  rw [TM1to0.tr_eval]
  unfold postProgram tapeInput
  rw [TM2to1.tr_eval_dom]
  change (StateTransition.eval (TM2.step PartrecToTM2.tr)
    (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n]))).Dom ↔ _
  have hi :
      (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n]) : PartrecToTM2.Cfg') =
        PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp [PartrecToTM2.K'.elim, Function.update]
  rw [hi]
  rfl

/-- A finite state set supporting the tape simulator for the fixed program `c`. -/
noncomputable def tapeStateSupport (c : ToPartrec.Code) : Finset TapeLabel :=
  TM1to0.trStmts postProgram (TM2to1.trSupp PartrecToTM2.tr (stackStateSupport c))

set_option backward.isDefEq.respectTransparency false in
/-- Every machine transition stays inside the specified finite state set. -/
theorem tapeStateSupport_closed (c : ToPartrec.Code) :
    letI : Inhabited PartrecToTM2.Λ' :=
      ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
    TM0.Supports tapeProgram ↑(tapeStateSupport c) := by
  let _ : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  exact TM1to0.tr_supports postProgram
    (TM2to1.tr_supports PartrecToTM2.tr (stackStateSupport_closed c))

/-- There is one fixed deterministic finite-support ordinary tape-machine
interpreter for standard program halting. -/
theorem exists_universal_tapeProgram :
    ∃ c : ToPartrec.Code, ∀ e : Code,
      (tapeRun c (Encodable.encode e)).Dom ↔ Halts e := by
  obtain ⟨c, hc⟩ := exists_universal_stackProgram
  exact ⟨c, fun e => (tapeRun_dom_iff_stackRun c _).trans (hc e)⟩

/-- One fixed ordinary tape program realizes the literal binary-word evaluator. -/
theorem exists_word_tapeProgram :
    ∃ c : ToPartrec.Code, ∀ w : BinaryWord,
      (tapeRun c (encodeWord w)).Dom ↔ WordHalts w := by
  obtain ⟨c, hc⟩ := exists_word_stackProgram
  exact ⟨c, fun w => (tapeRun_dom_iff_stackRun c _).trans (hc w)⟩

end TuranUniversality.Computation
