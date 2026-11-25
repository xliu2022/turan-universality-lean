module

public import TuranUniversality.Computation.FiniteMachine
public import TuranUniversality.Computation.ClosedConstruction
public import TuranUniversality.Computation.ClosedRecovery
public import TuranUniversality.Computation.LocalWitness

/-!
# A fixed finite interpreter and its exact local-model characterization

The witness below is obtained from Mathlib's proved compiler for partial
recursive functions.  Its ordinary two-sided tape model is intentional; all
finite-window, static-input, reset, and closed-component bridges have been
proved for that precise model.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Turing LocalSystem MatchingSystem

noncomputable instance tapeAlphabetDecidableEq : DecidableEq TapeAlphabet := Classical.decEq _

/-- A fixed supported interpreter, restricted to its literal finite state type. -/
structure Interpreter where
  program : ToPartrec.Code
  initial : Inhabited {q // q ∈ tapeStateSupport program}
  machine : @TM0.Machine TapeAlphabet {q // q ∈ tapeStateSupport program} initial
  correct : ∀ β : BinaryWord,
    (@TM0.eval TapeAlphabet {q // q ∈ tapeStateSupport program} initial inferInstance
      machine (tapeInput (encodeWord β))).Dom ↔ WordHalts β

theorem nonempty_interpreter : Nonempty Interpreter := by
  obtain ⟨c, initial, M, hM⟩ := exists_finite_word_tapeMachine
  exact ⟨⟨c, initial, M, hM⟩⟩

/-- The single interpreter used for every binary input. -/
noncomputable def universalInterpreter : Interpreter := Classical.choice nonempty_interpreter

namespace Interpreter

abbrev State (U : Interpreter) := {q // q ∈ tapeStateSupport U.program}

instance (U : Interpreter) : Inhabited U.State := U.initial
noncomputable instance (U : Interpreter) : Fintype U.State := inferInstance
noncomputable instance (U : Interpreter) : DecidableEq U.State := Classical.decEq _

abbrev Alphabet (U : Interpreter) := Label TapeAlphabet U.State

def input (β : BinaryWord) : List TapeAlphabet := tapeInput (encodeWord β)

theorem input_nonempty (β : BinaryWord) : input β ≠ [] := by
  simp [input, tapeInput, TM2to1.trInit]

noncomputable def specification (U : Interpreter) (β : BinaryWord) :
    Specification U.Alphabet := LocalSystem.specification U.machine (input β)

theorem specification_prefix_length (U : Interpreter) (β : BinaryWord) :
    (U.specification β).inputPrefix.length = (input β).length + 1 :=
  inputPrefix_length U.machine (input β)

theorem specification_witness_bound (U : Interpreter) (β : BinaryWord) :
    (U.specification β).witnessBound = 13 + 2 * (input β).length := by
  rw [Specification.witnessBound, specification_prefix_length]
  omega

/-- Any actual closed marked realization of the local rules forces `WordHalts`. -/
theorem closed_marked_halts (U : Interpreter) (β : BinaryWord)
    {D : Type*} [DecidableEq D] (A : Realization D U.Alphabet)
    (h : A.Legal (U.specification β)) (a : D) (ha : a ∈ A.marks)
    (hc : A.ClosedAt a) : WordHalts β :=
  (U.correct β).mp (A.closed_marked_halts U.machine (input β) h a ha hc)

/-- Every marked component of a legal nonhalting input has a missing incidence. -/
theorem nonhalting_open (U : Interpreter) (β : BinaryWord) (hn : ¬WordHalts β)
    {D : Type*} [DecidableEq D] (A : Realization D U.Alphabet)
    (h : A.Legal (U.specification β)) (a : D) (ha : a ∈ A.marks) : ¬A.ClosedAt a :=
  fun hc => hn (U.closed_marked_halts β A h a ha hc)

/-- A genuine halt supplies a concrete finite marked model with all the fixed
local tables and the exact primitive-recursively encoded input. -/
theorem halting_model (U : Interpreter) (β : BinaryWord) (h : WordHalts β) :
    ∃ (p m : ℕ) (P : PermutationModel U.machine (input β)
      (Fin (p + 1) × Fin (m + 3))) (x : Fin (p + 1) × Fin (m + 3)), P.MarkedAt x :=
  exists_marked_permutationModel U.machine (input β) (input_nonempty β) ((U.correct β).mpr h)

theorem halts_iff_marked_model (U : Interpreter) (β : BinaryWord) :
    WordHalts β ↔ ∃ (p m : ℕ) (P : PermutationModel U.machine (input β)
      (Fin (p + 1) × Fin (m + 3))) (x : Fin (p + 1) × Fin (m + 3)), P.MarkedAt x := by
  refine ⟨U.halting_model β, ?_⟩
  rintro ⟨p, m, P, x, hx⟩
  exact (U.correct β).mp (P.halts_of_marked x hx)

end Interpreter
end TuranUniversality.Computation
