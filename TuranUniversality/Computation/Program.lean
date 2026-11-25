module

public import TuranUniversality.Computation.Binary
public import Mathlib.Computability.Halting
public import Mathlib.Computability.Reduce

/-!
# Standard halting semantics and finite certificates

This module uses Mathlib's actual partial-recursive program semantics.  It does
not postulate a halting predicate or the computability of a compiler.  A binary
input beginning with true decodes a program and runs it on input zero; every
other input diverges.  This provides an explicitly encoded universal partial
evaluator and the reserved nonhalting word `[false]`.

The subsequent machine modules compile this evaluator into a fixed finite-state
two-sided tape machine. The finite-window, static-input, local reset, and marked
model bridges are proved for that precise machine representation. The chosen
representation differs from the manuscript's one-sided two-track presentation;
the halting semantics used by the main theorem are connected in both directions.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Nat.Partrec (Code)

/-- A standard program halts when its partial evaluation at zero is defined. -/
def Halts (c : Code) : Prop := (c.eval 0).Dom

/-- A finite certificate records the fuel bound and returned value of `evaln`.
The bound is Mathlib evaluator fuel, not a claimed Turing-machine step count. -/
def HaltCertificate (c : Code) (w : ℕ × ℕ) : Prop :=
  Code.evaln w.1 c 0 = some w.2

instance (c : Code) (w : ℕ × ℕ) : Decidable (HaltCertificate c w) :=
  inferInstanceAs (Decidable (Code.evaln w.1 c 0 = some w.2))

/-- The finite certificate test is an explicit Boolean computation. -/
def checkHaltCertificate (c : Code) (w : ℕ × ℕ) : Bool :=
  decide (HaltCertificate c w)

theorem checkHaltCertificate_primrec : Primrec₂ checkHaltCertificate := by
  have heval : Primrec (fun p : Code × (ℕ × ℕ) => Code.evaln p.2.1 p.1 0) :=
    Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.snd).pair Primrec.fst).pair (Primrec.const 0))
  exact (Primrec.eq.decide.comp heval
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))).to₂

theorem halts_iff_certificate (c : Code) :
    Halts c ↔ ∃ w, HaltCertificate c w := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
    exact ⟨(k, v), hk⟩
  · rintro ⟨⟨k, v⟩, hv⟩
    exact Part.dom_iff_mem.mpr ⟨v, Code.evaln_sound hv⟩

theorem haltCertificate_mono {c : Code} {k l v : ℕ} (hkl : k ≤ l)
    (h : HaltCertificate c (k, v)) : HaltCertificate c (l, v) :=
  Code.evaln_mono hkl h

theorem halts_recursivelyEnumerable : REPred Halts :=
  ComputablePred.halting_problem_re 0

theorem halts_not_computable : ¬ ComputablePred Halts :=
  ComputablePred.halting_problem 0

theorem nonhalting_not_recursivelyEnumerable : ¬ REPred (fun c => ¬ Halts c) :=
  ComputablePred.halting_problem_not_re 0

/-- Encode a standard program as an enabled binary input. -/
def encodeProgram (c : Code) : BinaryWord :=
  true :: binaryEncode (Encodable.encode c)

/-- Decode the program specified by the tail of a binary input. -/
def decodeProgram (w : BinaryWord) : Code :=
  Denumerable.ofNat Code (binaryValue w.tail)

/-- The leading bit distinguishes genuine program inputs from reserved divergence. -/
def inputEnabled (w : BinaryWord) : Bool := w.head?.getD false

@[simp] theorem decodeProgram_encodeProgram (c : Code) :
    decodeProgram (encodeProgram c) = c := by
  simp [decodeProgram, encodeProgram]

@[simp] theorem inputEnabled_encodeProgram (c : Code) :
    inputEnabled (encodeProgram c) = true := rfl

theorem encodeProgram_injective : Function.Injective encodeProgram := by
  intro c d h
  simpa only [decodeProgram_encodeProgram] using congrArg decodeProgram h

theorem encodeProgram_primrec : Primrec encodeProgram :=
  Primrec.list_cons.comp (Primrec.const true)
    (binaryEncode_primrec.comp Primrec.encode)

theorem decodeProgram_primrec : Primrec decodeProgram :=
  (Primrec.ofNat Code).comp (binaryValue_primrec.comp Primrec.list_tail)

theorem inputEnabled_primrec : Primrec inputEnabled :=
  Primrec.option_getD.comp Primrec.list_head? (Primrec.const false)

/-- An explicit universal partial evaluator on finite binary words. -/
def wordEval (w : BinaryWord) : Part ℕ :=
  bif inputEnabled w then (decodeProgram w).eval 0 else Part.none

/-- Halting of the explicit binary-input evaluator. -/
def WordHalts (w : BinaryWord) : Prop := (wordEval w).Dom

@[simp] theorem wordEval_encodeProgram (c : Code) :
    wordEval (encodeProgram c) = c.eval 0 := by
  simp [wordEval]

@[simp] theorem wordHalts_encodeProgram (c : Code) :
    WordHalts (encodeProgram c) ↔ Halts c := by
  simp [WordHalts, Halts]

theorem wordEval_partrec : Partrec wordEval :=
  Partrec.cond inputEnabled_primrec.to_comp
    (Code.eval_part.comp decodeProgram_primrec.to_comp (Computable.const 0))
    Partrec.none

theorem wordHalts_recursivelyEnumerable : REPred WordHalts :=
  wordEval_partrec.dom_re

theorem halts_manyOne_wordHalts : Halts ≤₀ WordHalts :=
  ⟨encodeProgram, encodeProgram_primrec.to_comp, fun c => (wordHalts_encodeProgram c).symm⟩

theorem wordHalts_not_computable : ¬ ComputablePred WordHalts := by
  intro h
  exact halts_not_computable
    (ComputablePred.computable_of_manyOneReducible halts_manyOne_wordHalts h)

/-- The literal one-letter input `0` is provably nonhalting. -/
theorem zeroWord_not_halting : ¬ WordHalts [false] := by
  simp [WordHalts, wordEval, inputEnabled]

/-- The same evaluator on the exact natural-number encoding of literal words.
Invalid encodings diverge. -/
def encodedWordEval (n : ℕ) : Part ℕ :=
  (decodeWord n : Part BinaryWord).bind wordEval

theorem encodedWordEval_partrec : Partrec encodedWordEval :=
  decodeWord_primrec.to_comp.ofOption.bind
    (wordEval_partrec.comp Computable.snd).to₂

@[simp] theorem encodedWordEval_encodeWord (w : BinaryWord) :
    encodedWordEval (encodeWord w) = wordEval w := by
  simp [encodedWordEval]

end TuranUniversality.Computation
