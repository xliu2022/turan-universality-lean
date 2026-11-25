module

public import TuranUniversality.Computation.TapeMachine
public import Mathlib.Computability.Encoding

/-!
# Primitive-recursive input for the actual finite tape interpreter

The fixed finite alphabets receive fixed finite encodings.  The theorem below
proves primitive recursiveness of the complete word-to-tape input map, including
Mathlib's binary stack representation and its reversal in the tape simulator.
-/

@[expose] public section

namespace TuranUniversality.Effective

open Turing
open TuranUniversality.Computation

/-- A fixed finite encoding of the four stack symbols. -/
noncomputable instance stackSymbolPrimcodable : Primcodable PartrecToTM2.Γ' :=
  Primcodable.ofEquiv (Fin (Fintype.card PartrecToTM2.Γ')) (Fintype.equivFin _)

/-- A fixed finite encoding of the ordinary tape alphabet. -/
noncomputable instance tapeAlphabetPrimcodable : Primcodable TapeAlphabet :=
  Primcodable.ofEquiv (Fin (Fintype.card TapeAlphabet)) (Fintype.equivFin _)

theorem encodePosNum_succ (n : PosNum) :
    Computability.encodePosNum n.succ = incrementBits (Computability.encodePosNum n) := by
  induction n with
  | one => rfl
  | bit0 n ih => rfl
  | bit1 n ih => simp [Computability.encodePosNum, PosNum.succ, incrementBits, ih]

theorem encodeNum_succ (n : Num) :
    Computability.encodeNum n.succ = incrementBits (Computability.encodeNum n) := by
  cases n with
  | zero => rfl
  | pos n => exact encodePosNum_succ n

/-- The binary encoding used internally by Mathlib agrees exactly with the
previously proved primitive-recursive repeated-increment representation. -/
theorem encodeNat_eq_binaryEncode (n : ℕ) : Computability.encodeNat n = binaryEncode n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Computability.encodeNat, Nat.cast_succ, Num.add_one,
      encodeNum_succ, binaryEncode_succ] using congrArg incrementBits ih

/-- Translate a Boolean bit to the corresponding stack symbol. -/
def bitSymbol (b : Bool) : PartrecToTM2.Γ' := bif b then .bit1 else .bit0

theorem trPosNum_eq_map (n : PosNum) :
    PartrecToTM2.trPosNum n = (Computability.encodePosNum n).map bitSymbol := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [PartrecToTM2.trPosNum, Computability.encodePosNum, bitSymbol, ih]
  | bit1 n ih => simp [PartrecToTM2.trPosNum, Computability.encodePosNum, bitSymbol, ih]

theorem trNat_eq_binaryEncode (n : ℕ) :
    PartrecToTM2.trNat n = (binaryEncode n).map bitSymbol := by
  rw [← encodeNat_eq_binaryEncode]
  unfold PartrecToTM2.trNat Computability.encodeNat
  generalize (n : Num) = m
  cases m with
  | zero => rfl
  | pos m => exact trPosNum_eq_map m

/-- Mathlib's actual stack-number input coding is primitive recursive. -/
theorem trNat_primrec : Primrec PartrecToTM2.trNat :=
  (Primrec.list_map binaryEncode_primrec
    ((Primrec.dom_finite bitSymbol).comp Primrec.snd).to₂).of_eq
      (fun n => (trNat_eq_binaryEncode n).symm)

theorem singletonStack_primrec : Primrec (fun n => PartrecToTM2.trList [n]) := by
  simpa only [PartrecToTM2.trList, List.cons_append, List.nil_append] using
    Primrec.list_append.comp trNat_primrec (Primrec.const [PartrecToTM2.Γ'.cons])

/-- The full concrete tape initializer is primitive recursive, including
reversal and the bottom-of-stack marker. -/
theorem tapeInput_primrec : Primrec tapeInput := by
  let letter : PartrecToTM2.Γ' → TapeAlphabet := fun a =>
    (false, Function.update (fun _ : PartrecToTM2.K' => none) .main (some a))
  let bottom : TapeAlphabet → TapeAlphabet := fun a => (true, a.2)
  have hletters : Primrec (fun n => (PartrecToTM2.trList [n]).reverse.map letter) :=
    Primrec.list_map (Primrec.list_reverse.comp singletonStack_primrec)
      ((Primrec.dom_finite letter).comp Primrec.snd).to₂
  exact (Primrec.list_cons.comp
      ((Primrec.dom_finite bottom).comp (Primrec.list_headI.comp hletters))
      (Primrec.list_tail.comp hletters)).of_eq (fun _ => rfl)

/-- This is the complete primitive-recursive conversion from literal binary
words to the finite tape input of the fixed interpreter. -/
theorem wordTapeInput_primrec : Primrec (fun β : BinaryWord => tapeInput (encodeWord β)) :=
  tapeInput_primrec.comp encodeWord_primrec

theorem tapeInput_nonempty (n : ℕ) : tapeInput n ≠ [] := by
  simp [tapeInput, TM2to1.trInit]

end TuranUniversality.Effective
