module

public import Mathlib.Computability.Primrec.List
public import Lean.Elab.Tactic.Omega

/-!
# Primitive-recursive finite binary input encoding

Binary words are literal finite lists of Boolean symbols.  Digits are stored
least-significant first.  Encoding is implemented by repeated binary increment;
its running time is irrelevant to primitive recursiveness.  The decoding theorem
proves that the representation does not identify distinct natural numbers.
-/

@[expose] public section

namespace TuranUniversality.Computation

/-- A finite word over the two-letter alphabet. -/
abbrev BinaryWord := List Bool

/-- The standard injective encoding of the entire literal finite word.
Unlike numerical binary value, this preserves trailing zero symbols. -/
def encodeWord : BinaryWord → ℕ := Encodable.encode

/-- Partial inverse to the exact finite-word encoding. -/
def decodeWord : ℕ → Option BinaryWord := Encodable.decode

@[simp] theorem decodeWord_encodeWord (w : BinaryWord) :
    decodeWord (encodeWord w) = some w := Encodable.encodek w

theorem encodeWord_injective : Function.Injective encodeWord :=
  Encodable.encode_injective

theorem encodeWord_primrec : Primrec encodeWord := Primrec.encode

theorem decodeWord_primrec : Primrec decodeWord := Primrec.decode

/-- The numerical value of a little-endian binary word.  This is a numerical
payload decoder, not an injective encoding of arbitrary literal words. -/
def binaryValue (w : BinaryWord) : ℕ :=
  w.foldr (fun b n => bif b then 2 * n + 1 else 2 * n) 0

@[simp] theorem binaryValue_nil : binaryValue [] = 0 := rfl

@[simp] theorem binaryValue_false_cons (w : BinaryWord) :
    binaryValue (false :: w) = 2 * binaryValue w := rfl

@[simp] theorem binaryValue_true_cons (w : BinaryWord) :
    binaryValue (true :: w) = 2 * binaryValue w + 1 := rfl

/-- Add one to a little-endian binary word, carrying through initial true bits. -/
def incrementBits : BinaryWord → BinaryWord
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: incrementBits w

theorem binaryValue_incrementBits (w : BinaryWord) :
    binaryValue (incrementBits w) = binaryValue w + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [incrementBits, ih]
    omega

/-- A specific effective binary representation of a natural number. -/
def binaryEncode : ℕ → BinaryWord :=
  Nat.rec [] (fun _ w => incrementBits w)

@[simp] theorem binaryEncode_zero : binaryEncode 0 = [] := rfl

@[simp] theorem binaryEncode_succ (n : ℕ) :
    binaryEncode (n + 1) = incrementBits (binaryEncode n) := rfl

@[simp] theorem binaryValue_binaryEncode (n : ℕ) :
    binaryValue (binaryEncode n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binaryValue_incrementBits, ih]

theorem binaryEncode_injective : Function.Injective binaryEncode := by
  intro m n h
  simpa only [binaryValue_binaryEncode] using congrArg binaryValue h

/-- Decoding a finite word is primitive recursive in Mathlib's standard coding. -/
theorem binaryValue_primrec : Primrec binaryValue := by
  have hstep : Primrec (fun p : Bool × ℕ => bif p.1 then 2 * p.2 + 1 else 2 * p.2) :=
    Primrec.cond Primrec.fst
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const 1))
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (hstep.comp Primrec.snd).to₂

/-- Carry propagation is primitive recursive, not merely Lean-executable. -/
theorem incrementBits_primrec : Primrec incrementBits := by
  have hstep : Primrec (fun p : Bool × BinaryWord × BinaryWord =>
      bif p.1 then false :: p.2.2 else true :: p.2.1) :=
    Primrec.cond Primrec.fst
      (Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp Primrec.snd))
  apply (Primrec.list_rec Primrec.id (Primrec.const [true])
    (hstep.comp Primrec.snd).to₂).of_eq
  intro w
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => rfl
    | true => exact congrArg (List.cons false) ih

/-- Encoding naturals as binary words is primitive recursive. -/
theorem binaryEncode_primrec : Primrec binaryEncode :=
  Primrec.nat_rec₁ [] (incrementBits_primrec.comp Primrec.snd).to₂

end TuranUniversality.Computation
