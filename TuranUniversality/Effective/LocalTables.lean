module

public import TuranUniversality.Computation.Interpreter
public import TuranUniversality.Effective.InputEncoding
public import TuranUniversality.Effective.RuleEncoding

/-!
# Primitive-recursive construction of the actual input-dependent local table

Fixed finite alphabets and their finite powersets receive fixed finite
encodings.  The machine tables are constants; the entire varying Start-prefix
table is proved primitive recursive, including its exact tape-input encoding.
-/

@[expose] public section

namespace TuranUniversality.Effective

open TuranUniversality.Computation
open LocalSystem MatchingSystem

noncomputable instance staticSymbolPrimcodable : Primcodable (StaticInput.Symbol TapeAlphabet) :=
  Primcodable.ofEquiv (Fin (Fintype.card (StaticInput.Symbol TapeAlphabet))) (Fintype.equivFin _)

noncomputable instance localAlphabetPrimcodable (U : Interpreter) : Primcodable U.Alphabet :=
  Primcodable.ofEquiv (Fin (Fintype.card U.Alphabet)) (Fintype.equivFin _)

noncomputable instance localSetPrimcodable (U : Interpreter) : Primcodable (Finset U.Alphabet) :=
  Primcodable.ofEquiv (Fin (Fintype.card (Finset U.Alphabet))) (Fintype.equivFin _)

theorem staticInputWord_primrec : Primrec (StaticInput.inputWord (Γ := TapeAlphabet)) := by
  have hstart : Primrec (StaticInput.Symbol.start (Γ := TapeAlphabet)) := Primrec.dom_finite _
  have hletter : Primrec (StaticInput.Symbol.input (Γ := TapeAlphabet)) := Primrec.dom_finite _
  have hm : Primrec (fun p : List TapeAlphabet × (TapeAlphabet × List TapeAlphabet) =>
      p.2.2.map StaticInput.Symbol.input) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) (hletter.comp Primrec.snd).to₂
  exact (Primrec.list_casesOn Primrec.id (Primrec.const [])
    (Primrec.list_cons.comp (hstart.comp (Primrec.fst.comp Primrec.snd)) hm).to₂).of_eq
      (fun l => by cases l <;> rfl)

theorem interpreterInput_primrec : Primrec Interpreter.input := wordTapeInput_primrec

/-- Every permitted-color set in the finite Start-prefix word is explicitly
computed from the primitive-recursive exact input word. -/
theorem inputPrefix_primrec (U : Interpreter) :
    Primrec (fun β : BinaryWord => (U.specification β).inputPrefix) := by
  let permit : StaticInput.Symbol TapeAlphabet → Finset U.Alphabet := fun s =>
    Finset.univ.filter fun a => staticPart a = some s
  have hp : Primrec permit := Primrec.dom_finite _
  have hw : Primrec (fun β : BinaryWord =>
      StaticInput.inputWord (Interpreter.input β) ++ [StaticInput.Symbol.finish]) :=
    Primrec.list_append.comp (staticInputWord_primrec.comp interpreterInput_primrec)
      (Primrec.const [StaticInput.Symbol.finish (Γ := TapeAlphabet)])
  exact Primrec.list_map hw (hp.comp Primrec.snd).to₂

/-- The entire actual local specification has a proved primitive-recursive
encoding; every field except its finite prefix is a fixed table. -/
theorem interpreterSpecification_primrec (U : Interpreter) : Primrec U.specification := by
  apply (Primrec.of_equiv_iff specificationEquiv).mp
  exact Primrec.pair (Primrec.const (U.specification []).leftWall)
    (Primrec.pair (Primrec.const (U.specification []).initial)
      (Primrec.pair (Primrec.const (U.specification []).horizontal)
        (Primrec.pair (Primrec.const (U.specification []).evolution)
          (Primrec.pair (Primrec.const (U.specification []).prefixTrigger) (inputPrefix_primrec U)))))

/-- The concrete local-failure bound, including the encoded tape word, is
primitive recursive as a function of the original literal binary input. -/
theorem witnessBound_primrec (U : Interpreter) :
    Primrec (fun β : BinaryWord => (U.specification β).witnessBound) := by
  exact (Primrec.nat_add.comp (Primrec.const 13)
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.list_length.comp interpreterInput_primrec))).of_eq
        (fun β => (U.specification_witness_bound β).symm)

/-- Reading one input-prefix entry is primitive recursive. -/
theorem inputPrefix_get_primrec (U : Interpreter) :
    Primrec₂ (fun (β : BinaryWord) (j : ℕ) => (U.specification β).inputPrefix[j]?) :=
  Primrec.list_getElem?.comp₂ (inputPrefix_primrec U |>.comp Primrec.fst).to₂ Primrec₂.right

end TuranUniversality.Effective
