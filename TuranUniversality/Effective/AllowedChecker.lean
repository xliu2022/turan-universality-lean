module

public import TuranUniversality.Effective.AdmissiblePrimrec
public import TuranUniversality.Effective.LocalTables
public import TuranUniversality.Reduction.LegalClass

/-!
# A complete primitive-recursive checker for the actual reduction class

For each fixed finite universal interpreter this file gives the Boolean
acceptance procedure used by the graph compiler. It enumerates partial root
assignments and checks their actual root incidences, partial matchings, marks,
and input-dependent local rules. The equivalence below is with `Reduction.Legal`
itself; it is not a separate assumed correctness condition.
-/

@[expose] public section

namespace TuranUniversality.Effective

open Computation Construction

/-- A fixed finite coding for the root alphabet of the concrete signature. -/
noncomputable instance rootLabelsPrimcodable (A : ℕ) : Primcodable (RootLabels A) :=
  Primcodable.ofEquiv (Fin (Fintype.card (RootLabels A))) (Fintype.equivFin _)

/-- The total bounded legality decision used by the primitive-recursive compiler. -/
noncomputable def allowedCheck (U : Interpreter) (β : BinaryWord) (g : GraphCode) : Bool :=
  admissibleCheck (compilerSignature U.Alphabet)
    (colorLabel (LocalSystem.background (Γ := TapeAlphabet) (Λ := U.State)))
    g (U.specification β)

/-- Both the literal input and the finite graph vary primitively recursively. -/
theorem allowedCheck_primrec (U : Interpreter) : Primrec₂ (allowedCheck U) :=
  (admissibleCheck_primrec (compilerSignature U.Alphabet)
    (colorLabel (LocalSystem.background (Γ := TapeAlphabet) (Λ := U.State)))).comp
      Primrec.snd ((interpreterSpecification_primrec U).comp Primrec.fst)

/-- Acceptance is exactly membership in the actual mathematical legal class. -/
theorem allowedCheck_correct (U : Interpreter) (β : BinaryWord) (g : GraphCode) :
    allowedCheck U β g = true ↔
      Reduction.Legal U.machine (Interpreter.input β) (decodeGraph g) :=
  admissibleCheck_correct (compilerSignature U.Alphabet)
    (colorLabel (LocalSystem.background (Γ := TapeAlphabet) (Λ := U.State)))
    g (U.specification β)

end TuranUniversality.Effective
