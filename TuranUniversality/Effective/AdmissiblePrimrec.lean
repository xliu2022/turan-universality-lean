module

public import TuranUniversality.Effective.AdmissibleChecker
public import TuranUniversality.Effective.RootedPrimrec

/-!
# Primitive recursion of the complete admissibility decision

The procedure enumerates every partial assignment of the fixed root alphabet
to the finite graph. Each assignment is checked using the literal incidence
queries and the actual local computational tables. Both the bounded assignment
search and all checks have primitive-recursion proofs.
-/

@[expose] public section

namespace TuranUniversality.Effective

open Weighted Selector Computation.MatchingSystem

variable {Roots Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Primcodable Roots]
    [Fintype Code] [DecidableEq Code] [Primcodable Code]
    [Fintype Kinds] [DecidableEq Kinds] [Primcodable Kinds]
    [Fintype Alphabet] [DecidableEq Alphabet] [Inhabited Alphabet] [Primcodable Alphabet]

namespace RootedCode

theorem fullOK_primrec (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet) :
    PrimrecRel (FullOK S color) := by
  exact (valid_primrec.comp Primrec.fst).and
    (((incidenceOK_primrec S).comp Primrec.fst).and
      (MatchingCode.legal_primrec.comp
        ((matchingCode_primrec S color).comp Primrec.fst) Primrec.snd))

theorem check_primrec (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet) :
    Primrec₂ (check S color) := (fullOK_primrec S color).decide

end RootedCode

theorem admissibleOK_primrec (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) : PrimrecRel (AdmissibleOK S color) := by
  exact exists_list_primrec
    (assignmentWords_primrec.comp (Primrec.fst.comp Primrec.fst))
    ((RootedCode.fullOK_primrec S color).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst))

theorem admissibleCheck_primrec (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) : Primrec₂ (admissibleCheck S color) :=
  (admissibleOK_primrec S color).decide

end TuranUniversality.Effective
