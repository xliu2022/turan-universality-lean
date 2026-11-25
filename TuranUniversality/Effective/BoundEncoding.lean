module

public import TuranUniversality.Effective.LocalTables
public import TuranUniversality.Reduction.DensityDichotomy

@[expose] public section

/-! # Primitive-recursive bounds for the actual forbidden-core enumeration -/

namespace TuranUniversality.Effective

open TuranUniversality.Computation Construction Selector Reduction
open scoped BigOperators

theorem rootSearchBound_primrec (q : ℕ) : Primrec (rootSearchBound q) := by
  have hp (j : ℕ) : Primrec (fun w : ℕ => (q * w) ^ j) := by
    induction j with
    | zero => simpa using (Primrec.const (1 : ℕ) : Primrec (fun _ : ℕ => (1 : ℕ)))
    | succ j ih =>
        simpa only [pow_succ, id_eq] using Primrec.nat_mul.comp ih
          (Primrec.nat_mul.comp (Primrec.const q) Primrec.id)
  have hsum (n : ℕ) : Primrec (fun w : ℕ => ∑ j ∈ Finset.range n, (q * w) ^ j) := by
    induction n with
    | zero => simpa using (Primrec.const (0 : ℕ) : Primrec (fun _ : ℕ => (0 : ℕ)))
    | succ n ih => simpa only [Finset.sum_range_succ] using Primrec.nat_add.comp ih (hp n)
  exact Primrec.nat_mul.comp Primrec.id (hsum (q + 1))

noncomputable def forbiddenCoreBound (U : Interpreter) (β : BinaryWord) : ℕ :=
  admissibleWitnessBound (RootLabels (Fintype.card U.Alphabet)) (U.specification β) +
    (guardGraph TapeAlphabet U.State).1

theorem forbiddenCoreBound_primrec (U : Interpreter) : Primrec (forbiddenCoreBound U) := by
  let q := Fintype.card (RootLabels (Fintype.card U.Alphabet))
  have hw : Primrec (fun β : BinaryWord => q + ((U.specification β).witnessBound + 3)) :=
    Primrec.nat_add.comp (Primrec.const q)
      (Primrec.nat_add.comp (witnessBound_primrec U) (Primrec.const 3))
  exact Primrec.nat_add.comp ((rootSearchBound_primrec q).comp hw)
    (Primrec.const (guardGraph TapeAlphabet U.State).1)

theorem forbiddenCores_eq_forbiddenBasis (U : Interpreter) (β : BinaryWord) :
    forbiddenCores U.machine (Interpreter.input β) =
      @FiniteGraph.forbiddenBasis 3
        (FiniteGraph.guardedClass
          (admissibleClass (compilerSignature U.Alphabet)
            (colorLabel (LocalSystem.background (Γ := TapeAlphabet) (Λ := U.State)))
            (U.specification β)) (guardGraph TapeAlphabet U.State))
        (fun _ => Classical.propDecidable _)
        (forbiddenCoreBound U β) := by
  classical
  ext A
  rw [forbiddenCores, mem_guardedAdmissibleBasis, FiniteGraph.mem_forbiddenBasis]
  simp only [FiniteGraph.guardedClass, not_or, not_not]
  rfl

end TuranUniversality.Effective
