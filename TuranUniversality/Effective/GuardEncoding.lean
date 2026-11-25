module

public import TuranUniversality.Effective.GraphEmbeddingPrimrec
public import TuranUniversality.Effective.BoundEncoding

@[expose] public section

/-! # The actual guard-containment test is primitive recursive -/

namespace TuranUniversality.Effective

open TuranUniversality.Computation Reduction

noncomputable def fixedGuardCode (U : Interpreter) : GraphCode :=
  encodeFiniteGraph (guardGraph TapeAlphabet U.State)

def GuardPresent (U : Interpreter) (g : GraphCode) : Prop :=
  CodeContains (fixedGuardCode U) g

noncomputable instance (U : Interpreter) (g : GraphCode) : Decidable (GuardPresent U g) := by
  unfold GuardPresent
  infer_instance

theorem guardPresent_primrec (U : Interpreter) : PrimrecPred (GuardPresent U) :=
  codeContains_primrec.comp (Primrec.const (fixedGuardCode U)) Primrec.id

theorem guardPresent_iff (U : Interpreter) (g : GraphCode) :
    GuardPresent U g ↔ (guardGraph TapeAlphabet U.State).Contains (decodeGraphCode g) := by
  have h : GuardPresent U g ↔ (decodeGraphCode (fixedGuardCode U)).Contains (decodeGraphCode g) :=
    codeContains_iff (fixedGuardCode U) g
  simpa only [fixedGuardCode, decode_encode_finiteGraph] using h

end TuranUniversality.Effective
