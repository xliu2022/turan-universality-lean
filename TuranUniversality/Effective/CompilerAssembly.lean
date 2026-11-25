module

public import TuranUniversality.Effective.GuardEncoding
public import TuranUniversality.Effective.BasisEncoding
public import TuranUniversality.Effective.SingletonEncoding

@[expose] public section

/-! # Assembly of a proved legality checker into the actual singleton compiler

The remaining input to this module is an explicit checker with both a
primitive-recursion proof and an exact legality theorem. The final theorem
instantiates that input with the independently verified rooted-rule checker.
-/

namespace TuranUniversality.Effective

open TuranUniversality.Computation Reduction Construction Selector

set_option backward.isDefEq.respectTransparency false

noncomputable def coreRejection (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (β : BinaryWord) (g : GraphCode) : Bool :=
  !(allowed β g) && decide (GuardPresent U g)

theorem coreRejection_primrec (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : Primrec₂ allowed) : Primrec₂ (coreRejection U allowed) :=
  (Primrec.and.comp (Primrec.not.comp hallowed)
    ((guardPresent_primrec U).decide.comp Primrec.snd)).to₂

theorem coreRejection_iff (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : ∀ β g, allowed β g = true ↔ Legal U.machine (Interpreter.input β) (decodeGraph g))
    (β : BinaryWord) (g : GraphCode) :
    coreRejection U allowed β g = true ↔
      ¬ FiniteGraph.guardedClass
        (admissibleClass (compilerSignature U.Alphabet)
          (colorLabel (LocalSystem.background (Γ := TapeAlphabet) (Λ := U.State)))
          (U.specification β)) (guardGraph TapeAlphabet U.State) (decodeGraphCode g) := by
  have hn : ¬ (allowed β g = true) ↔
      ¬ Legal U.machine (Interpreter.input β) (decodeGraph g) := not_congr (hallowed β g)
  simpa only [coreRejection, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true, decide_eq_true_eq,
    guardPresent_iff, FiniteGraph.guardedClass, not_or, not_not,
    admissibleClass, Legal, Interpreter.specification, decodeGraphCode] using
      and_congr hn (guardPresent_iff U g)

noncomputable def coreCodes (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (β : BinaryWord) : List GraphCode :=
  filteredGraphCodes (forbiddenCoreBound U) (coreRejection U allowed) β

theorem coreCodes_primrec (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : Primrec₂ allowed) : Primrec (coreCodes U allowed) :=
  filteredGraphCodes_primrec _ _ (forbiddenCoreBound_primrec U)
    (coreRejection_primrec U allowed hallowed)

theorem coreCodes_decode (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : ∀ β g, allowed β g = true ↔ Legal U.machine (Interpreter.input β) (decodeGraph g))
    (β : BinaryWord) :
    ((coreCodes U allowed β).map decodeGraphCode).toFinset =
      forbiddenCores U.machine (Interpreter.input β) := by
  classical
  rw [forbiddenCores_eq_forbiddenBasis]
  have h := filteredGraphCodes_decode _ (forbiddenCoreBound U) (coreRejection U allowed)
    (coreRejection_iff U allowed hallowed) β
  apply h.trans
  ext A
  simp only [FiniteGraph.mem_forbiddenBasis]

noncomputable def compileWithChecker (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (β : BinaryWord) : GraphCode := singletonCode (coreCodes U allowed β)

theorem compileWithChecker_primrec (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : Primrec₂ allowed) : Primrec (compileWithChecker U allowed) :=
  singletonCode_primrec.comp (coreCodes_primrec U allowed hallowed)

theorem compileWithChecker_density (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : ∀ β g, allowed β g = true ↔ Legal U.machine (Interpreter.input β) (decodeGraph g))
    (β : BinaryWord) :
    turanDensity (decodeGraph (compileWithChecker U allowed β)) =
      turanDensity (forbiddenGraph U.machine (Interpreter.input β)).2 :=
  singletonCode_density _ _ (coreCodes_decode U allowed hallowed β)
    (forbiddenCores_nonempty _ _) (fun _ h => forbiddenCores_has_edges _ _ h)

theorem compileWithChecker_has_edges (U : Interpreter) (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : ∀ β g, allowed β g = true ↔ Legal U.machine (Interpreter.input β) (decodeGraph g))
    (β : BinaryWord) : (decodeGraph (compileWithChecker U allowed β)).edges.Nonempty :=
  singletonCode_edges_nonempty _ _ (coreCodes_decode U allowed hallowed β)
    (forbiddenCores_nonempty _ _) (fun _ h => forbiddenCores_has_edges _ _ h)

theorem compileWithChecker_density_eq_iff (U : Interpreter)
    (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : ∀ β g, allowed β g = true ↔ Legal U.machine (Interpreter.input β) (decodeGraph g))
    (β : BinaryWord) :
    turanDensity (decodeGraph (compileWithChecker U allowed β)) =
      (threshold (alphabetSize TapeAlphabet U.State) : ℝ) ↔ ¬ WordHalts β := by
  rw [compileWithChecker_density U allowed hallowed β]
  exact (forbiddenGraph_density_eq_iff _ _ (Interpreter.input_nonempty β)).trans
    (not_congr (U.correct β))

theorem compileWithChecker_density_strict_iff (U : Interpreter)
    (allowed : BinaryWord → GraphCode → Bool)
    (hallowed : ∀ β g, allowed β g = true ↔ Legal U.machine (Interpreter.input β) (decodeGraph g))
    (β : BinaryWord) :
    (threshold (alphabetSize TapeAlphabet U.State) : ℝ) <
      turanDensity (decodeGraph (compileWithChecker U allowed β)) ↔ WordHalts β := by
  rw [compileWithChecker_density U allowed hallowed β]
  exact (forbiddenGraph_density_strict_iff _ _ (Interpreter.input_nonempty β)).trans (U.correct β)

end TuranUniversality.Effective
