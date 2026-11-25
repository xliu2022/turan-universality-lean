module

public import TuranUniversality.Reduction.Universality
public import TuranUniversality.Density.FamilyLower

@[expose] public section

/-! # The fixed three-uniform template, free for every input -/

open scoped BigOperators

namespace TuranUniversality.Uniformity

open TuranUniversality.Computation Reduction Construction Effective Weighted

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

abbrev BaselineVertex (U : Interpreter) := ConcreteWitness.Roots (Γ := TapeAlphabet) (Λ := U.State) ⊕
  (ConcreteWitness.Kinds (Γ := TapeAlphabet) (Λ := U.State) × Unit)

def baselineBase (U : Interpreter) : RGraph (BaselineVertex U) 3 :=
  (ConcreteWitness.baselineCompletion (Γ := TapeAlphabet) (Λ := U.State)).model.toRGraph

def baselineClones (U : Interpreter) : BaselineVertex U → ℕ := ConcreteWitness.baselineSizes

def baselineTemplate (U : Interpreter) : FiniteGraph 3 :=
  FiniteGraph.ofRGraph ((baselineBase U).blowup (baselineClones U))

theorem baselineTemplate_order_pos (U : Interpreter) : 0 < (baselineTemplate U).1 := by
  change 0 < Fintype.card (RGraph.BlowupVertex (baselineClones U))
  rw [RGraph.blowup_vertex_card]
  exact ConcreteWitness.baselineSizes_pos

theorem baselineBase_homFree (U : Interpreter) (w : BinaryWord) :
    (decodeGraph (compileWithChecker U (allowedCheck U) w)).HomFree (baselineBase U) := by
  have hfree := singletonProduct_target_exclusion U.machine (Interpreter.input w)
    (forbiddenCores U.machine (Interpreter.input w))
    (forbiddenCores_nonempty _ _)
    (fun _ hA => forbiddenCores_illegal _ _ hA)
    (fun _ hA => forbiddenCores_contain_guard _ _ hA)
    (ConcreteWitness.baselineCompletion (Γ := TapeAlphabet) (Λ := U.State)).model
    (ConcreteWitness.baselineCompletion_legal U.machine (Interpreter.input w))
    ConcreteWitness.baselineCompletion_declared
  obtain ⟨f, hf⟩ := (singletonCode_mutual_hom
    (coreCodes U (allowedCheck U) w) (forbiddenCores U.machine (Interpreter.input w))
    (coreCodes_decode U (allowedCheck U) (allowedCheck_correct U) w)
    (forbiddenCores_nonempty _ _)).2
  exact hfree.of_hom hf

theorem baselineTemplate_homFree (U : Interpreter) (w : BinaryWord) :
    (decodeGraph (compileWithChecker U (allowedCheck U) w)).HomFree (baselineTemplate U).2 := by
  have h := (decodeGraph (compileWithChecker U (allowedCheck U) w)).blowup_homFree (baselineBase U)
    (baselineBase_homFree U w) (baselineClones U)
  rintro ⟨f, hf⟩
  exact h ⟨_, (FiniteGraph.ofRGraph_embedding ((baselineBase U).blowup (baselineClones U))).isHom.comp hf⟩

theorem baselineTemplate_uniform_value (U : Interpreter) :
    6 * (baselineTemplate U).2.edgePolynomial (fun _ => ((baselineTemplate U).1 : ℝ)⁻¹) =
      (threshold (alphabetSize TapeAlphabet U.State) : ℝ) := by
  let G := (baselineBase U).blowup (baselineClones U)
  change 6 * (G.pullback (Fintype.equivFin (RGraph.BlowupVertex (baselineClones U))).symm.toEmbedding).edgePolynomial
    ((fun _ => (Fintype.card (RGraph.BlowupVertex (baselineClones U)) : ℝ)⁻¹) ∘
      (Fintype.equivFin (RGraph.BlowupVertex (baselineClones U))).symm) = _
  rw [G.pullback_equiv_polynomial]
  change 6 * ((baselineBase U).blowup (baselineClones U)).edgePolynomial _ = _
  rw [(baselineBase U).blowup_polynomial]
  exact ConcreteWitness.baselineCompletion_value

def baselineThree : FiniteGraph 3 := baselineTemplate universalInterpreter

theorem baselineThree_order_pos : 0 < baselineThree.1 :=
  baselineTemplate_order_pos _

theorem baselineThree_homFree (w : BinaryWord) :
    (decodeGraph (forbiddenCompiler w)).HomFree baselineThree.2 :=
  baselineTemplate_homFree _ w

theorem baselineThree_uniform_value :
    6 * baselineThree.2.edgePolynomial (fun _ => (baselineThree.1 : ℝ)⁻¹) = (tau3 : ℝ) :=
  baselineTemplate_uniform_value _

theorem baselineThree_weighted_bound (x : Fin baselineThree.1 → ℝ) (hx : ProbabilityWeights x) :
    6 * baselineThree.2.edgePolynomial x ≤ (tau3 : ℝ) := by
  have h := turanDensity_lower_weighted_of_homFree
    (decodeGraph (forbiddenCompiler [false])) baselineThree.2 (baselineThree_homFree [false]) x hx
  rw [(forbiddenCompiler_density_eq_iff [false]).mpr zeroWord_not_halting] at h
  simpa only [show Nat.factorial 3 = 6 from rfl, Nat.cast_ofNat] using h

theorem baselineThree_uniform_optimal (x : Fin baselineThree.1 → ℝ) (hx : ProbabilityWeights x) :
    baselineThree.2.edgePolynomial x ≤
      baselineThree.2.edgePolynomial (fun _ => (baselineThree.1 : ℝ)⁻¹) := by
  have h := baselineThree_weighted_bound x hx
  have he := baselineThree_uniform_value
  linarith

theorem baselineThree_blowup_free (w : BinaryWord) (sizes : Fin baselineThree.1 → ℕ) :
    ¬ ∃ f, (decodeGraph (forbiddenCompiler w)).IsEmbedding (baselineThree.2.blowup sizes) f :=
  (decodeGraph (forbiddenCompiler w)).blowup_free _ (baselineThree_homFree w) sizes

end
end TuranUniversality.Uniformity
