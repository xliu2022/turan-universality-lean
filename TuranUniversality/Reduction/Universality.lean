module

public import TuranUniversality.Effective.AllowedChecker
public import TuranUniversality.Effective.CompilerAssembly
public import TuranUniversality.RegistryStatement

@[expose] public section

/-! # The complete primitive-recursive singleton universality theorem -/

namespace TuranUniversality

set_option maxRecDepth 8000

open Construction Reduction Effective TuranUniversality.Computation
open Filter Topology

/-- One fixed rational number, independent of the binary input. -/
noncomputable def tau3 : ℚ :=
  threshold (alphabetSize TapeAlphabet universalInterpreter.State)

/-- A total graph-code function with a proved primitive-recursion certificate.
All legality decisions in the finite enumeration are verified against the
actual rooted model, and the output is a single ordinary finite three-graph. -/
noncomputable def forbiddenCompiler : BinaryWord → GraphCode :=
  compileWithChecker universalInterpreter (allowedCheck universalInterpreter)

theorem tau3_bounds : 0 < tau3 ∧ tau3 < 1 := threshold_bounds _

/-- The exported threshold is the manuscript's explicit rational expression
`6 B(t₀)`, with an admissible fixed physical-type count. -/
theorem tau3_baseline_formula : ∃ m : ℕ,
    30 ≤ m ∧ m % 4 = 2 ∧ tau3 = Weighted.rationalThreshold (m : ℚ) := by
  refine ⟨physicalCount (chosenParameter (alphabetSize TapeAlphabet universalInterpreter.State)),
    physicalCount_ge _, ?_, rfl⟩
  unfold physicalCount
  omega

theorem tau3_eq_six_baseline : (tau3 : ℝ) =
    6 * Weighted.baselineMax
      (physicalCount (chosenParameter (alphabetSize TapeAlphabet universalInterpreter.State)))
      (rootNumber (chosenParameter (alphabetSize TapeAlphabet universalInterpreter.State))) :=
  threshold_cast _

theorem forbiddenCompiler_primrec : Primrec forbiddenCompiler :=
  compileWithChecker_primrec _ _ (allowedCheck_primrec universalInterpreter)

theorem forbiddenCompiler_has_edges (w : BinaryWord) :
    (decodeGraph (forbiddenCompiler w)).edges.Nonempty :=
  compileWithChecker_has_edges _ _ (allowedCheck_correct universalInterpreter) w

theorem forbiddenCompiler_density_eq_iff (w : BinaryWord) :
    turanDensity (decodeGraph (forbiddenCompiler w)) = (tau3 : ℝ) ↔ ¬ WordHalts w :=
  compileWithChecker_density_eq_iff _ _ (allowedCheck_correct universalInterpreter) w

theorem forbiddenCompiler_density_strict_iff (w : BinaryWord) :
    (tau3 : ℝ) < turanDensity (decodeGraph (forbiddenCompiler w)) ↔ WordHalts w :=
  compileWithChecker_density_strict_iff _ _ (allowedCheck_correct universalInterpreter) w

/-- The ordinary normalized extremal numbers really converge to the density
used in the dichotomy. This rules out replacing ordinary Turán density by a
weighted proxy in the exported theorem statement. -/
theorem forbiddenCompiler_density_limit (w : BinaryWord) :
    Tendsto (extremalDensity (decodeGraph (forbiddenCompiler w))) atTop
      (𝓝 (turanDensity (decodeGraph (forbiddenCompiler w)))) :=
  extremalDensity_tendsto _ (Finset.card_pos.mpr (forbiddenCompiler_has_edges w))

theorem singleton_universality : Registry.mainStatement := by
  refine ⟨tau3, tau3_bounds.1, tau3_bounds.2, tau3_baseline_formula, forbiddenCompiler,
    forbiddenCompiler_primrec, ?_⟩
  intro w
  exact ⟨Finset.card_pos.mpr (forbiddenCompiler_has_edges w), forbiddenCompiler_density_limit w,
    forbiddenCompiler_density_eq_iff w, forbiddenCompiler_density_strict_iff w⟩

end TuranUniversality
