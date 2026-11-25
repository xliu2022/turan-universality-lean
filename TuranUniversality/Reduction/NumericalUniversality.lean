module

public import TuranUniversality.Effective.UniformCompiler
public import TuranUniversality.Effective.UniformTemplate
public import TuranUniversality.Uniformity.NumericalCore
public import TuranUniversality.RegistryNumericalStatement

@[expose] public section

/-! # Complete effective numerical universality in every uniformity

Both effective witnesses are actual finite-code functions with joint
primitive-recursion proofs. The decoded family is the bounded obstruction
and full extension family used by the ordinary-density proof.
-/

namespace TuranUniversality

open TuranUniversality.Computation TuranUniversality.Effective TuranUniversality.Uniformity
open Filter Topology

set_option maxRecDepth 8000

attribute [local irreducible] forbiddenCompiler Uniformity.baselineThree
  Effective.Uniform.compiler Effective.Uniform.templateCode

namespace Effective.Uniform

theorem compiler_decode_numerical (r : ℕ) (hr : 3 ≤ r) (w : BinaryWord) :
    decodeFamily r (compiler r w) = numericalFamily r w := by
  by_cases h : r = 3
  · subst r
    rw [numericalFamily_three]
    exact compiler_decode_three w
  · rw [numericalFamily_of_ne_three r w h]
    exact compiler_decode_other r hr h w

/-- The coded fixed template is globally optimal over all real probability
weightings. A single nonhalting input supplies the sharp density upper bound. -/
theorem templateCode_weighted_bound (r : ℕ) (hr : 3 ≤ r)
    (x : Fin (templateCode r).1 → ℝ) (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * (decode r (templateCode r)).edgePolynomial x ≤
      (thresholdR r : ℝ) := by
  have h := familyTuranDensity_lower_of_homFree
    (decodeFamily r (compiler r [false])) (decode r (templateCode r))
    (templateCode_familyHomFree r hr [false]) x hx
  rw [compiler_decode_numerical r hr [false],
    (numericalFamily_density_eq_iff r hr [false]).mpr zeroWord_not_halting] at h
  exact h

theorem templateCode_uniform_optimal (r : ℕ) (hr : 3 ≤ r)
    (x : Fin (templateCode r).1 → ℝ) (hx : ProbabilityWeights x) :
    (decode r (templateCode r)).edgePolynomial x ≤
      (decode r (templateCode r)).edgePolynomial
        (fun _ => ((templateCode r).1 : ℝ)⁻¹) := by
  have h := templateCode_weighted_bound r hr x hx
  rw [← templateCode_uniform_value r hr] at h
  have hp : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  exact (mul_le_mul_iff_right₀ hp).mp h

end Effective.Uniform

/-- The complete unconditional statement corresponding to V4 Theorem 1.2.
The endpoint is the original singleton compiler; for all higher ranks the
exact ordinary-density formula, a fixed uniformly optimal template and
primitive-recursive family and template compilers hold simultaneously. -/
theorem numerical_universality : Registry.numericalStatement := by
  refine ⟨tau3, tau3_bounds.1, tau3_bounds.2, tau3_baseline_formula,
    forbiddenCompiler, forbiddenCompiler_primrec,
    (fun p => Uniform.compiler p.1 p.2), Uniform.compiler_primrec,
    Uniform.templateCode, Uniform.templateCode_primrec, ?_, ?_⟩
  · intro w
    exact Uniform.compiler_decode_three w
  intro r hr
  dsimp only
  refine ⟨(thresholdR_bounds hr).1, (thresholdR_bounds hr).2,
    Uniform.templateCode_order_pos r, Uniform.templateCode_uniform_value r hr,
    Uniform.templateCode_weighted_bound r hr, ?_⟩
  intro w
  rw [Uniform.compiler_decode_numerical r hr w]
  refine ⟨?_, numericalFamily_density_limit r w,
    numericalFamily_density_scaling r hr w,
    numericalFamily_density_eq_iff r hr w,
    numericalFamily_density_strict_iff r hr w, ?_, ?_⟩
  · intro A hA
    exact Finset.card_pos.mpr (numericalFamily_has_edges r w hA)
  · have h := Uniform.templateCode_familyHomFree r hr w
    change familyHomFree (Uniform.decodeFamily r (Uniform.compiler r w)) _ at h
    rwa [Uniform.compiler_decode_numerical r hr w] at h
  · intro sizes
    have h := Uniform.templateCode_blowup_free r hr w sizes
    change familyFree (Uniform.decodeFamily r (Uniform.compiler r w)) _ at h
    rwa [Uniform.compiler_decode_numerical r hr w] at h

end TuranUniversality
