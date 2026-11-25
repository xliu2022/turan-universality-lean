module

public import TuranUniversality.Structural.NeutralConvergence
public import TuranUniversality.Structural.PhaseImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Realization of the finite neutral profile

The finite role law has probability weights and is the limit of actual
canonical compiled hypergraphs. Its forbidden coordinates and edge density
therefore place it in the actual ordinary extremal space.
-/

open Filter Topology

namespace TuranUniversality.Structural.NeutralRoles

variable {b t : ℕ}

theorem optimalRoleWeight_probability (b t : ℕ) : ProbabilityWeights (optimalRoleWeight b t) := by
  have hx : ProbabilityWeights (fun _ : Unit => (1 : ℝ)) := by constructor <;> simp
  have h := roleWeight_probability (Compiled.optimalWeights b t (fun _ : Unit => (1 : ℝ)))
    (Compiled.optimalWeights_probability b t _ hx)
  have he : roleWeight (Compiled.optimalWeights b t (fun _ : Unit => (1 : ℝ))) =
      optimalRoleWeight b t := by
    funext r
    rcases r with (r | r) | u
    · rfl
    · rfl
    · exact Compiled.optimalWeights_dataMass b t _ hx.2
  rwa [he] at h

theorem neutralProfile_mem (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : familyTuranDensity F = p / q)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    neutralProfile Ω t ∈ SetFamily.extremalProfiles (Ordinary.forbidden F Ω t) := by
  let O n := RecordApproximation.object F hedges false n
  let x n := Compiled.optimalWeights b t (RecordApproximation.weights F p q n)
  have hx n : ProbabilityWeights (x n) := Compiled.optimalWeights_probability b t _
    (RecordApproximation.weights_probability F p q hz.ge n)
  have hpoly := Compiled.approximation_value_tendsto (t := t) F hedges Ω p q hp hpq hq hz.ge hΩ false
  have hprofile : Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (O n).records) (x n))
      atTop (𝓝 (neutralProfile Ω t)) :=
    compiled_profile_tendsto_neutral F hedges Ω (fun n => (O n).records)
      (fun n => (O n).records_locallyLegal) p q hp hpq hq hz hΩ x hx atTop hpoly
  have hfree n : familyHomFree (Ordinary.forbidden F Ω t) (Compiled.graph t Ω (O n).records) :=
    Ordinary.canonical_homFree F Ω _
      (Compiled.canonical (homomorphicClosure F) Ω (O n).records (O n).records_locallyLegal)
  have hlimitfree : neutralProfile Ω t ∈
      SetFamily.freeLimitProfiles (Ordinary.forbidden F Ω t : Set _) := by
    apply (SetFamily.isCompact_freeLimitProfiles _).isClosed.mem_of_tendsto hprofile
    apply Eventually.of_forall
    intro n
    refine ⟨SetFamily.isLimitProfile_weighted _ _ (hx n), ?_⟩
    intro A hA
    exact A.2.weightedHomDensity_eq_zero_of_homFree _ (hfree n A hA) _
  refine ⟨hlimitfree, ?_⟩
  have heval : Tendsto (fun n => SetFamily.weightedProfile
      (Compiled.graph t Ω (O n).records) (x n) (SetFamily.edgeTest (t + (3 * b + 4)))) atTop
      (𝓝 (familyTuranDensity (Ordinary.forbidden F Ω t))) := by
    rw [Ordinary.density_eq F hedges Ω hdis t p q hp hpq hq hz.ge hΩ]
    simpa only [SetFamily.weightedProfile, SetFamily.edgeTest, RGraph.weightedHomDensity_oneEdge] using
      hpoly.const_mul ((t + (3 * b + 4)).factorial : ℝ)
  exact tendsto_nhds_unique ((tendsto_pi_nhds.mp hprofile) _) heval

end TuranUniversality.Structural.NeutralRoles
