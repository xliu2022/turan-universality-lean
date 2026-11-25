module

public import TuranUniversality.Structural.PhaseApproximation
public import TuranUniversality.Structural.OrdinaryFamily

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The two phase images lie in the actual ordinary extremal space

The map is realized by genuine finite compiled graphs, which are hom-free
for the actual finite family of Section 9. Their ordinary profile limits
therefore satisfy the ordinary forbidden-coordinate and edge-density
conditions. This is the forward inclusion, not yet exhaustion.
-/

open Filter Topology

namespace TuranUniversality.Structural.PhaseRoles

variable {b t : ℕ}

noncomputable def extremalPhaseMap (Ω : Label → Finset (Cube.Word b))
    (phase : Bool) (p q z : ℝ) : SetFamily.Profile 3 → SetFamily.Profile (t + (3 * b + 4)) :=
  phaseMap Ω phase (optimalRoleWeight b t (SwitchScalar.optimalMass (z - p / q)))

theorem continuous_extremalPhaseMap (Ω : Label → Finset (Cube.Word b))
    (phase : Bool) (p q z : ℝ) : Continuous (extremalPhaseMap (t := t) Ω phase p q z) :=
  (continuous_phaseMap Ω phase).comp (continuous_const.prodMk continuous_id)

theorem extremalPhaseMap_mem (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (phase : Bool)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q < familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (W : SetFamily.Profile 3) (hW : W ∈ SetFamily.extremalProfiles F) :
    extremalPhaseMap (t := t) Ω phase p q (familyTuranDensity F) W ∈
      SetFamily.extremalProfiles (Ordinary.forbidden F Ω t) := by
  obtain ⟨G, hpos, hG, hsize, hlim, hedge⟩ := SetFamily.exists_extremal_homFree_sequence F W hW
  let α := SwitchScalar.optimalMass (familyTuranDensity F - p / q)
  have ha : 0 < α := SwitchScalar.optimalMass_pos _ (sub_pos.mpr hz)
  have ha1 : α < 1 := (SwitchScalar.optimalMass_lt_three_quarters _
    (sub_nonneg.mpr hz.le)).trans (by norm_num)
  let O n := PhaseApproximation.object F (G n) (hpos n) (hG n) phase
  let x n := PhaseApproximation.weights b t (G n) α
  have hx n : ProbabilityWeights (x n) :=
    PhaseApproximation.weights_probability (G n) (hpos n) α ha.le ha1.le
  have hprofile : Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (O n).records) (x n))
      atTop (𝓝 (extremalPhaseMap Ω phase p q (familyTuranDensity F) W)) :=
    PhaseApproximation.profile_tendsto F Ω phase G hpos hG hsize α ha ha1 W hlim
  have hfree n : familyHomFree (Ordinary.forbidden F Ω t) (Compiled.graph t Ω (O n).records) :=
    Ordinary.canonical_homFree F Ω _
      (Compiled.canonical (homomorphicClosure F) Ω (O n).records (O n).records_locallyLegal)
  have hlimitfree : extremalPhaseMap (t := t) Ω phase p q (familyTuranDensity F) W ∈
      SetFamily.freeLimitProfiles (Ordinary.forbidden F Ω t : Set _) := by
    apply (SetFamily.isCompact_freeLimitProfiles _).isClosed.mem_of_tendsto hprofile
    apply Eventually.of_forall
    intro n
    refine ⟨SetFamily.isLimitProfile_weighted _ _ (hx n), ?_⟩
    intro A hA
    exact A.2.weightedHomDensity_eq_zero_of_homFree _ (hfree n A hA) _
  refine ⟨hlimitfree, ?_⟩
  have hval : Tendsto (fun n => 6 * (G n).2.edgePolynomial
      (fun _ => ((G n).1 : ℝ)⁻¹)) atTop (𝓝 (familyTuranDensity F)) := by
    simpa only [RGraph.oneEdge_homDensity_polynomial, Fintype.card_fin,
      show (Nat.factorial 3 : ℝ) = 6 by norm_num] using hedge
  have hpval := PhaseApproximation.polynomial_tendsto (t := t) F Ω phase G hpos hG hsize
    p q (familyTuranDensity F) hp hpq hq hz.le hΩ hval
  have heval : Tendsto (fun n => SetFamily.weightedProfile
      (Compiled.graph t Ω (O n).records) (x n) (SetFamily.edgeTest (t + (3 * b + 4)))) atTop
      (𝓝 (familyTuranDensity (Ordinary.forbidden F Ω t))) := by
    rw [Ordinary.density_eq F hedges Ω hdis t p q hp hpq hq hz.le hΩ]
    simpa only [SetFamily.weightedProfile, SetFamily.edgeTest, RGraph.weightedHomDensity_oneEdge] using
      hpval.const_mul ((t + (3 * b + 4)).factorial : ℝ)
  exact tendsto_nhds_unique ((tendsto_pi_nhds.mp hprofile) _) heval

theorem isCompact_phaseImage (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (phase : Bool) (p q : ℝ) :
    IsCompact (extremalPhaseMap (t := t) Ω phase p q (familyTuranDensity F) ''
      SetFamily.extremalProfiles F) :=
  (SetFamily.isCompact_extremalProfiles F).image (continuous_extremalPhaseMap Ω phase p q _)

end TuranUniversality.Structural.PhaseRoles
