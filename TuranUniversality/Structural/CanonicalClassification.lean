module

public import TuranUniversality.Structural.CanonicalProfiles
public import TuranUniversality.Structural.PhaseTopology

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The two exact weighted canonical phase alternatives

The space here is explicitly the closure of actual weighted canonical
hypergraphs. Its comparison with all ordinary forbidden-free extremal
sequences is a separate stability theorem, not an assumption hidden here.
-/

open Filter Topology

namespace TuranUniversality.Structural.CanonicalProfiles

variable {b t : ℕ}

theorem phase_mem (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q < familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (W : SetFamily.Profile 3) (hW : W ∈ SetFamily.extremalProfiles F) :
    PhaseRoles.extremalPhaseMap (t := t) Ω phase p q (familyTuranDensity F) W ∈
      extremal F Ω t p q := by
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
      atTop (𝓝 (PhaseRoles.extremalPhaseMap Ω phase p q (familyTuranDensity F) W)) :=
    PhaseApproximation.profile_tendsto F Ω phase G hpos hG hsize α ha ha1 W hlim
  have hval : Tendsto (fun n => 6 * (G n).2.edgePolynomial
      (fun _ => ((G n).1 : ℝ)⁻¹)) atTop (𝓝 (familyTuranDensity F)) := by
    simpa only [RGraph.oneEdge_homDensity_polynomial, Fintype.card_fin,
      show (Nat.factorial 3 : ℝ) = 6 by norm_num] using hedge
  have hpoly := PhaseApproximation.polynomial_tendsto (t := t) F Ω phase G hpos hG hsize
    p q (familyTuranDensity F) hp hpq hq hz.le hΩ hval
  exact mem_of_compiled_sequence F Ω (fun n => (O n).records) (fun n => (O n).records_locallyLegal)
    x hx p q hpoly _ hprofile

theorem neutral_mem (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : familyTuranDensity F = p / q)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    NeutralRoles.neutralProfile Ω t ∈ extremal F Ω t p q := by
  let O n := RecordApproximation.object F hedges false n
  let x n := Compiled.optimalWeights b t (RecordApproximation.weights F p q n)
  have hx n : ProbabilityWeights (x n) := Compiled.optimalWeights_probability b t _
    (RecordApproximation.weights_probability F p q hz.ge n)
  have hpoly := Compiled.approximation_value_tendsto (t := t) F hedges Ω p q hp hpq hq hz.ge hΩ false
  have hprofile : Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (O n).records) (x n))
      atTop (𝓝 (NeutralRoles.neutralProfile Ω t)) :=
    NeutralRoles.compiled_profile_tendsto_neutral F hedges Ω (fun n => (O n).records)
      (fun n => (O n).records_locallyLegal) p q hp hpq hq hz hΩ x hx atTop hpoly
  exact mem_of_compiled_sequence F Ω (fun n => (O n).records) (fun n => (O n).records_locallyLegal)
    x hx p q hpoly _ hprofile

theorem positive_classification (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q < familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    extremal F Ω t p q =
      (PhaseRoles.extremalPhaseMap (t := t) Ω false p q (familyTuranDensity F) ''
        SetFamily.extremalProfiles F) ∪
      (PhaseRoles.extremalPhaseMap (t := t) Ω true p q (familyTuranDensity F) ''
        SetFamily.extremalProfiles F) := by
  ext W
  constructor
  · intro hW
    obtain ⟨phase, U, hU, rfl⟩ := positive_exhaustion F hedges Ω p q hp hpq hq hz hΩ W hW
    cases phase
    · exact Or.inl ⟨U, hU, rfl⟩
    · exact Or.inr ⟨U, hU, rfl⟩
  · rintro (⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)
    · exact phase_mem F Ω false p q hp hpq hq hz hΩ U hU
    · exact phase_mem F Ω true p q hp hpq hq hz hΩ U hU

theorem zero_classification (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : familyTuranDensity F = p / q)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    extremal F Ω t p q = {NeutralRoles.neutralProfile Ω t} := by
  ext W
  constructor
  · exact zero_exhaustion F hedges Ω p q hp hpq hq hz hΩ W
  · intro hW
    rw [Set.mem_singleton_iff] at hW
    subst W
    exact neutral_mem F hedges Ω p q hp hpq hq hz hΩ

theorem subset_ordinary (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    extremal F Ω t p q ⊆ SetFamily.extremalProfiles (Ordinary.forbidden F Ω t) := by
  intro W hW
  refine ⟨?_, ?_⟩
  · apply closure_minimal (t := SetFamily.freeLimitProfiles (Ordinary.forbidden F Ω t : Set _))
      ?_ (SetFamily.isCompact_freeLimitProfiles _).isClosed hW.1
    rintro Z ⟨G, x, hG, hx, rfl⟩
    refine ⟨SetFamily.isLimitProfile_weighted _ _ hx, ?_⟩
    intro A hA
    exact A.2.weightedHomDensity_eq_zero_of_homFree _
      (Ordinary.canonical_homFree F Ω G.2 hG A hA) x
  · rw [Ordinary.density_eq F hedges Ω hdis t p q hp hpq hq hz hΩ]
    exact hW.2

end TuranUniversality.Structural.CanonicalProfiles
