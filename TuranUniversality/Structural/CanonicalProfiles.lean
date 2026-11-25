module

public import TuranUniversality.Structural.PhaseExhaustion
public import TuranUniversality.Structural.NeutralImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Complete weighted profile classification for actual canonical graphs

Canonical completion is performed on the original carrier. Its polynomial
excess and every homomorphism-density excess tend to zero. The quotient
profile is exactly an actual compiled profile, so the two-phase and neutral
classification applies without identifying support compression with edit
stability of arbitrary ordinary forbidden-free graphs.
-/

open Filter Topology

namespace TuranUniversality.Structural.CanonicalProfiles

open Density

variable {b t : ℕ}

def graphClass (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b)) (t : ℕ) :
    FiniteGraph (t + (3 * b + 4)) → Prop := fun G => Canonical (homomorphicClosure F) Ω G.2

def extremal (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (p q : ℝ) : Set (SetFamily.Profile (t + (3 * b + 4))) :=
  SetFamily.weightedExtremalProfiles (graphClass F Ω t)
    (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))

theorem weightedProfile_mem {V : Type*} [DecidableEq V] [Fintype V]
    (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) (hG : Canonical (homomorphicClosure F) Ω G)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    SetFamily.weightedProfile G x ∈ SetFamily.weightedClassProfiles (graphClass F Ω t) := by
  let e := (Fintype.equivFin V).symm
  refine ⟨FiniteGraph.ofRGraph G, x ∘ e,
    Canonical.of_embedding F Ω (FiniteGraph.ofRGraph_embedding G) hG,
    probabilityWeights_equiv e x hx, ?_⟩
  funext A
  exact (A.2.weightedHomDensity_pullback_equiv G e x).symm

theorem completion_sequence {I : Type*} {X : I → Type*}
    [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)] (l : Filter I)
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b))
    (G : ∀ i, RGraph (X i) (t + (3 * b + 4)))
    (hG : ∀ i, Canonical (homomorphicClosure F) Ω (G i))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : ∀ i, X i → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (hpoly : Tendsto (fun i => (G i).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))))
    (W : SetFamily.Profile (t + (3 * b + 4)))
    (hW : Tendsto (fun i => SetFamily.weightedProfile (G i) (x i)) l (𝓝 W)) :
    ∃ (R : ∀ i, RecordSystem (X i)) (y : ∀ i, Compiled.Vertex b t (X i) → ℝ),
      (∀ i, (R i).LocallyLegal (homomorphicClosure F)) ∧
      (∀ i, ProbabilityWeights (y i)) ∧
      Tendsto (fun i => (Compiled.graph t Ω (R i)).edgePolynomial (y i)) l
        (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) ∧
      Tendsto (fun i => SetFamily.weightedProfile (Compiled.graph t Ω (R i)) (y i)) l (𝓝 W) := by
  classical
  choose ρ R H hR hsub hvalue hhom using
    (fun i => Canonical.completion (homomorphicClosure F) Ω (G i) (hG i) (x i))
  let y i := pushforwardWeight (Rooted.place (ρ i)) (x i)
  have hy i : ProbabilityWeights (y i) := pushforwardWeight_probability _ _ (hx i)
  let Λ := OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)
  have hub i : (H i).edgePolynomial (x i) ≤ Λ := by
    rw [hvalue i]
    exact Compiled.polynomial_upper F hedges Ω (R i) (hR i) p q hp hpq hq hz hΩ (y i) (hy i)
  have hHp : Tendsto (fun i => (H i).edgePolynomial (x i)) l (𝓝 Λ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hpoly tendsto_const_nhds
      (fun i => (G i).edgePolynomial_mono (H i) (hsub i) (hx i).1) hub
  refine ⟨R, y, hR, hy, ?_, ?_⟩
  · simpa only [hvalue] using hHp
  · apply tendsto_pi_nhds.mpr
    intro A
    have hd := A.2.weightedHomDensity_sub_tendsto_zero_of_completion G H hsub x hx l Λ hub hpoly
    have h := hd.add ((tendsto_pi_nhds.mp hW) A)
    simpa only [SetFamily.weightedProfile, sub_add_cancel, zero_add, hhom] using h

theorem exists_compiled_sequence (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (W : SetFamily.Profile (t + (3 * b + 4))) (hW : W ∈ extremal F Ω t p q) :
    ∃ (N : ℕ → ℕ) (R : ∀ n, RecordSystem (Fin (N n)))
      (y : ∀ n, Compiled.Vertex b t (Fin (N n)) → ℝ),
      (∀ n, (R n).LocallyLegal (homomorphicClosure F)) ∧
      (∀ n, ProbabilityWeights (y n)) ∧
      Tendsto (fun n => (Compiled.graph t Ω (R n)).edgePolynomial (y n)) atTop
        (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) ∧
      Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (R n)) (y n)) atTop (𝓝 W) := by
  obtain ⟨G, x, hG, hx, hlim⟩ := SetFamily.exists_weighted_sequence _ W hW.1
  have he := (tendsto_pi_nhds.mp hlim) (SetFamily.edgeTest (t + (3 * b + 4)))
  rw [hW.2] at he
  have hk : (((t + (3 * b + 4)).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpoly : Tendsto (fun n => (G n).2.edgePolynomial (x n)) atTop
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) := by
    simpa only [SetFamily.weightedProfile, SetFamily.edgeTest, RGraph.weightedHomDensity_oneEdge,
      mul_div_cancel_left₀ _ hk] using he.div_const (((t + (3 * b + 4)).factorial : ℕ) : ℝ)
  obtain ⟨R, y, hR, hy, hpval, hprof⟩ := completion_sequence atTop F hedges Ω
    (fun n => (G n).2) hG p q hp hpq hq hz hΩ x hx hpoly W hlim
  exact ⟨fun n => (G n).1, R, y, hR, hy, hpval, hprof⟩

theorem positive_exhaustion (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q < familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (W : SetFamily.Profile (t + (3 * b + 4))) (hW : W ∈ extremal F Ω t p q) :
    ∃ (phase : Bool) (U : SetFamily.Profile 3), U ∈ SetFamily.extremalProfiles F ∧
      W = PhaseRoles.extremalPhaseMap Ω phase p q (familyTuranDensity F) U := by
  obtain ⟨N, R, y, hR, hy, hpoly, hlim⟩ :=
    exists_compiled_sequence F hedges Ω p q hp hpq hq hz.le hΩ W hW
  exact PhaseRoles.compiled_limit_is_phase F hedges Ω R hR p q hp hpq hq hz hΩ y hy hpoly W hlim

theorem zero_exhaustion (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : familyTuranDensity F = p / q)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (W : SetFamily.Profile (t + (3 * b + 4))) (hW : W ∈ extremal F Ω t p q) :
    W = NeutralRoles.neutralProfile Ω t := by
  obtain ⟨N, R, y, hR, hy, hpoly, hlim⟩ :=
    exists_compiled_sequence F hedges Ω p q hp hpq hq hz.ge hΩ W hW
  have hzero := NeutralRoles.compiled_profile_tendsto_neutral F hedges Ω R hR
    p q hp hpq hq hz hΩ y hy atTop hpoly
  exact tendsto_nhds_unique hlim hzero

/-- Any realized near-optimal compiled sequence determines an actual weighted
canonical extremal point. -/
theorem mem_of_compiled_sequence {X : ℕ → Type*}
    [∀ n, DecidableEq (X n)] [∀ n, Fintype (X n)]
    (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (R : ∀ n, RecordSystem (X n)) (hR : ∀ n, (R n).LocallyLegal (homomorphicClosure F))
    (x : ∀ n, Compiled.Vertex b t (X n) → ℝ) (hx : ∀ n, ProbabilityWeights (x n))
    (p q : ℝ)
    (hpoly : Tendsto (fun n => (Compiled.graph t Ω (R n)).edgePolynomial (x n)) atTop
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))))
    (W : SetFamily.Profile (t + (3 * b + 4)))
    (hW : Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (R n)) (x n)) atTop (𝓝 W)) :
    W ∈ extremal F Ω t p q := by
  refine ⟨?_, ?_⟩
  · apply isClosed_closure.mem_of_tendsto hW
    apply Eventually.of_forall
    intro n
    exact subset_closure (weightedProfile_mem F Ω _
      (Compiled.canonical (homomorphicClosure F) Ω (R n) (hR n)) (x n) (hx n))
  · have he : Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (R n)) (x n)
        (SetFamily.edgeTest (t + (3 * b + 4)))) atTop
        (𝓝 (((t + (3 * b + 4)).factorial : ℝ) *
          (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)))) := by
      simpa only [SetFamily.weightedProfile, SetFamily.edgeTest, RGraph.weightedHomDensity_oneEdge] using
        hpoly.const_mul (((t + (3 * b + 4)).factorial : ℕ) : ℝ)
    exact tendsto_nhds_unique ((tendsto_pi_nhds.mp hW) _) he

end TuranUniversality.Structural.CanonicalProfiles
