module

public import TuranUniversality.Structural.PhaseReadbackWeights
public import TuranUniversality.Structural.ProfileSupport

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact readback coordinates of both continuous phase maps

The coordinate identity is obtained as a limit of the verified finite
ordinary readback tests. A test in the opposite phase has coordinate zero.
No graphon representation or additional readback axiom is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.PhaseRoles

theorem poolGraph_phase_nonempty (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (phase : Bool) :
    (Support.poolGraph (CodePools.pool p q hpq (.inr phase))).edges.Nonempty := by
  obtain ⟨w, hw⟩ := CodePools.pool_nonempty p q hpq hq (.inr phase)
  obtain ⟨e, he⟩ := TripleClasses.wordGraph_nonempty w
  exact ⟨e, Finset.mem_biUnion.mpr ⟨w, hw, he⟩⟩

noncomputable def testSupport (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (phase : Bool) :
    Finset (Support.Vertex (CodePools.blockCount q)) :=
  (poolGraph_phase_nonempty p q hpq hq phase).choose

theorem testSupport_mem (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (phase : Bool) :
    testSupport p q hpq hq phase ∈ (Support.poolGraph (CodePools.pool p q hpq (.inr phase))).edges :=
  (poolGraph_phase_nonempty p q hpq hq phase).choose_spec

noncomputable def readbackTest (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (phase : Bool) (A : FiniteGraph 3) : FiniteGraph (t + (3 * CodePools.blockCount q + 4)) :=
  FiniteGraph.ofRGraph (Readback.test t (CodePools.pool p q hpq CodePools.neutralLabel)
    (testSupport p q hpq hq phase)
    ((Support.poolGraph _).uniform _ (testSupport_mem p q hpq hq phase)) A.2)

noncomputable def readbackFactor (q t : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  (2 * 10 ^ CodePools.blockCount q * t.factorial : ℕ) * rootMassProduct (CodePools.blockCount q) t *
    ((4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ)) * (1 - α)) ^ 5 *
      ((4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ)) * α) ^ n

theorem readbackFactor_pos (q t : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (n : ℕ) :
    0 < readbackFactor q t α n := by
  have hr : 0 < (OuterWeights.arity (CodePools.blockCount q) t : ℝ) :=
    Nat.cast_pos.mpr (OuterWeights.arity_pos _ _)
  have hroot := rootMassProduct_pos (CodePools.blockCount q) t
  have hn : 0 < 1 - α := sub_pos.mpr hα1
  have hfac := Nat.factorial_pos t
  unfold readbackFactor
  positivity

theorem innerProfile_eq_zero_of_empty {V : Type*} [DecidableEq V] [Fintype V]
    {B : Finset (FiniteGraph 3)} {b t : ℕ} (O : LegalObject B V) (phase : Bool)
    (he : (O.inner phase).edges = ∅) (x : Compiled.Vertex b t V → ℝ)
    (A : FiniteGraph 3) (hA : A.2.edges.Nonempty) : innerProfile O phase x A = 0 := by
  apply A.2.weightedHomDensity_eq_zero_of_homFree
  rintro ⟨f, hf⟩
  obtain ⟨e, heA⟩ := hA
  have h := ((O.inner phase).mem_pullback _ _).mp (hf e heA)
  simpa [he] using h.2

/-- The same fixed finite test reads its own phase and vanishes on the
opposite phase, with the exact positive factor from the finite formulas. -/
theorem phaseMap_readback (B : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (phase query : Bool) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (W : SetFamily.Profile 3) (hW : W ∈ SetFamily.freeLimitProfiles (B : Set _))
    (A : FiniteGraph 3) (hA : A.2.edges.Nonempty) (hno : Uniformity.NoIsolates A.2) :
    phaseMap (CodePools.pool p q hpq) phase (optimalRoleWeight (CodePools.blockCount q) t α) W
      (readbackTest p q hpq hq t query A) =
        readbackFactor q t α A.1 * (if query = phase then W A else 0) := by
  obtain ⟨G, hpos, hG, hsize, hlim⟩ := SetFamily.exists_positive_homFree_sequence B W hW
  let O n := PhaseApproximation.object B (G n) (hpos n) (hG n) phase
  let x n := PhaseApproximation.weights (CodePools.blockCount q) t (G n) α
  have hx n : ProbabilityWeights (x n) :=
    PhaseApproximation.weights_probability (G n) (hpos n) α hα.le hα1.le
  have hprofile := PhaseApproximation.profile_tendsto (t := t) B
    (CodePools.pool p q hpq) phase G hpos hG hsize α hα hα1 W hlim
  have hroot : Tendsto (fun n => Readback.rootProduct (x n)) atTop
      (𝓝 (rootMassProduct (CodePools.blockCount q) t)) := by
    simpa only [x, PhaseApproximation.weights, rootProduct_optimalWeights] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => rootMassProduct (CodePools.blockCount q) t)
        atTop (𝓝 _))
  have hneutral : Tendsto (fun n => (O n).neutralMass (Compiled.dataWeight (x n))) atTop
      (𝓝 ((4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ)) * (1 - α))) := by
    simpa only [O, x, object_neutralMass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ)) * (1 - α)) atTop (𝓝 _))
  have hactive : Tendsto (fun n => (O n).activeMass (Compiled.dataWeight (x n))) atTop
      (𝓝 ((4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ)) * α)) := by
    simpa only [O, x, object_activeMass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ)) * α) atTop (𝓝 _))
  have hsquares : Tendsto (fun n => ∑ v, (Compiled.dataWeight (x n) v) ^ 2) atTop (𝓝 0) :=
    PhaseApproximation.weights_data_squares_tendsto G hsize α hα.le hα1.le
  have hinner : Tendsto (fun n => innerProfile (O n) query (x n) A) atTop
      (𝓝 (if query = phase then W A else 0)) := by
    by_cases hs : query = phase
    · subst query
      simpa only [O, x, PhaseApproximation.object_innerProfile _ _ _ _ _ _ (ne_of_gt hα),
        ite_true] using (tendsto_pi_nhds.mp hlim) A
    · have hn (n : ℕ) : innerProfile (O n) query (x n) A = 0 :=
        innerProfile_eq_zero_of_empty (O n) query
          (PhaseApproximation.object_other_phase B (G n) (hpos n) (hG n) phase query hs) (x n) A hA
      simpa only [hn, hs, ite_false] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hread := Readback.weighted_readback_tendsto p q hpq hq t A.2 hA hno O query
    (testSupport p q hpq hq query) (testSupport_mem p q hpq hq query) x hx atTop
    _ _ _ _ hroot hneutral hsquares hactive
    (by simpa only [innerProfile_eq_readback] using hinner)
  have hfinite : Tendsto (fun n => SetFamily.weightedProfile
      (Compiled.graph t (CodePools.pool p q hpq) (O n).records) (x n)
      (readbackTest p q hpq hq t query A)) atTop
      (𝓝 (readbackFactor q t α A.1 * (if query = phase then W A else 0))) := by
    have h := hread.congr' (Eventually.of_forall (fun n =>
      (RGraph.weightedHomDensity_source_ofRGraph _ _ (x n) (hx n).2).symm))
    simpa only [RootActions.group_card p q hpq hq t, Fintype.card_fin,
      readbackFactor, readbackTest, SetFamily.weightedProfile] using h
  exact tendsto_nhds_unique ((tendsto_pi_nhds.mp hprofile) _) hfinite

end TuranUniversality.Structural.PhaseRoles
