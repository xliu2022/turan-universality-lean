module

public import TuranUniversality.Structural.NeutralImage
public import TuranUniversality.Structural.PhaseReadback

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A universal finite approximation of the neutral role profile -/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.NeutralRoles

variable {b t : ℕ}

theorem roleWeight_optimalWeights {V : Type*} [DecidableEq V] [Fintype V]
    (x : V → ℝ) (hx : ∑ v, x v = 1) :
    roleWeight (Compiled.optimalWeights b t x) = optimalRoleWeight b t := by
  funext r
  rcases r with (j | v) | a
  · rfl
  · rfl
  · exact Compiled.optimalWeights_dataMass b t x hx

noncomputable def approximationWeights (b t n : ℕ) : Compiled.Vertex b t (Fin (n + 3)) → ℝ :=
  Compiled.optimalWeights b t (fun _ => ((n + 3 : ℕ) : ℝ)⁻¹)

theorem approximationWeights_probability (b t n : ℕ) :
    ProbabilityWeights (approximationWeights b t n) :=
  Compiled.optimalWeights_probability b t _ (RecordApproximation.uniform_probability n)

theorem approximation_tendsto (B : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ B, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b)) (t : ℕ) :
    Tendsto (fun n => SetFamily.weightedProfile
      (Compiled.graph t Ω (object B hedges : LegalObject B (Fin (n + 3))).records)
      (approximationWeights b t n)) atTop (𝓝 (neutralProfile Ω t)) := by
  have hT n : 0 < Compiled.dataMass (approximationWeights b t n) := by
    rw [approximationWeights, Compiled.optimalWeights_dataMass b t _
      (RecordApproximation.uniform_probability n).2]
    exact div_pos (by norm_num) (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  have hrole n : roleWeight (approximationWeights b t n) = optimalRoleWeight b t :=
    roleWeight_optimalWeights _ (RecordApproximation.uniform_probability n).2
  have hs n : (∑ v, (Compiled.normalizedData (approximationWeights b t n) v) ^ 2) =
      ((n + 3 : ℕ) : ℝ)⁻¹ := by
    rw [approximationWeights, Compiled.normalizedData_optimalWeights b t _
      (RecordApproximation.uniform_probability n).2]
    exact RecordApproximation.uniform_squares (n + 3)
  exact profile_tendsto hedges Ω (approximationWeights b t) (approximationWeights_probability b t)
    atTop (optimalRoleWeight b t) (Eventually.of_forall hT)
    (by simpa only [hrole] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => optimalRoleWeight b t) atTop (𝓝 (optimalRoleWeight b t))))
    (by simpa only [hs] using RecordApproximation.inverse_order_tendsto)

theorem neutralProfile_readback_zero (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (phase : Bool) (A : FiniteGraph 3) (hA : A.2.edges.Nonempty) (hno : Uniformity.NoIsolates A.2) :
    neutralProfile (CodePools.pool p q hpq) t (PhaseRoles.readbackTest p q hpq hq t phase A) = 0 := by
  let O n := (object ∅ (by simp) : LegalObject ∅ (Fin (n + 3)))
  let x n := approximationWeights (CodePools.blockCount q) t n
  have hlim := approximation_tendsto ∅ (by simp) (CodePools.pool p q hpq) t
  have hzero n : SetFamily.weightedProfile (Compiled.graph t (CodePools.pool p q hpq) (O n).records)
      (x n) (PhaseRoles.readbackTest p q hpq hq t phase A) = 0 := by
    change (FiniteGraph.ofRGraph _).2.weightedHomDensity _ _ = _
    rw [RGraph.weightedHomDensity_source_ofRGraph _ _ _ (approximationWeights_probability _ _ n).2]
    rw [Readback.weighted_readback_raw p q hpq hq t A.2 hno (O n) phase
      (PhaseRoles.testSupport p q hpq hq phase) (PhaseRoles.testSupport_mem p q hpq hq phase)]
    have hempty : A.2.weightedHomDensity ((O n).inner phase)
        (fun v => x n (Readback.dataVertex v)) = 0 := by
      apply A.2.weightedHomDensity_eq_zero_of_homFree
      rintro ⟨f, hf⟩
      obtain ⟨e, he⟩ := hA
      have h := hf e he
      simpa [O, object, LegalObject.empty, RGraph.empty] using h
    rw [hempty, mul_zero]
  have ht := (tendsto_pi_nhds.mp hlim) (PhaseRoles.readbackTest p q hpq hq t phase A)
  have ht0 : Tendsto (fun n => SetFamily.weightedProfile
      (Compiled.graph t (CodePools.pool p q hpq) (O n).records) (x n)
      (PhaseRoles.readbackTest p q hpq hq t phase A)) atTop (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht ht0

end TuranUniversality.Structural.NeutralRoles
