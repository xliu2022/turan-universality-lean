module

public import TuranUniversality.Structural.NeutralApproximation
public import TuranUniversality.Structural.CanonicalTopology

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Two fixed ordinary tests and their exact separator values -/

namespace TuranUniversality.Structural.Separation

noncomputable def test (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (phase : Bool) :
    FiniteGraph (t + (3 * CodePools.blockCount q + 4)) :=
  PhaseRoles.readbackTest p q hpq hq t phase (SetFamily.edgeTest 3)

noncomputable def separator (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (W : SetFamily.Profile (t + (3 * CodePools.blockCount q + 4))) : ℝ :=
  W (test p q hpq hq t false) - W (test p q hpq hq t true)

theorem continuous_separator (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    Continuous (separator p q hpq hq t) :=
  (continuous_apply _).sub (continuous_apply _)

noncomputable def value (p q t : ℕ) (z : ℝ) : ℝ :=
  PhaseRoles.readbackFactor q t (SwitchScalar.optimalMass (z - (p : ℝ) / q)) 3 * z

theorem value_pos (p q : ℕ) (t : ℕ) (z : ℝ) (hz : (p : ℝ) / q < z) : 0 < value p q t z := by
  have hd : 0 < z - (p : ℝ) / q := sub_pos.mpr hz
  have ha := SwitchScalar.optimalMass_pos _ hd
  have ha1 : SwitchScalar.optimalMass (z - (p : ℝ) / q) < 1 :=
    (SwitchScalar.optimalMass_lt_three_quarters _ hd.le).trans (by norm_num)
  exact mul_pos (PhaseRoles.readbackFactor_pos q t _ ha ha1 3)
    ((div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans_lt hz)

theorem phase_coordinate (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) (phase query : Bool)
    (W : SetFamily.Profile 3) (hW : W ∈ SetFamily.extremalProfiles F) :
    PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity F) W
      (test p q hpq hq t query) =
      if query = phase then value p q t (familyTuranDensity F) else 0 := by
  have hd : 0 < familyTuranDensity F - (p : ℝ) / q := sub_pos.mpr hz
  have ha := SwitchScalar.optimalMass_pos _ hd
  have ha1 : SwitchScalar.optimalMass (familyTuranDensity F - (p : ℝ) / q) < 1 :=
    (SwitchScalar.optimalMass_lt_three_quarters _ hd.le).trans (by norm_num)
  have h := PhaseRoles.phaseMap_readback F p q hpq hq t phase query _ ha ha1 W hW.1
    (SetFamily.edgeTest 3) (by simp [SetFamily.edgeTest, RGraph.oneEdge])
    PhaseRoles.oneEdge_three_noIsolates
  rw [hW.2] at h
  change _ = PhaseRoles.readbackFactor q t
    (SwitchScalar.optimalMass (familyTuranDensity F - (p : ℝ) / q)) 3 *
      (if query = phase then familyTuranDensity F else 0) at h
  simpa only [test, PhaseRoles.extremalPhaseMap, value, mul_ite, mul_zero] using h

theorem phase_separator (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) (phase : Bool)
    (W : SetFamily.Profile 3) (hW : W ∈ SetFamily.extremalProfiles F) :
    separator p q hpq hq t
      (PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity F) W) =
      if phase then -value p q t (familyTuranDensity F) else value p q t (familyTuranDensity F) := by
  unfold separator
  rw [phase_coordinate F p q hpq hq t hz phase false W hW,
    phase_coordinate F p q hpq hq t hz phase true W hW]
  cases phase <;> simp

theorem neutral_separator (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    separator p q hpq hq t (NeutralRoles.neutralProfile (CodePools.pool p q hpq) t) = 0 := by
  unfold separator test
  rw [NeutralRoles.neutralProfile_readback_zero p q hpq hq t false (SetFamily.edgeTest 3)
      (by simp [SetFamily.edgeTest, RGraph.oneEdge]) PhaseRoles.oneEdge_three_noIsolates,
    NeutralRoles.neutralProfile_readback_zero p q hpq hq t true (SetFamily.edgeTest 3)
      (by simp [SetFamily.edgeTest, RGraph.oneEdge]) PhaseRoles.oneEdge_three_noIsolates]
  ring

end TuranUniversality.Structural.Separation
