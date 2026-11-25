module

public import TuranUniversality.Structural.PhaseReadback
public import TuranUniversality.Structural.PhaseImage
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Injective phase maps, their homeomorphic images, and separation

Readback determines every edged coordinate without isolated vertices.
The proved source-support reduction then determines the complete profile.
Compactness makes each continuous injection a homeomorphism onto its image.
One actual ordinary readback test separates the two extremal phase images.
-/

namespace TuranUniversality.Structural.PhaseRoles

theorem phaseMap_injOn (B : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (phase : Bool)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Set.InjOn (phaseMap (CodePools.pool p q hpq) phase
      (optimalRoleWeight (CodePools.blockCount q) t α))
      (SetFamily.freeLimitProfiles (B : Set _)) := by
  intro W hW Z hZ heq
  apply SetFamily.IsLimitProfile.ext_of_noIsolates W Z hW.1 hZ.1
  intro A hA hno
  have h := congrFun heq (readbackTest p q hpq hq t phase A)
  rw [phaseMap_readback B p q hpq hq t phase phase α hα hα1 W hW A hA hno,
    phaseMap_readback B p q hpq hq t phase phase α hα hα1 Z hZ A hA hno,
    if_pos rfl] at h
  have hz : (if phase = phase then Z A else (0 : ℝ)) = Z A := if_pos rfl
  rw [hz] at h
  exact mul_left_cancel₀ (ne_of_gt (readbackFactor_pos q t α hα hα1 A.1)) h

theorem extremalPhaseMap_injOn (B : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (phase : Bool)
    (hz : (p : ℝ) / q < familyTuranDensity B) :
    Set.InjOn (extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity B))
      (SetFamily.extremalProfiles B) := by
  have ha := SwitchScalar.optimalMass_pos _ (sub_pos.mpr hz)
  have ha1 : SwitchScalar.optimalMass (familyTuranDensity B - (p : ℝ) / q) < 1 :=
    (SwitchScalar.optimalMass_lt_three_quarters _ (sub_nonneg.mpr hz.le)).trans (by norm_num)
  intro W hW Z hZ h
  exact phaseMap_injOn B p q hpq hq t phase _ ha ha1 hW.1 hZ.1 h

noncomputable def phaseHomeomorph (B : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (phase : Bool)
    (hz : (p : ℝ) / q < familyTuranDensity B) :
    (SetFamily.extremalProfiles B) ≃ₜ
      (extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity B) ''
        SetFamily.extremalProfiles B) := by
  letI : CompactSpace (SetFamily.extremalProfiles B) :=
    isCompact_iff_compactSpace.mp (SetFamily.isCompact_extremalProfiles B)
  let e := Equiv.Set.imageOfInjOn
    (extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity B))
    (SetFamily.extremalProfiles B) (extremalPhaseMap_injOn B p q hpq hq t phase hz)
  have he : Continuous e := by
    exact ((continuous_extremalPhaseMap (CodePools.pool p q hpq) phase p q _).comp
      continuous_subtype_val).subtype_mk (fun (W : SetFamily.extremalProfiles B) =>
        show extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity B) W.val ∈
          extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity B) ''
            SetFamily.extremalProfiles B from ⟨W.val, W.property, rfl⟩)
  exact he.homeoOfEquivCompactToT2

theorem oneEdge_three_noIsolates : Uniformity.NoIsolates (RGraph.oneEdge 3) := by
  intro v
  exact ⟨Finset.univ, by simp [RGraph.oneEdge], Finset.mem_univ v⟩

theorem phaseImages_disjoint (B : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity B) :
    Disjoint
      (extremalPhaseMap (t := t) (CodePools.pool p q hpq) false p q (familyTuranDensity B) ''
        SetFamily.extremalProfiles B)
      (extremalPhaseMap (t := t) (CodePools.pool p q hpq) true p q (familyTuranDensity B) ''
        SetFamily.extremalProfiles B) := by
  apply Set.disjoint_left.mpr
  rintro Z ⟨W, hW, rfl⟩ ⟨Y, hY, heq⟩
  let α := SwitchScalar.optimalMass (familyTuranDensity B - (p : ℝ) / q)
  have ha : 0 < α := SwitchScalar.optimalMass_pos _ (sub_pos.mpr hz)
  have ha1 : α < 1 := (SwitchScalar.optimalMass_lt_three_quarters _
    (sub_nonneg.mpr hz.le)).trans (by norm_num)
  have hzpos : 0 < familyTuranDensity B :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)) hz
  have hedge : (SetFamily.edgeTest 3).2.edges.Nonempty :=
    ⟨Finset.univ, by simp [SetFamily.edgeTest, RGraph.oneEdge]⟩
  have h := congrFun heq (readbackTest p q hpq hq t false (SetFamily.edgeTest 3))
  change phaseMap _ true (optimalRoleWeight _ _ α) Y _ =
    phaseMap _ false (optimalRoleWeight _ _ α) W _ at h
  rw [phaseMap_readback B p q hpq hq t true false α ha ha1 Y hY.1 _ hedge oneEdge_three_noIsolates,
    phaseMap_readback B p q hpq hq t false false α ha ha1 W hW.1 _ hedge oneEdge_three_noIsolates] at h
  have hp : 0 < readbackFactor q t α (SetFamily.edgeTest 3).1 * familyTuranDensity B :=
    mul_pos (readbackFactor_pos q t α ha ha1 _) hzpos
  have hzero : (if false = true then Y (SetFamily.edgeTest 3) else (0 : ℝ)) = 0 := rfl
  have hone : (if false = false then W (SetFamily.edgeTest 3) else (0 : ℝ)) =
      W (SetFamily.edgeTest 3) := rfl
  rw [hzero, hone, mul_zero, hW.2] at h
  linarith

theorem phaseImage_subset_extremal (B : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (phase : Bool)
    (hz : (p : ℝ) / q < familyTuranDensity B) :
    extremalPhaseMap (t := t) (CodePools.pool p q hpq) phase p q (familyTuranDensity B) ''
      SetFamily.extremalProfiles B ⊆
        SetFamily.extremalProfiles (Ordinary.forbidden B (CodePools.pool p q hpq) t) := by
  rintro Z ⟨W, hW, rfl⟩
  exact extremalPhaseMap_mem B hedges (CodePools.pool p q hpq)
    (fun _ _ h => CodePools.pools_disjoint p q hpq h) phase p q (Nat.cast_nonneg p)
    (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz (CodePools.pool_card_cast p q hpq hq) W hW

end TuranUniversality.Structural.PhaseRoles
