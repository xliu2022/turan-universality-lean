module

public import TuranUniversality.Structural.NeutralRoles
public import TuranUniversality.Structural.CompiledCoupling
public import TuranUniversality.Structural.PhaseConvergence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The unique zero-gap compiled limit

The active part is erased with an explicit four-sample error. The remaining
actual neutral compiled graphs converge to a finite role-sampling profile.
All comparisons keep the original finite carrier and original real weights.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural

namespace Compiled

theorem profile_tendsto_of_repair {I : Type*} {X : I → Type*}
    [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)] {b t : ℕ} {B : Finset (FiniteGraph 3)}
    (l : Filter I) (Ω : Label → Finset (Cube.Word b)) (R : ∀ i, RecordSystem (X i))
    (O : ∀ i, LegalObject B (X i)) (x : ∀ i, Vertex b t (X i) → ℝ)
    (hx : ∀ i, ProbabilityWeights (x i))
    (hT : ∀ᶠ i in l, 0 < dataMass (x i))
    (hd : Tendsto (fun i => sampleProbability (normalizedData (x i))
      ((R i).Disagreement (O i))) l (𝓝 0))
    (W : SetFamily.Profile (t + (3 * b + 4)))
    (hW : Tendsto (fun i => SetFamily.weightedProfile (graph t Ω (O i).records) (x i)) l (𝓝 W)) :
    Tendsto (fun i => SetFamily.weightedProfile (graph t Ω (R i)) (x i)) l (𝓝 W) := by
  have hm := mismatch_tendsto l Ω R O x hx hT hd
  apply tendsto_pi_nhds.mpr
  intro A
  have hdiff := A.2.weightedHomDensity_sub_tendsto_zero_of_mismatch
    (fun i => graph t Ω (R i)) (fun i => graph t Ω (O i).records) x hx l hm
  have h := hdiff.add ((tendsto_pi_nhds.mp hW) A)
  simpa only [SetFamily.weightedProfile, sub_add_cancel, zero_add] using h

end Compiled

namespace NeutralRoles

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

noncomputable def profile (Ω : Label → Finset (Cube.Word b)) (z : Role b t → ℝ) :
    SetFamily.Profile (t + (3 * b + 4)) := fun H => coordinate Ω H.2 z

theorem continuous_profile (Ω : Label → Finset (Cube.Word b)) : Continuous (profile (t := t) Ω) := by
  apply continuous_pi
  intro H
  exact continuous_coordinate Ω H.2

noncomputable def optimalRoleWeight (b t : ℕ) : Role b t → ℝ
  | .inl (.inl _) => 1 / (OuterWeights.arity b t : ℝ)
  | .inl (.inr _) => 3 / (5 * (OuterWeights.arity b t : ℝ))
  | .inr _ => 4 / (OuterWeights.arity b t : ℝ)

noncomputable def neutralProfile (Ω : Label → Finset (Cube.Word b)) (t : ℕ) :
    SetFamily.Profile (t + (3 * b + 4)) := profile Ω (optimalRoleWeight b t)

theorem object_realizes_neutral (hedges : ∀ A ∈ B, A.2.edges.Nonempty) (O : LegalObject B V) :
    (object B hedges : LegalObject B V).Realizes O.records (Finset.univ \ O.active) := by
  intro X _hX hXS
  have hi : X ∩ O.active = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    exact (Finset.mem_sdiff.mp (hXS (Finset.mem_inter.mp hv).1)).2 (Finset.mem_inter.mp hv).2
  have hn (a : Bool) : ∅ ∉ (O.inner a).edges := by
    intro he
    have hc := (O.inner a).uniform ∅ he
    simp at hc
  have hl : O.records.label X = .inl 0 := by
    change O.label X = _
    simp [LegalObject.label, hi, hn]
  rw [hl]
  exact LegalObject.empty_labels hedges ∅ X 0 (by simp)

theorem object_disagreement_le (hedges : ∀ A ∈ B, A.2.edges.Nonempty) (O : LegalObject B V)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    sampleProbability x (O.records.Disagreement (object B hedges : LegalObject B V)) ≤
      6 * (∑ v, (x v) ^ 2) + 4 * O.activeMass x := by
  have h := RecordSystem.disagreement_probability_le (object B hedges : LegalObject B V)
    (Finset.univ \ O.active) (object_realizes_neutral hedges O) x hx
  have hs : 1 - ∑ v ∈ Finset.univ \ O.active, x v = O.activeMass x := by
    change 1 - O.neutralMass x = _
    rw [O.neutralMass_eq, hx.2]
    ring
  have he : O.records.erasure x ≤ 6 * ∑ v, (x v) ^ 2 := by
    rw [← O.records.erasure_probability x hx]
    simpa only [O.records_successful] using collision_probability_le x hx
  rw [hs] at h
  linarith

variable {I : Type*} {X : I → Type*}
variable [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

theorem profile_tendsto (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b))
    (x : ∀ i, Compiled.Vertex b t (X i) → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I) (z : Role b t → ℝ)
    (hT : ∀ᶠ i in l, 0 < Compiled.dataMass (x i))
    (hz : Tendsto (fun i => roleWeight (x i)) l (𝓝 z))
    (hs : Tendsto (fun i => ∑ v : X i, (Compiled.normalizedData (x i) v) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => SetFamily.weightedProfile
      (Compiled.graph t Ω (object B hedges : LegalObject B (X i)).records) (x i))
      l (𝓝 (profile Ω z)) := by
  have hΦ := (continuous_profile Ω).tendsto z |>.comp hz
  apply tendsto_pi_nhds.mpr
  intro H
  have hsmall : Tendsto (fun i => (H.1 : ℝ) ^ 2 *
      ∑ v : X i, (Compiled.normalizedData (x i) v) ^ 2) l (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul ((H.1 : ℝ) ^ 2)
  have herr : Tendsto (fun i => SetFamily.weightedProfile
      (Compiled.graph t Ω (object B hedges : LegalObject B (X i)).records) (x i) H -
      profile Ω (roleWeight (x i)) H) l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg _)) _ hsmall
    filter_upwards [hT] with i hi
    simpa only [SetFamily.weightedProfile, profile, Fintype.card_fin] using
      coordinate_error hedges Ω H.2 (x i) (hx i) hi
  have h := herr.add ((tendsto_pi_nhds.mp hΦ) H)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using h

theorem object_disagreement_tendsto (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (O : ∀ i, LegalObject B (X i)) (x : ∀ i, X i → ℝ) (l : Filter I)
    (hx : ∀ᶠ i in l, ProbabilityWeights (x i))
    (hs : Tendsto (fun i => ∑ v : X i, (x i v) ^ 2) l (𝓝 0))
    (ha : Tendsto (fun i => (O i).activeMass (x i)) l (𝓝 0)) :
    Tendsto (fun i => sampleProbability (x i)
      ((O i).records.Disagreement (object B hedges : LegalObject B (X i)))) l (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hx] with i hi
    exact sampleProbability_nonneg _ hi.1 _
  · filter_upwards [hx] with i hi
    exact object_disagreement_le hedges (O i) (x i) hi
  · simpa only [mul_zero, zero_add] using (hs.const_mul 6).add (ha.const_mul 4)

/-- Zero gap determines every coordinate of any near-optimal actual compiled
sequence, without assuming in advance that the sequence has a limit. -/
theorem compiled_profile_tendsto_neutral
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : ∀ i, RecordSystem (X i))
    (hlocal : ∀ i, (R i).LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : familyTuranDensity F = p / q)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : ∀ i, Compiled.Vertex b t (X i) → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I)
    (hpoly : Tendsto (fun i => (Compiled.graph t Ω (R i)).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => SetFamily.weightedProfile (Compiled.graph t Ω (R i)) (x i)) l
      (𝓝 (neutralProfile Ω t)) := by
  have hge : p / q ≤ familyTuranDensity F := hz.ge
  obtain ⟨O, _, hd, _, ha, _, _, _⟩ :=
    Compiled.exists_decoded_models X F hedges Ω R hlocal p q hp hpq hq hge hΩ x hx hpoly
  have hb := homomorphicClosure_has_edges F hedges
  have hT := Compiled.eventually_positive_dataMass X F hedges Ω R hlocal
    p q hp hpq hq hge hΩ x hx hpoly
  have hs := Compiled.normalized_squares_tendsto X F hedges Ω R hlocal
    p q hp hpq hq hge hΩ x hx hpoly
  have hroot := Compiled.near_optimal_root_limits X F hedges Ω R hlocal
    p q hp hpq hq hge hΩ x hx hpoly
  have hrole : Tendsto (fun i => roleWeight (x i)) l (𝓝 (optimalRoleWeight b t)) := by
    apply tendsto_pi_nhds.mpr
    rintro ((j | v) | a)
    · exact hroot.1 j
    · exact hroot.2.1 v.1 v.2
    · exact hroot.2.2
  have hneutral := profile_tendsto hb Ω x hx l (optimalRoleWeight b t) hT hrole hs
  have ha0 : Tendsto (fun i => (O i).activeMass (Compiled.normalizedData (x i))) l (𝓝 0) := by
    simpa only [hz, sub_self, SwitchScalar.optimalMass, mul_zero, zero_div] using ha
  have hprob : ∀ᶠ i in l, ProbabilityWeights (Compiled.normalizedData (x i)) :=
    hT.mono (fun i hi => Compiled.normalizedData_probability (x i) (hx i).1 hi)
  have hd0 := object_disagreement_tendsto hb O (fun i => Compiled.normalizedData (x i)) l
    hprob hs ha0
  have hO := Compiled.profile_tendsto_of_repair l Ω (fun i => (O i).records)
    (fun i => (object _ hb : LegalObject (homomorphicClosure F) (X i))) x hx hT hd0
    (neutralProfile Ω t) hneutral
  exact Compiled.profile_tendsto_of_repair l Ω R O x hx hT hd (neutralProfile Ω t) hO

end NeutralRoles
end TuranUniversality.Structural
