module

public import TuranUniversality.Structural.PhaseInnerProfiles
public import TuranUniversality.Structural.CompiledCoupling
public import TuranUniversality.Structural.PhaseImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exhaustion of positive-gap near-optimal compiled profile limits

Finite record repair is applied on the original carriers and weights. Its
actual edge mismatch tends to zero. A fixed-phase subsequence and compactness
of the hom-free inner space then identify the limit with one phase map.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.PhaseRoles

theorem compiled_limit_is_phase {X : ℕ → Type*}
    [∀ n, DecidableEq (X n)] [∀ n, Fintype (X n)] {b t : ℕ}
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : ∀ n, RecordSystem (X n))
    (hlocal : ∀ n, (R n).LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q < familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : ∀ n, Compiled.Vertex b t (X n) → ℝ) (hx : ∀ n, ProbabilityWeights (x n))
    (hpoly : Tendsto (fun n => (Compiled.graph t Ω (R n)).edgePolynomial (x n)) atTop
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))))
    (W : SetFamily.Profile (t + (3 * b + 4)))
    (hW : Tendsto (fun n => SetFamily.weightedProfile (Compiled.graph t Ω (R n)) (x n)) atTop (𝓝 W)) :
    ∃ (phase : Bool) (U : SetFamily.Profile 3), U ∈ SetFamily.extremalProfiles F ∧
      W = extremalPhaseMap Ω phase p q (familyTuranDensity F) U := by
  obtain ⟨O, _, hdis, _, _, hactive, hneutral, hinner⟩ :=
    Compiled.exists_decoded_models X F hedges Ω R hlocal p q hp hpq hq hz.le hΩ x hx hpoly
  have hT := Compiled.eventually_positive_dataMass X F hedges Ω R hlocal
    p q hp hpq hq hz.le hΩ x hx hpoly
  have hrepair := Compiled.profile_repair_tendsto atTop Ω R O x hx hT hdis W hW
  have hroot := Compiled.near_optimal_root_limits X F hedges Ω R hlocal
    p q hp hpq hq hz.le hΩ x hx hpoly
  have hsquares := Compiled.data_squares_tendsto X F hedges Ω R hlocal
    p q hp hpq hq hz.le hΩ x hx hpoly
  let δ := familyTuranDensity F - p / q
  let α := SwitchScalar.optimalMass δ
  have hd : 0 < δ := sub_pos.mpr hz
  have ha : 0 < α := SwitchScalar.optimalMass_pos δ hd
  have ha1 : α < 1 := (SwitchScalar.optimalMass_lt_three_quarters δ hd.le).trans (by norm_num)
  have hr : 0 < (OuterWeights.arity b t : ℝ) := Nat.cast_pos.mpr (OuterWeights.arity_pos b t)
  have hapos : 0 < optimalRoleWeight b t α (.inr false) := by
    change 0 < (4 / (OuterWeights.arity b t : ℝ)) * α
    positivity
  have hwpos : 0 < optimalRoleWeight b t α (.inr true) := by
    change 0 < (4 / (OuterWeights.arity b t : ℝ)) * (1 - α)
    exact mul_pos (div_pos (by norm_num) hr) (sub_pos.mpr ha1)
  have haeq : optimalRoleWeight b t α (.inr false) = Compiled.activeLimit b t δ :=
    Compiled.activeLimit_formula b t δ hd.le
  have hweq : optimalRoleWeight b t α (.inr true) = Compiled.neutralLimit b t δ := by
    rw [← Compiled.neutralLimit_formula b t δ hd.le,
      ← Compiled.activeLimit_formula b t δ hd.le]
    change (4 / (OuterWeights.arity b t : ℝ)) * (1 - α) =
      4 / (OuterWeights.arity b t : ℝ) - (4 / (OuterWeights.arity b t : ℝ)) * α
    ring
  have hrole : Tendsto (fun n => roleWeight (O n) (x n)) atTop (𝓝 (optimalRoleWeight b t α)) := by
    apply tendsto_pi_nhds.mpr
    rintro ((j | v) | a)
    · exact hroot.1 j
    · exact hroot.2.1 v.1 v.2
    · cases a
      · simpa only [roleWeight_active, haeq] using hactive
      · simpa only [roleWeight_neutral, hweq] using hneutral
  have hA := ((tendsto_pi_nhds.mp hrole) (.inr false)).eventually (lt_mem_nhds hapos)
  obtain ⟨phase, φ, hφ, hgood, hphase⟩ := exists_fixed_phase_subsequence O
    (fun n => 0 < roleWeight (O n) (x n) (.inr false) ∧ 0 < Compiled.dataMass (x n)) (hA.and hT)
  have hmem n : innerProfile (O (φ n)) phase (x (φ n)) ∈
      SetFamily.freeLimitProfiles (F : Set _) :=
    innerProfile_mem_free F (O (φ n)) phase (x (φ n)) (hx (φ n)).1 (hgood n).1
  obtain ⟨U, hU, ψ, hψ, hUlim⟩ := (SetFamily.isCompact_freeLimitProfiles (F : Set _)).tendsto_subseq
    (x := fun n => innerProfile (O (φ n)) phase (x (φ n))) hmem
  let σ := φ ∘ ψ
  have hσ : StrictMono σ := hφ.comp hψ
  have hUlim' : Tendsto (fun n => innerProfile (O (σ n)) phase (x (σ n))) atTop (𝓝 U) := hUlim
  have hphase' n s (hs : s ≠ phase) : ((O (σ n)).inner s).edges = ∅ := hphase (ψ n) s hs
  have hUedge : U (SetFamily.edgeTest 3) = familyTuranDensity F := by
    have he := (hinner hz).comp hσ.tendsto_atTop
    have he' : Tendsto (fun n => innerProfile (O (σ n)) phase (x (σ n)) (SetFamily.edgeTest 3))
        atTop (𝓝 (familyTuranDensity F)) := by
      apply he.congr'
      exact Eventually.of_forall (fun n =>
        (innerProfile_edge_eq (O (σ n)) phase (hphase' n) (x (σ n)) (hgood (ψ n)).2).symm)
    exact tendsto_nhds_unique ((tendsto_pi_nhds.mp hUlim') _) he'
  refine ⟨phase, U, ⟨hU, hUedge⟩, ?_⟩
  have hphaseLimit := phaseMap_tendsto Ω phase (fun n => O (σ n)) hphase'
    (fun n => x (σ n)) (fun n => hx (σ n)) atTop (optimalRoleWeight b t α) U hapos hwpos
    (hrole.comp hσ.tendsto_atTop) hUlim' (hsquares.comp hσ.tendsto_atTop)
  exact tendsto_nhds_unique (hrepair.comp hσ.tendsto_atTop) hphaseLimit

end TuranUniversality.Structural.PhaseRoles
