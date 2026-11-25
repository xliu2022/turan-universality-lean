module

public import TuranUniversality.Hypergraph.FiniteProfiles
public import TuranUniversality.Density.FreeRealizationApprox
public import TuranUniversality.Structural.WeightedExpectations

@[expose] public section

/-! # Hom-density coordinates of a finite multiset profile

Independent role sampling defines every coordinate. The only discrepancy
from an actual finite realization comes from collisions in the vertex
sample; no distinctness condition is imposed on its sampled roles.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.FiniteRolePattern

open Density

variable {R U V : Type*} [DecidableEq R] [DecidableEq U] [DecidableEq V]
variable [Fintype R] [Fintype U] [Fintype V] {r : ℕ}

def Compatible (P : FiniteRolePattern R r) (H : RGraph U r) (θ : U → R) : Prop :=
  ∀ e ∈ H.edges, e.val.map θ ∈ P.edges

noncomputable def coordinate (P : FiniteRolePattern R r) (H : RGraph U r) (z : R → ℝ) : ℝ :=
  weightedMean z (fun θ => truth (P.Compatible H θ))

noncomputable def profile (P : FiniteRolePattern R r) (z : R → ℝ) : SetFamily.Profile r :=
  fun H => P.coordinate H.2 z

theorem continuous_coordinate (P : FiniteRolePattern R r) (H : RGraph U r) :
    Continuous (P.coordinate H) := by
  unfold coordinate weightedMean productWeight
  fun_prop

theorem continuous_profile (P : FiniteRolePattern R r) : Continuous P.profile := by
  apply continuous_pi
  intro H
  exact P.continuous_coordinate H.2

theorem compatible_iff_of_injective (P : FiniteRolePattern R r) (H : RGraph U r)
    (ρ : V → R) (f : U → V) (hf : Function.Injective f) :
    P.Compatible H (ρ ∘ f) ↔ H.IsHom (P.graph ρ) f := by
  constructor
  · intro h e he
    apply (P.mem_graph ρ (e.image f)).mpr
    refine ⟨by rw [Finset.card_image_of_injective _ hf, H.uniform e he], ?_⟩
    rw [Finset.image_val_of_injOn hf.injOn, Multiset.map_map]
    exact h e he
  · intro h e he
    have hm := ((P.mem_graph ρ (e.image f)).mp (h e he)).2
    rwa [Finset.image_val_of_injOn hf.injOn, Multiset.map_map] at hm

theorem weightedHom_error (P : FiniteRolePattern R r) (H : RGraph U r)
    (ρ : V → R) (x : V → ℝ) (hx : ProbabilityWeights x) :
    |H.weightedHomDensity (P.graph ρ) x - P.coordinate H (pushforwardWeight ρ x)| ≤
      (Fintype.card U : ℝ) ^ 2 * ∑ v, (x v) ^ 2 := by
  have hc : P.coordinate H (pushforwardWeight ρ x) =
      weightedMean x (fun f : U → V => truth (P.Compatible H (ρ ∘ f))) :=
    (weightedMean_pushforward ρ x (fun θ => truth (P.Compatible H θ))).symm
  rw [hc]
  apply (weightedMean_abs_sub_le x hx.1 (H.homIndicator (P.graph ρ)) _).trans
  apply (weightedMean_mono x hx.1 (fun f => ?_)).trans (weightedMean_collision_le x hx)
  by_cases hf : Function.Injective f
  · simp only [RGraph.homIndicator, truth, P.compatible_iff_of_injective H ρ f hf,
      sub_self, abs_zero]
    split <;> norm_num
  · have h1 := H.homIndicator_nonneg (P.graph ρ) f
    have h2 := H.homIndicator_le_one (P.graph ρ) f
    have h3 := truth_nonneg (P.Compatible H (ρ ∘ f))
    have h4 : truth (P.Compatible H (ρ ∘ f)) ≤ 1 := by
      unfold truth
      split <;> norm_num
    simp only [hf, not_false_eq_true, truth_true]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem weightedProfile_tendsto (P : FiniteRolePattern R r)
    {I : Type*} {X : I → Type*} [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]
    (ρ : ∀ i, X i → R) (x : ∀ i, X i → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I) (z : R → ℝ)
    (hz : Tendsto (fun i => pushforwardWeight (ρ i) (x i)) l (𝓝 z))
    (hs : Tendsto (fun i => ∑ v : X i, (x i v) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => fun H : FiniteGraph r =>
      H.2.weightedHomDensity (P.graph (ρ i)) (x i)) l (𝓝 (P.profile z)) := by
  apply tendsto_pi_nhds.mpr
  intro H
  have hsmall : Tendsto (fun i => (H.1 : ℝ) ^ 2 * ∑ v : X i, (x i v) ^ 2) l (𝓝 0) := by
    simpa using hs.const_mul ((H.1 : ℝ) ^ 2)
  have herr : Tendsto (fun i => H.2.weightedHomDensity (P.graph (ρ i)) (x i) -
      P.coordinate H.2 (pushforwardWeight (ρ i) (x i))) l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero (fun _ => abs_nonneg _) _ hsmall
    intro i
    simpa only [Fintype.card_fin] using P.weightedHom_error H.2 (ρ i) (x i) (hx i)
  have hc := (P.continuous_coordinate H.2).tendsto z |>.comp hz
  simpa only [Function.comp_apply, profile, sub_add_cancel, zero_add] using herr.add hc

end TuranUniversality.FiniteRolePattern
