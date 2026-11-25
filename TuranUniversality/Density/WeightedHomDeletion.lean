module

public import TuranUniversality.Density.WeightedHomZeroExtension
public import TuranUniversality.Density.WeightedCollisions
public import TuranUniversality.Hypergraph.InducedDegree
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! # Deleting vertices and conditioning the sampling weights

For every finite test, including tests with isolated vertices, conditioning
all sampled vertices to a retained set changes the homomorphism density
by at most the probability that some sampled vertex was deleted. The
bound is exact at the level of independent sampling and needs no removal
lemma or support restriction on the test graph.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality

namespace Density

variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def retainedWeight (x : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then x v else 0

noncomputable def conditionedWeight (x : V → ℝ) (S : Finset V) (v : S) : ℝ :=
  x v.val / ∑ w ∈ S, x w

theorem sum_retainedWeight (x : V → ℝ) (S : Finset V) :
    ∑ v, retainedWeight x S v = ∑ v ∈ S, x v := by
  classical
  simp only [retainedWeight, ← Finset.sum_filter]
  simp

theorem retainedWeight_bounds (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (S : Finset V) (v : V) :
    0 ≤ retainedWeight x S v ∧ retainedWeight x S v ≤ x v := by
  classical
  by_cases h : v ∈ S <;> simp [retainedWeight, h, hx]

theorem retained_mass_bounds (x : V → ℝ) (hx : ProbabilityWeights x) (S : Finset V) :
    0 ≤ ∑ v ∈ S, x v ∧ ∑ v ∈ S, x v ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun v _ => hx.1 v), ?_⟩
  rw [← hx.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hx.1 v)

theorem conditionedWeight_probability (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (S : Finset V) (hs : 0 < ∑ v ∈ S, x v) : ProbabilityWeights (conditionedWeight x S) := by
  refine ⟨fun v => div_nonneg (hx v.val) hs.le, ?_⟩
  simp only [conditionedWeight, ← Finset.sum_div, Finset.sum_coe_sort, div_self (ne_of_gt hs)]

theorem retained_mass_uniform_complement (S : Finset V) (hn : 0 < Fintype.card V) :
    (∑ v ∈ S, (Fintype.card V : ℝ)⁻¹) =
      1 - ((Finset.univ \ S).card : ℝ) / Fintype.card V := by
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hc : (S.card : ℝ) + (Finset.univ \ S).card = Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ] at h
    exact_mod_cast (show S.card + (Finset.univ \ S).card = Fintype.card V by omega)
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_mul, hc, mul_inv_cancel₀ hn0]

theorem conditionedWeight_uniform (S : Finset V) (hn : 0 < Fintype.card V) :
    conditionedWeight (fun _ : V => (Fintype.card V : ℝ)⁻¹) S =
      (fun _ : S => (Fintype.card S : ℝ)⁻¹) := by
  funext v
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hs0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨v.val, v.property⟩))
  simp only [conditionedWeight, Finset.sum_const, nsmul_eq_mul, Fintype.card_coe]
  field_simp

end Density

namespace RGraph

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V] {r : ℕ}

theorem weightedHomDensity_subweight_bounds (F : RGraph U r) (G : RGraph V r)
    (x y : V → ℝ) (hy : ∀ v, 0 ≤ y v) (hyx : ∀ v, y v ≤ x v) :
    0 ≤ F.weightedHomDensity G x - F.weightedHomDensity G y ∧
      F.weightedHomDensity G x - F.weightedHomDensity G y ≤
        (∑ v, x v) ^ Fintype.card U - (∑ v, y v) ^ Fintype.card U := by
  classical
  have hprod (f : U → V) : productWeight y f ≤ productWeight x f :=
    Finset.prod_le_prod₀ (fun _ _ => hy _) (fun _ _ => hyx _)
  have heq : F.weightedHomDensity G x - F.weightedHomDensity G y =
      ∑ f : U → V, (productWeight x f - productWeight y f) * F.homIndicator G f := by
    simp only [weightedHomDensity, weightedMean, ← Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  refine ⟨Finset.sum_nonneg (fun f _ =>
    mul_nonneg (sub_nonneg.mpr (hprod f)) (F.homIndicator_nonneg G f)), ?_⟩
  calc
    _ ≤ ∑ f : U → V, (productWeight x f - productWeight y f) :=
      Finset.sum_le_sum (fun f _ => mul_le_of_le_one_right
        (sub_nonneg.mpr (hprod f)) (F.homIndicator_le_one G f))
    _ = _ := by rw [Finset.sum_sub_distrib, sum_productWeight_mass, sum_productWeight_mass]

theorem weightedHomDensity_retained (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (S : Finset V) :
    F.weightedHomDensity G (retainedWeight x S) =
      F.weightedHomDensity (G.induced S) (fun v => x v.val) := by
  classical
  have h := F.weightedHomDensity_zero_extension G (Function.Embedding.subtype (· ∈ S))
    (retainedWeight x S) (by
      intro v hv
      have hn : v ∉ S := fun h => hv ⟨⟨v, h⟩, rfl⟩
      simp only [retainedWeight, if_neg hn])
  have he : retainedWeight x S ∘ (Function.Embedding.subtype (· ∈ S)) =
      (fun v : S => x v.val) := by
    funext v
    exact if_pos v.property
  rw [he] at h
  exact h.symm

theorem weightedHomDensity_retained_eq_conditioned (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (S : Finset V) (hs : (∑ v ∈ S, x v) ≠ 0) :
    F.weightedHomDensity G (retainedWeight x S) =
      (∑ v ∈ S, x v) ^ Fintype.card U *
        F.weightedHomDensity (G.induced S) (conditionedWeight x S) := by
  rw [weightedHomDensity_retained, ← weightedHomDensity_scale]
  congr 1
  funext v
  exact (mul_div_cancel₀ (x v.val) hs).symm

theorem weightedHomDensity_conditioned_abs_sub_le
    (F : RGraph U r) (G : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x)
    (S : Finset V) (hs : 0 < ∑ v ∈ S, x v) :
    |F.weightedHomDensity G x -
      F.weightedHomDensity (G.induced S) (conditionedWeight x S)| ≤
        1 - (∑ v ∈ S, x v) ^ Fintype.card U := by
  have h := F.weightedHomDensity_subweight_bounds G x (retainedWeight x S)
    (fun v => (retainedWeight_bounds x hx.1 S v).1)
    (fun v => (retainedWeight_bounds x hx.1 S v).2)
  rw [hx.2, one_pow, sum_retainedWeight,
    weightedHomDensity_retained_eq_conditioned F G x S (ne_of_gt hs)] at h
  have hz := conditionedWeight_probability x hx.1 S hs
  have hz0 := F.weightedHomDensity_nonneg (G.induced S) _ hz.1
  have hz1 := F.weightedHomDensity_le_one (G.induced S) _ hz
  have hmass := retained_mass_bounds x hx S
  have hp : (∑ v ∈ S, x v) ^ Fintype.card U ≤ 1 :=
    pow_le_one₀ hmass.1 hmass.2
  have h0 := mul_nonneg (sub_nonneg.mpr hp) hz0
  have h1 := mul_le_mul_of_nonneg_left hz1 (sub_nonneg.mpr hp)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem weightedHomDensity_conditioned_sub_tendsto_zero
    {I : Type*} {W : I → Type*} [∀ i, DecidableEq (W i)] [∀ i, Fintype (W i)]
    (F : RGraph U r) (G : ∀ i, RGraph (W i) r)
    (x : ∀ i, W i → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (S : ∀ i, Finset (W i)) (l : Filter I)
    (hmass : Tendsto (fun i => ∑ v ∈ S i, x i v) l (𝓝 1)) :
    Tendsto (fun i => F.weightedHomDensity (G i) (x i) -
      F.weightedHomDensity ((G i).induced (S i)) (conditionedWeight (x i) (S i))) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hpos := (tendsto_order.1 hmass).1 0 zero_lt_one
  apply squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg _))
    (hpos.mono (fun i hi => F.weightedHomDensity_conditioned_abs_sub_le
      (G i) (x i) (hx i) (S i) hi))
  simpa only [one_pow, sub_self] using (hmass.pow (Fintype.card U)).const_sub 1

theorem homDensity_induced_sub_tendsto_zero
    {I : Type*} {W : I → Type*} [∀ i, DecidableEq (W i)] [∀ i, Fintype (W i)]
    (F : RGraph U r) (G : ∀ i, RGraph (W i) r)
    (hn : ∀ i, 0 < Fintype.card (W i)) (S : ∀ i, Finset (W i)) (l : Filter I)
    (hsmall : Tendsto (fun i => ((Finset.univ \ S i).card : ℝ) /
      Fintype.card (W i)) l (𝓝 0)) :
    Tendsto (fun i => F.homDensity (G i) - F.homDensity ((G i).induced (S i))) l (𝓝 0) := by
  have hx i : ProbabilityWeights (fun _ : W i => (Fintype.card (W i) : ℝ)⁻¹) := by
    have hp : (0 : ℝ) < Fintype.card (W i) := by exact_mod_cast hn i
    exact ⟨fun _ => inv_nonneg.mpr hp.le, by simp [ne_of_gt hp]⟩
  have hmass : Tendsto (fun i => ∑ v ∈ S i, (Fintype.card (W i) : ℝ)⁻¹) l (𝓝 1) := by
    simpa only [retained_mass_uniform_complement _ (hn _), sub_zero] using hsmall.const_sub 1
  have h := F.weightedHomDensity_conditioned_sub_tendsto_zero G
    (fun i _ => (Fintype.card (W i) : ℝ)⁻¹) hx S l hmass
  simpa only [conditionedWeight_uniform _ (hn _), weightedHomDensity_uniform] using h

end RGraph
end TuranUniversality
