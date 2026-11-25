module

public import TuranUniversality.Structural.ReadbackNormalization
public import TuranUniversality.Structural.CompiledRepair
public import TuranUniversality.Density.WeightedCollisions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Neutral distinct assignments and readback limits

The five neutral frame vertices are sampled without collisions. Their exact
weight converges to the fifth power of the neutral mass because the actual
second moment vanishes. This proves the limiting coefficient in readback
without replacing a finite elementary symmetric sum by a power prematurely.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.Readback

open Density

variable {V : Type*} [DecidableEq V] {B : Finset (FiniteGraph 3)}

abbrev NeutralVertex (O : LegalObject B V) := {v : V // v ∉ O.active}

def neutralAssignmentEquiv (O : LegalObject B V) :
    {f : Fin 5 → NeutralVertex O // Function.Injective f} ≃ NeutralAssignment O where
  toFun f := ⟨fun i => (f.val i).val,
    ⟨fun i j h => f.property (Subtype.ext h), fun i => (f.val i).property⟩⟩
  invFun d := ⟨fun i => ⟨d.val i, d.property.2 i⟩,
    fun i j h => d.property.1 (congrArg Subtype.val h)⟩
  left_inv f := by apply Subtype.ext; funext i; rfl
  right_inv d := by apply Subtype.ext; rfl

theorem sum_neutralSubtype [Fintype V] (O : LegalObject B V) (x : V → ℝ) :
    (∑ v : NeutralVertex O, x v.val) = ∑ v ∈ neutralSet O, x v := by
  symm
  exact Finset.sum_subtype (neutralSet O) (by intro v; simp [neutralSet]) x

theorem neutral_distinctWeight [Fintype V] (O : LegalObject B V) (x : V → ℝ) :
    distinctWeight (A := Fin 5) (fun v : NeutralVertex O => x v.val) =
      (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O) x 5 := by
  rw [distinctWeight_eq_sum, ← neutralAssignment_weight]
  apply Fintype.sum_equiv (neutralAssignmentEquiv O)
  intro f
  rfl

theorem neutral_quintic_bounds [Fintype V] (O : LegalObject B V) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hs : ∑ v, x v ≤ 1) :
    0 ≤ O.neutralMass x ^ 5 -
        (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O) x 5 ∧
      O.neutralMass x ^ 5 -
          (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O) x 5 ≤
        25 * ∑ v, (x v) ^ 2 := by
  have hsub : (∑ v : NeutralVertex O, x v.val) ≤ 1 := by
    rw [sum_neutralSubtype]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => hx v)).trans hs
  have h := distinctWeight_subprob_bounds (A := Fin 5)
    (fun v : NeutralVertex O => x v.val) (fun v => hx v.val) hsub
  rw [neutral_distinctWeight O x, sum_neutralSubtype] at h
  have hsq : (∑ v : NeutralVertex O, (x v.val) ^ 2) ≤ ∑ v, (x v) ^ 2 := by
    rw [sum_neutralSubtype O (fun v => (x v) ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => sq_nonneg _)
  change 0 ≤ O.neutralMass x ^ 5 -
      (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O) x 5 ∧
    O.neutralMass x ^ 5 -
      (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O) x 5 ≤
      (5 : ℝ) ^ 2 * ∑ v : NeutralVertex O, (x v.val) ^ 2 at h
  rw [show (5 : ℝ) ^ 2 = 25 by norm_num] at h
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))⟩

theorem neutral_quintic_tendsto {I : Type*} {V : I → Type*}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (O : ∀ i, LegalObject B (V i)) (x : ∀ i, V i → ℝ)
    (hx : ∀ i v, 0 ≤ x i v) (hs : ∀ i, ∑ v, x i v ≤ 1)
    (l : Filter I) (w : ℝ)
    (hmass : Tendsto (fun i => (O i).neutralMass (x i)) l (𝓝 w))
    (hsquares : Tendsto (fun i => ∑ v, (x i v) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => (Nat.factorial 5 : ℝ) *
      Weighted.elementary (neutralSet (O i)) (x i) 5) l (𝓝 (w ^ 5)) := by
  have hdef : Tendsto (fun i => (O i).neutralMass (x i) ^ 5 -
      (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet (O i)) (x i) 5)
      l (𝓝 0) := by
    apply squeeze_zero
      (fun i => (neutral_quintic_bounds (O i) (x i) (hx i) (hs i)).1)
      (fun i => (neutral_quintic_bounds (O i) (x i) (hx i) (hs i)).2)
    simpa only [mul_zero] using hsquares.const_mul 25
  convert (hmass.pow 5).sub hdef using 1
  · funext i
    ring
  · simp

theorem weighted_readback_tendsto {I U : Type*} {V : I → Type*}
    [DecidableEq U] [Fintype U] [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (F : RGraph U 3) (hF : F.edges.Nonempty) (hno : Uniformity.NoIsolates F)
    (O : ∀ i, LegalObject B (V i)) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (Support.poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (x : ∀ i, Compiled.Vertex (CodePools.blockCount q) t (V i) → ℝ)
    (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I) (ρ w a d : ℝ)
    (hroot : Tendsto (fun i => rootProduct (x i)) l (𝓝 ρ))
    (hneutral : Tendsto (fun i => (O i).neutralMass (Compiled.dataWeight (x i))) l (𝓝 w))
    (hsquares : Tendsto (fun i => ∑ v, (Compiled.dataWeight (x i) v) ^ 2) l (𝓝 0))
    (hactive : Tendsto (fun i => (O i).activeMass (Compiled.dataWeight (x i))) l (𝓝 a))
    (hinner : Tendsto (fun i => F.weightedHomDensity (activeGraph (O i) phase)
      (normalizedActiveWeight (O i) (Compiled.dataWeight (x i)))) l (𝓝 d)) :
    Tendsto (fun i => (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((Support.poolGraph _).uniform Z hZ) F).weightedHomDensity
      (Compiled.graph t (CodePools.pool p q hpq) (O i).records) (x i)) l
      (𝓝 ((Fintype.card (RootActions.group (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)) : ℝ) *
        ρ * w ^ 5 * a ^ Fintype.card U * d)) := by
  have hdata (i : I) : ∑ v, Compiled.dataWeight (x i) v ≤ 1 := by
    have h := Compiled.mass_sum (x i) (hx i)
    have hs : 0 ≤ ∑ j, Compiled.suspensionWeight (x i) j :=
      Finset.sum_nonneg (fun j _ => (hx i).1 _)
    have hb : 0 ≤ ∑ j, Compiled.blockMass (x i) j :=
      Finset.sum_nonneg (fun j _ => Compiled.blockMass_nonneg (x i) (hx i).1 j)
    change ∑ v, Compiled.dataWeight (x i) v ≤ 1
    change _ + _ + (∑ v, Compiled.dataWeight (x i) v) = 1 at h
    linarith
  have hn := neutral_quintic_tendsto O (fun i => Compiled.dataWeight (x i))
    (fun i v => (hx i).1 _) hdata l w hneutral hsquares
  have hlim := (((hroot.const_mul (Fintype.card (RootActions.group
      (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)) : ℝ)).mul hn).mul
    (hactive.pow (Fintype.card U))).mul hinner
  apply hlim.congr'
  exact Filter.Eventually.of_forall (fun i =>
    (weighted_readback_normalized p q hpq hq t F hF hno (O i) phase Z hZ (x i) (hx i).1).symm)

end TuranUniversality.Structural.Readback
