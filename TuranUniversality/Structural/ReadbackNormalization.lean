module

public import TuranUniversality.Structural.ReadbackDensity
public import TuranUniversality.Density.WeightedHomRestriction

@[expose] public section

/-! # Readback with the normalized active weighting

Every vertex of a test without isolated vertices lands in the active set
under an inner homomorphism. Restriction and homogeneity therefore give
the paper's active-mass power. When the active mass is zero, a test with
an edge has readback density zero, proved directly from nonnegative
weights rather than from a division convention.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Readback

open Cube Support TripleClasses Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable {B : Finset (FiniteGraph 3)}

def activeGraph (O : LegalObject B V) (phase : Bool) : RGraph O.active 3 :=
  (O.inner phase).pullback (Function.Embedding.subtype _)

theorem inner_hom_active (F : RGraph U 3) (hno : Uniformity.NoIsolates F)
    (O : LegalObject B V) (phase : Bool) (g : U → V) (hg : F.IsHom (O.inner phase) g) :
    ∀ u, g u ∈ O.active := by
  intro u
  obtain ⟨e, he, hue⟩ := hno u
  exact O.supported phase _ (hg e he) (Finset.mem_image.mpr ⟨u, hue, rfl⟩)

theorem inner_weight_active [Fintype U] [Fintype V]
    (F : RGraph U 3) (hno : Uniformity.NoIsolates F) (O : LegalObject B V) (phase : Bool)
    (x : V → ℝ) :
    F.weightedHomDensity (activeGraph O phase) (fun v => x v.val) =
      F.weightedHomDensity (O.inner phase) x := by
  apply F.weightedHomDensity_pullback_of_hom_supported (O.inner phase)
    (Function.Embedding.subtype _) _ x
  intro g hg u
  exact ⟨⟨g u, inner_hom_active F hno O phase g hg u⟩, rfl⟩

noncomputable def normalizedActiveWeight [Fintype V] (O : LegalObject B V)
    (x : V → ℝ) (v : O.active) : ℝ := x v.val / O.activeMass x

theorem normalizedActive_probability [Fintype V] (O : LegalObject B V)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (hm : 0 < O.activeMass x) :
    ProbabilityWeights (normalizedActiveWeight O x) := by
  refine ⟨fun v => div_nonneg (hx v.val) hm.le, ?_⟩
  unfold normalizedActiveWeight
  rw [← Finset.sum_div, Finset.sum_coe_sort]
  change O.activeMass x / O.activeMass x = 1
  exact div_self (ne_of_gt hm)

theorem active_weight_zero [Fintype V] (O : LegalObject B V) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hm : O.activeMass x = 0) {v : V} (hv : v ∈ O.active) :
    x v = 0 := by
  have hle : x v ≤ O.activeMass x := Finset.single_le_sum (fun v _ => hx v) hv
  rw [hm] at hle
  exact le_antisymm hle (hx v)

theorem source_card_pos [Fintype U] (F : RGraph U 3) (hF : F.edges.Nonempty) :
    0 < Fintype.card U := by
  obtain ⟨e, he⟩ := hF
  obtain ⟨u, _⟩ := Finset.card_pos.mp (by rw [F.uniform e he]; omega : 0 < e.card)
  letI : Nonempty U := ⟨u⟩
  exact Fintype.card_pos

theorem inner_weight_zero [Fintype U] [Fintype V]
    (F : RGraph U 3) (hF : F.edges.Nonempty) (O : LegalObject B V) (phase : Bool)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (hm : O.activeMass x = 0) :
    F.weightedHomDensity (O.inner phase) x = 0 := by
  obtain ⟨e, he⟩ := hF
  obtain ⟨u, hue⟩ := Finset.card_pos.mp (by rw [F.uniform e he]; omega : 0 < e.card)
  rw [RGraph.weightedHomDensity_eq_sum_homs]
  apply Finset.sum_eq_zero
  intro g _
  have hu := O.supported phase _ (g.property e he) (Finset.mem_image.mpr ⟨u, hue, rfl⟩)
  exact Finset.prod_eq_zero (Finset.mem_univ u) (active_weight_zero O x hx hm hu)

theorem inner_weight_normalize [Fintype U] [Fintype V]
    (F : RGraph U 3) (hF : F.edges.Nonempty) (hno : Uniformity.NoIsolates F)
    (O : LegalObject B V) (phase : Bool) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    F.weightedHomDensity (O.inner phase) x =
      O.activeMass x ^ Fintype.card U *
        F.weightedHomDensity (activeGraph O phase) (normalizedActiveWeight O x) := by
  by_cases hm : O.activeMass x = 0
  · rw [inner_weight_zero F hF O phase x hx hm, hm,
      zero_pow (Nat.ne_of_gt (source_card_pos F hF)), zero_mul]
  · have he : (fun v : O.active => O.activeMass x * normalizedActiveWeight O x v) =
        (fun v : O.active => x v.val) := by
      funext v
      unfold normalizedActiveWeight
      field_simp
    calc
      _ = F.weightedHomDensity (activeGraph O phase) (fun v => x v.val) :=
        (inner_weight_active F hno O phase x).symm
      _ = F.weightedHomDensity (activeGraph O phase)
          (fun v => O.activeMass x * normalizedActiveWeight O x v) := congrArg _ he.symm
      _ = _ := F.weightedHomDensity_scale _ _ _

/-- Equation `readback`, including the zero-active-mass convention, for the
actual ordinary test and the actual active induced inner graph. -/
theorem weighted_readback_normalized [Fintype U] [Fintype V]
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (F : RGraph U 3) (hF : F.edges.Nonempty) (hno : Uniformity.NoIsolates F)
    (O : LegalObject B V) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (x : Compiled.Vertex (CodePools.blockCount q) t V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).weightedHomDensity
      (Compiled.graph t (CodePools.pool p q hpq) O.records) x =
      (Fintype.card (RootActions.group (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)) : ℝ) * rootProduct x *
        ((Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O)
          (fun v => x (dataVertex v)) 5) *
        O.activeMass (fun v => x (dataVertex v)) ^ Fintype.card U *
          F.weightedHomDensity (activeGraph O phase)
            (normalizedActiveWeight O (fun v => x (dataVertex v))) := by
  rw [weighted_readback p q hpq hq t F hno O phase Z hZ,
    inner_weight_normalize F hF hno O phase _ (fun v => hx (dataVertex v))]
  ring

end TuranUniversality.Structural.Readback
