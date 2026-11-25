module

public import TuranUniversality.Structural.PhaseApproximation
public import TuranUniversality.Structural.ReadbackConvergence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Matching the generative roles with the exact readback factors -/

open scoped BigOperators

namespace TuranUniversality.Structural.PhaseRoles

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}
variable {B : Finset (FiniteGraph 3)}

theorem roleWeight_active (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ) :
    roleWeight O x (.inr false) = O.activeMass (Compiled.dataWeight x) := by
  exact Finset.sum_coe_sort O.active (Compiled.dataWeight x)

theorem roleWeight_neutral (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ) :
    roleWeight O x (.inr true) = O.neutralMass (Compiled.dataWeight x) :=
  Readback.sum_neutralSubtype O (Compiled.dataWeight x)

theorem activeWeight_eq_normalized (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ) :
    activeWeight O x = Readback.normalizedActiveWeight O (Compiled.dataWeight x) := by
  funext v
  unfold activeWeight Readback.normalizedActiveWeight
  rw [roleWeight_active]
  rfl

theorem innerProfile_eq_readback (O : LegalObject B V) (phase : Bool)
    (x : Compiled.Vertex b t V → ℝ) (A : FiniteGraph 3) :
    innerProfile O phase x A = A.2.weightedHomDensity (Readback.activeGraph O phase)
      (Readback.normalizedActiveWeight O (Compiled.dataWeight x)) := by
  unfold innerProfile SetFamily.weightedProfile
  rw [activeWeight_eq_normalized]
  rfl

noncomputable def rootMassProduct (b t : ℕ) : ℝ :=
  (1 / (OuterWeights.arity b t : ℝ)) ^ t *
    (3 / (5 * (OuterWeights.arity b t : ℝ))) ^ (5 * b)

theorem rootMassProduct_pos (b t : ℕ) : 0 < rootMassProduct b t := by
  have hr : 0 < (OuterWeights.arity b t : ℝ) := Nat.cast_pos.mpr (OuterWeights.arity_pos b t)
  unfold rootMassProduct
  positivity

theorem rootProduct_optimalWeights (x : V → ℝ) :
    Readback.rootProduct (Compiled.optimalWeights b t x) = rootMassProduct b t := by
  simp only [Readback.rootProduct, Compiled.optimalWeights, Sum.elim_inl, Sum.elim_inr,
    Support.Vertex, Finset.prod_const, Finset.card_univ, Fintype.card_sigma,
    Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm, rootMassProduct]

theorem object_activeMass (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase : Bool) (α : ℝ) :
    (PhaseApproximation.object F G hpos hG phase).activeMass
      (Compiled.dataWeight (PhaseApproximation.weights b t G α)) =
        (4 / (OuterWeights.arity b t : ℝ)) * α := by
  rw [← roleWeight_active, PhaseApproximation.object_roleWeight]
  rfl

theorem object_neutralMass (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase : Bool) (α : ℝ) :
    (PhaseApproximation.object F G hpos hG phase).neutralMass
      (Compiled.dataWeight (PhaseApproximation.weights b t G α)) =
        (4 / (OuterWeights.arity b t : ℝ)) * (1 - α) := by
  rw [← roleWeight_neutral, PhaseApproximation.object_roleWeight]
  rfl

end TuranUniversality.Structural.PhaseRoles
