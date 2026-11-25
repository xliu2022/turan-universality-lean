module

public import TuranUniversality.Structural.NeutralModels
public import TuranUniversality.Structural.NeutralConvergence
public import TuranUniversality.Hypergraph.PartitionRounding

@[expose] public section

open scoped BigOperators

namespace TuranUniversality.Structural.NeutralRoles

open Density

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem roleWeight_pushforward (ρ : V → Option (Rooted.Roots b t)) (x : V → ℝ) :
    roleWeight (pushforwardWeight (Rooted.place ρ) x) =
      pushforwardWeight (roleOfRooting ρ) x := by
  classical
  funext a
  rcases a with (i | j) | a
  · simp only [roleWeight, PhaseRoles.rootVertex, pushforwardWeight_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro v _
    cases h : ρ v with
    | none => simp [roleOfRooting, Rooted.place, Selector.rootedVertex, h]
    | some r => cases r <;> simp [roleOfRooting, Rooted.place, Selector.rootedVertex, h]
  · simp only [roleWeight, PhaseRoles.rootVertex, pushforwardWeight_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro v _
    cases h : ρ v with
    | none => simp [roleOfRooting, Rooted.place, Selector.rootedVertex, h]
    | some r => cases r <;> simp [roleOfRooting, Rooted.place, Selector.rootedVertex, h]
  · cases a
    simp only [roleWeight, Compiled.dataMass, Compiled.dataWeight, pushforwardWeight_eq_sum_ite]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    cases h : ρ v with
    | none => simp [roleOfRooting, Rooted.place, Selector.rootedVertex, h]
    | some r => cases r <;> simp [roleOfRooting, Rooted.place, Selector.rootedVertex, h]

theorem roleWeight_uniform (ρ : V → Option (Rooted.Roots b t)) (a : Role b t) :
    roleWeight (pushforwardWeight (Rooted.place ρ)
      (fun _ : V => (Fintype.card V : ℝ)⁻¹)) a =
      (PartitionRounding.fiberSize (roleOfRooting ρ) a : ℝ) / Fintype.card V := by
  rw [roleWeight_pushforward]
  simp [pushforwardWeight, Fintype.card_subtype, PartitionRounding.fiberSize, div_eq_mul_inv]

end TuranUniversality.Structural.NeutralRoles
