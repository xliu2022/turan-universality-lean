module

public import TuranUniversality.Computation.OrbitFrames
public import TuranUniversality.Computation.RootedRealization

/-!
# Recovery of genuine halting from an actual closed marked component

This combines the actual J/R/S partial matchings, their closed-component
permutations, wall extraction, the static Start-prefix constraints, and the
proved radius-one reset theorem.  No halting recovery property is assumed.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

open Turing LocalSystem

variable {Γ Λ D : Type*} [Inhabited Γ] [Inhabited Λ]
  [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ] [DecidableEq D]

namespace Realization

variable {M : TM0.Machine Γ Λ} {input : List Γ}
  {A : Realization D (Label Γ Λ)} {a : D}

/-- Total local permutations obtained from the actual finite component,
instantiated with the explicit machine/static/reset local tables. -/
def ClosedDynamics.permutationModel (d : A.ClosedDynamics a)
    (h : A.Legal (specification M input)) :
    PermutationModel M input (A.CellComponent a) where
  H := d.horizontal
  V := d.vertical
  label := d.label
  commute := d.commute h.1
  horizontal := fun x => (mem_horizontal M input _ _).mp (d.horizontal_grammar h.2.2.1 x)
  evolution := fun x => (mem_evolution M input _ _ _ _).mp (d.evolution h.2.1 x)
  input_rule := by
    intro x hx j hj
    have hj' : j < (specification M input).inputPrefix.length := by
      simpa [specification] using hj
    have hh := d.input_prefix h.2.2.2.2 x ((mem_prefixTrigger M input _).mpr hx) j hj'
    exact (mem_inputPrefix M input j hj' _).mp hh

/-- A closed relation component containing a marked cell certifies genuine
ordinary machine halting on the specified exact input. -/
theorem closed_marked_halts (A : Realization D (Label Γ Λ))
    (M : TM0.Machine Γ Λ) (input : List Γ)
    (h : A.Legal (specification M input)) (a : D) (ha : a ∈ A.marks)
    (hc : A.ClosedAt a) : (TM0.eval M input).Dom := by
  obtain ⟨d⟩ := A.closed_dynamics a hc
  let x : A.CellComponent a := ⟨a, A.marks_cells ha, .refl⟩
  have hx := d.marked_initial h.2.2.2.1 x ha
  have hx' : (d.permutationModel h).MarkedAt x :=
    ⟨hx.1, (mem_initial M input _).mp hx.2⟩
  exact (d.permutationModel h).halts_of_marked x hx'

/-- Consequently every marked component of a legal nonhalting input has an
actual missing indexed incidence somewhere in that component. -/
theorem nonhalting_not_closed (A : Realization D (Label Γ Λ))
    (M : TM0.Machine Γ Λ) (input : List Γ)
    (h : A.Legal (specification M input)) (hn : ¬(TM0.eval M input).Dom)
    (a : D) (ha : a ∈ A.marks) : ¬A.ClosedAt a :=
  fun hc => hn (A.closed_marked_halts M input h a ha hc)

end Realization

end TuranUniversality.Computation.MatchingSystem
