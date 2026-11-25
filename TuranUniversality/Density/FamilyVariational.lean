module

public import TuranUniversality.Density.FamilyHomUpper
public import TuranUniversality.Density.HomFreeMax

@[expose] public section

/-! # The hom-free variational formula for a finite forbidden family

All real probability weightings are included.  The right-hand side is the
supremum of the normalized edge polynomials of actual finite hom-free graphs.
The proof uses the ordinary Turán density, not an alternative definition of it.
-/

namespace TuranUniversality

variable {r : ℕ}

def familyWeightedValues (F : Finset (FiniteGraph r)) : Set ℝ :=
  {z | ∃ (m : ℕ) (G : RGraph (Fin m) r) (x : Fin m → ℝ),
    familyHomFree F G ∧ ProbabilityWeights x ∧
    z = (r.factorial : ℝ) * G.edgePolynomial x}

theorem zero_mem_familyWeightedValues (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    0 ∈ familyWeightedValues F := by
  refine ⟨1, RGraph.empty (Fin 1) r, fun _ => (Fintype.card (Fin 1) : ℝ)⁻¹,
    familyHomFree_empty F hedges 1, probabilityWeights_uniform, ?_⟩
  simp [RGraph.edgePolynomial, RGraph.empty]

theorem familyWeightedValues_bddAbove (F : Finset (FiniteGraph r)) :
    BddAbove (familyWeightedValues F) := by
  refine ⟨familyTuranDensity F, ?_⟩
  rintro z ⟨m, G, x, hfree, hx, rfl⟩
  exact familyTuranDensity_lower_of_homFree F G hfree x hx

/-- The finite-family homomorphism--Lagrangian variational identity in
normalized form, with arbitrary real probability weights. -/
theorem familyTuranDensity_eq_sSup_weighted (F : Finset (FiniteGraph r))
    (hr : 0 < r) (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    familyTuranDensity F = sSup (familyWeightedValues F) := by
  have hzero := zero_mem_familyWeightedValues F hedges
  have hbdd := familyWeightedValues_bddAbove F
  have hnonneg : 0 ≤ sSup (familyWeightedValues F) := le_csSup hbdd hzero
  apply le_antisymm
  · apply familyTuranDensity_upper_of_homFree F hedges _ hnonneg
    intro m G hfree
    by_cases hm : m = 0
    · subst m
      simpa [RGraph.oneEdge_homDensity, zero_pow (Nat.ne_of_gt hr)] using hnonneg
    · letI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
      rw [G.oneEdge_homDensity_polynomial]
      apply le_csSup hbdd
      exact ⟨m, G, _, hfree, probabilityWeights_uniform, rfl⟩
  · apply csSup_le ⟨0, hzero⟩
    rintro z ⟨m, G, x, hfree, hx, rfl⟩
    exact familyTuranDensity_lower_of_homFree F G hfree x hx

end TuranUniversality
