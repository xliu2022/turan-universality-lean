module

public import TuranUniversality.Density.FamilyExtremal

@[expose] public section

/-! # Families containing an edgeless forbidden graph

The ordinary extremal-number convention returns zero if there is no free host.
An edgeless forbidden graph embeds in every sufficiently large host, so these
families have density zero.  This lets the effective approximation algorithm
keep every input code, without silently discarding an edgeless forbidden graph.
-/

namespace TuranUniversality

variable {r : ℕ}

theorem not_familyFree_of_edgeless (F : Finset (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (hempty : A.2.edges = ∅)
    {n : ℕ} (hn : A.1 ≤ n) (G : RGraph (Fin n) r) :
    ¬ familyFree F G := by
  intro hfree
  apply hfree A hA
  refine ⟨Fin.castLE hn, Fin.castLE_injective hn, ?_⟩
  intro e he
  simp [hempty] at he

theorem familyExtremalNumber_eq_zero_of_edgeless (F : Finset (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (hempty : A.2.edges = ∅)
    {n : ℕ} (hn : A.1 ≤ n) : familyExtremalNumber F n = 0 := by
  classical
  unfold familyExtremalNumber
  apply Nat.findGreatest_eq_zero_iff.mpr
  intro k _hk _hkn h
  obtain ⟨G, hfree, _⟩ := h
  exact not_familyFree_of_edgeless F hA hempty hn G hfree

theorem familyTuranDensity_eq_zero_of_edgeless (F : Finset (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (hempty : A.2.edges = ∅) :
    familyTuranDensity F = 0 := by
  apply le_antisymm _ (familyTuranDensity_nonneg F)
  calc
    familyTuranDensity F ≤ familyExtremalDensity F (A.1 + r) :=
      familyTuranDensity_le_extremalDensity F (by omega)
    _ = 0 := by
      rw [familyExtremalDensity,
        familyExtremalNumber_eq_zero_of_edgeless F hA hempty (by omega)]
      simp

theorem familyTuranDensity_eq_zero_of_not_nonempty (F : Finset (FiniteGraph r))
    (h : ¬ ∀ A ∈ F, A.2.edges.Nonempty) : familyTuranDensity F = 0 := by
  classical
  push Not at h
  obtain ⟨A, hA, hempty⟩ := h
  exact familyTuranDensity_eq_zero_of_edgeless F hA hempty

end TuranUniversality
