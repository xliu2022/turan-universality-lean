module

public import TuranUniversality.Density.SetFamilyExtremal

@[expose] public section

/-! # Finite-subfamily approximation of an arbitrary Turán density

At a fixed host order, only finitely many forbidden graphs can embed. This
gives the infimum formula directly from ordinary extremal numbers, without
using a limit-space realization theorem. Increasing finite enumerations of
the family consequently have densities converging to its actual density.
-/

open Filter Topology

namespace TuranUniversality.SetFamily

noncomputable section

variable {r : ℕ}

def finiteDensityValues (F : Set (FiniteGraph r)) : Set ℝ :=
  {z | ∃ E : Finset (FiniteGraph r), (E : Set (FiniteGraph r)) ⊆ F ∧
    z = familyTuranDensity E}

theorem finiteDensityValues_nonempty (F : Set (FiniteGraph r)) :
    (finiteDensityValues F).Nonempty :=
  ⟨familyTuranDensity ∅, ∅, by simp, rfl⟩

theorem finiteDensityValues_bddBelow (F : Set (FiniteGraph r)) :
    BddBelow (finiteDensityValues F) := by
  refine ⟨0, ?_⟩
  rintro z ⟨E, _, rfl⟩
  exact familyTuranDensity_nonneg E

theorem turanDensity_le_finite (F : Set (FiniteGraph r)) (E : Finset (FiniteGraph r))
    (hE : (E : Set (FiniteGraph r)) ⊆ F) : turanDensity F ≤ familyTuranDensity E := by
  simpa only [turanDensity_finset] using turanDensity_antitone hE

/-- The density of an arbitrary family is the infimum over all of its
finite subfamilies, also when an edgeless graph is forbidden. -/
theorem turanDensity_eq_sInf_finite (F : Set (FiniteGraph r)) :
    turanDensity F = sInf (finiteDensityValues F) := by
  apply le_antisymm
  · apply le_csInf (finiteDensityValues_nonempty F)
    rintro z ⟨E, hE, rfl⟩
    exact turanDensity_le_finite F E hE
  · apply le_ciInf
    intro n
    calc
      sInf (finiteDensityValues F) ≤ familyTuranDensity (truncate F (n + r)) :=
        csInf_le (finiteDensityValues_bddBelow F)
          ⟨truncate F (n + r), truncate_subset F (n + r), rfl⟩
      _ ≤ familyExtremalDensity (truncate F (n + r)) (n + r) :=
        familyTuranDensity_le_extremalDensity _ (by omega)
      _ = extremalDensity F (n + r) := by
        rw [familyExtremalDensity, extremalDensity, extremalNumber_truncate]

theorem finite_subset_stage (F : Set (FiniteGraph r))
    (stage : ℕ → Finset (FiniteGraph r)) (hmono : Monotone stage)
    (hcover : ∀ A, A ∈ F ↔ ∃ n, A ∈ stage n)
    (E : Finset (FiniteGraph r)) (hE : (E : Set (FiniteGraph r)) ⊆ F) :
    ∃ n, E ⊆ stage n := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert A E hnot ih =>
    obtain ⟨s, hs⟩ := (hcover A).mp (hE (by simp))
    obtain ⟨t, ht⟩ := ih (fun B hB => hE (Finset.mem_insert_of_mem hB))
    refine ⟨max s t, ?_⟩
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hmono (Nat.le_max_left s t) hs
    · exact hmono (Nat.le_max_right s t) (ht hB)

theorem stage_density_antitone (stage : ℕ → Finset (FiniteGraph r))
    (hmono : Monotone stage) : Antitone (fun n => familyTuranDensity (stage n)) := by
  intro n m hnm
  simpa only [turanDensity_finset] using
    turanDensity_antitone (show (stage n : Set (FiniteGraph r)) ⊆ stage m from hmono hnm)

theorem stage_density_bddBelow (stage : ℕ → Finset (FiniteGraph r)) :
    BddBelow (Set.range (fun n => familyTuranDensity (stage n))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact familyTuranDensity_nonneg _⟩

theorem turanDensity_eq_iInf_exhaustion (F : Set (FiniteGraph r))
    (stage : ℕ → Finset (FiniteGraph r)) (hmono : Monotone stage)
    (hcover : ∀ A, A ∈ F ↔ ∃ n, A ∈ stage n) :
    turanDensity F = ⨅ n, familyTuranDensity (stage n) := by
  apply le_antisymm
  · apply le_ciInf
    intro n
    exact turanDensity_le_finite F (stage n) (fun A hA => (hcover A).mpr ⟨n, hA⟩)
  · rw [turanDensity_eq_sInf_finite]
    apply le_csInf (finiteDensityValues_nonempty F)
    rintro z ⟨E, hE, rfl⟩
    obtain ⟨n, hn⟩ := finite_subset_stage F stage hmono hcover E hE
    apply (ciInf_le (stage_density_bddBelow stage) n).trans
    simpa only [turanDensity_finset] using
      turanDensity_antitone (show (E : Set (FiniteGraph r)) ⊆ stage n from hn)

/-- Density convergence for any increasing finite enumeration of the family.
No computable rate of convergence is asserted. -/
theorem turanDensity_tendsto_of_exhaustion (F : Set (FiniteGraph r))
    (stage : ℕ → Finset (FiniteGraph r)) (hmono : Monotone stage)
    (hcover : ∀ A, A ∈ F ↔ ∃ n, A ∈ stage n) :
    Tendsto (fun n => familyTuranDensity (stage n)) atTop (𝓝 (turanDensity F)) := by
  rw [turanDensity_eq_iInf_exhaustion F stage hmono hcover]
  exact tendsto_atTop_ciInf (stage_density_antitone stage hmono) (stage_density_bddBelow stage)

theorem turanDensity_tendsto_truncate (F : Set (FiniteGraph r)) :
    Tendsto (fun n => familyTuranDensity (truncate F n)) atTop (𝓝 (turanDensity F)) := by
  apply turanDensity_tendsto_of_exhaustion F (truncate F) (fun _ _ h => truncate_mono F h)
  intro A
  constructor
  · intro hA
    exact ⟨A.1, (mem_truncate F A.1 A).mpr ⟨le_rfl, hA⟩⟩
  · rintro ⟨n, hn⟩
    exact (mem_truncate F n A).mp hn |>.2

end
end TuranUniversality.SetFamily
