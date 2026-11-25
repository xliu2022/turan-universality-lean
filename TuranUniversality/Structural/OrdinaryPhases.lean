module

public import TuranUniversality.Structural.OrdinaryTransfer
public import TuranUniversality.Structural.PhaseSeparator

@[expose] public section

/-! # The complete ordinary extremal space and its two compact phases

This assembly uses the actual finite forbidden family and the ordinary
hom-density compactification. No finite stability assumption remains.
-/

namespace TuranUniversality.Structural.Ordinary

noncomputable def phase (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (t : ℕ) (s : Bool) :
    Set (SetFamily.Profile (t + (3 * CodePools.blockCount q + 4))) :=
  PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) s p q
    (familyTuranDensity F) '' SetFamily.extremalProfiles F

theorem isCompact_phase (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (t : ℕ) (s : Bool) :
    IsCompact (phase F p q hpq t s) :=
  PhaseRoles.isCompact_phaseImage F (CodePools.pool p q hpq) s p q

theorem phase_nonempty (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (t : ℕ) (s : Bool) :
    (phase F p q hpq t s).Nonempty := by
  obtain ⟨W, hW⟩ := SetFamily.extremalProfiles_nonempty F (by omega) hedges
  exact ⟨_, ⟨W, hW, rfl⟩⟩

theorem phase_disjoint (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    Disjoint (phase F p q hpq t false) (phase F p q hpq t true) :=
  PhaseRoles.phaseImages_disjoint F p q hpq hq t hz

noncomputable def phaseHomeomorph (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) (s : Bool)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    SetFamily.extremalProfiles F ≃ₜ phase F p q hpq t s :=
  PhaseRoles.phaseHomeomorph F p q hpq hq t s hz

noncomputable def positiveHomeomorph (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    (Bool × SetFamily.extremalProfiles F) ≃ₜ
      SetFamily.extremalProfiles (forbidden F (CodePools.pool p q hpq) t) :=
  (CanonicalProfiles.positiveHomeomorph F hedges p q hpq hq t hz).trans
    (Homeomorph.setCongr (extremal_eq_canonical_actual F hedges p q hpq hq t hz.le).symm)

theorem separator_on_phase (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) (s : Bool)
    (W : SetFamily.Profile (t + (3 * CodePools.blockCount q + 4)))
    (hW : W ∈ phase F p q hpq t s) :
    Separation.separator p q hpq hq t W =
      if s then -Separation.value p q t (familyTuranDensity F)
      else Separation.value p q t (familyTuranDensity F) := by
  obtain ⟨U, hU, rfl⟩ := hW
  exact Separation.phase_separator F p q hpq hq t hz s U hU

theorem positive_phases (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    SetFamily.extremalProfiles (forbidden F (CodePools.pool p q hpq) t) =
        phase F p q hpq t false ∪ phase F p q hpq t true ∧
      Disjoint (phase F p q hpq t false) (phase F p q hpq t true) ∧
      0 < Separation.value p q t (familyTuranDensity F) ∧
      ∀ s, IsCompact (phase F p q hpq t s) ∧ (phase F p q hpq t s).Nonempty ∧
        Nonempty (SetFamily.extremalProfiles F ≃ₜ phase F p q hpq t s) ∧
        ∀ W ∈ phase F p q hpq t s,
          Separation.separator p q hpq hq t W =
            if s then -Separation.value p q t (familyTuranDensity F)
            else Separation.value p q t (familyTuranDensity F) := by
  refine ⟨positive_profile_classification_actual F hedges p q hpq hq t hz,
    phase_disjoint F p q hpq hq t hz,
    Separation.value_pos p q t _ hz, ?_⟩
  intro s
  exact ⟨isCompact_phase F p q hpq t s, phase_nonempty F hedges p q hpq t s,
    ⟨phaseHomeomorph F p q hpq hq t s hz⟩,
    fun W hW => separator_on_phase F p q hpq hq t hz s W hW⟩

end TuranUniversality.Structural.Ordinary
