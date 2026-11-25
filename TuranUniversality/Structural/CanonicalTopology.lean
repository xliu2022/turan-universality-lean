module

public import TuranUniversality.Structural.CanonicalClassification

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A homeomorphism from two entire inner extremal spaces

The domain is the product of the discrete two-point space with the complete
inner extremal space. The map is the actual finite-coordinate phase map;
its inverse is supplied by compactness after readback proves injectivity.
-/

namespace TuranUniversality.Structural.CanonicalProfiles

noncomputable def phasePairMap (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    Bool × SetFamily.extremalProfiles F → extremal F (CodePools.pool p q hpq) t p q :=
  fun z => ⟨PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq)
    z.1 p q (familyTuranDensity F) z.2.val,
    phase_mem F (CodePools.pool p q hpq) z.1 p q (Nat.cast_nonneg _)
      (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz (CodePools.pool_card_cast p q hpq hq)
      z.2.val z.2.property⟩

theorem phasePairMap_injective (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    Function.Injective (phasePairMap F p q hpq hq t hz) := by
  rintro ⟨a, W⟩ ⟨c, Z⟩ heq
  have he := congrArg Subtype.val heq
  change PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) a p q
    (familyTuranDensity F) W.val =
      PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) c p q
        (familyTuranDensity F) Z.val at he
  have hWmem : PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) a p q
      (familyTuranDensity F) W.val ∈
      PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) a p q
        (familyTuranDensity F) '' SetFamily.extremalProfiles F := ⟨W.val, W.property, rfl⟩
  have hZmem : PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) a p q
      (familyTuranDensity F) W.val ∈
      PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) c p q
        (familyTuranDensity F) '' SetFamily.extremalProfiles F := ⟨Z.val, Z.property, he.symm⟩
  have hac : a = c := by
    by_contra hn
    have hd := PhaseRoles.phaseImages_disjoint F p q hpq hq t hz
    cases a <;> cases c
    · exact hn rfl
    · exact Set.disjoint_left.mp hd hWmem hZmem
    · exact Set.disjoint_left.mp hd hZmem hWmem
    · exact hn rfl
  subst c
  have hWZ := PhaseRoles.extremalPhaseMap_injOn F p q hpq hq t a hz W.property Z.property he
  exact Prod.ext rfl (Subtype.ext hWZ)

theorem phasePairMap_surjective (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    Function.Surjective (phasePairMap F p q hpq hq t hz) := by
  intro W
  obtain ⟨phase, U, hU, he⟩ := positive_exhaustion F hedges (CodePools.pool p q hpq)
    p q (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) W.val W.property
  exact ⟨⟨phase, ⟨U, hU⟩⟩, Subtype.ext he.symm⟩

theorem continuous_phasePairMap (F : Finset (FiniteGraph 3))
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    Continuous (phasePairMap F p q hpq hq t hz) := by
  apply continuous_prod_of_discrete_left.mpr
  intro phase
  exact ((PhaseRoles.continuous_extremalPhaseMap (CodePools.pool p q hpq) phase p q
    (familyTuranDensity F)).comp continuous_subtype_val).subtype_mk
      (fun W => phase_mem F (CodePools.pool p q hpq) phase p q (Nat.cast_nonneg _)
        (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz (CodePools.pool_card_cast p q hpq hq)
        W.val W.property)

noncomputable def positiveHomeomorph (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    (Bool × SetFamily.extremalProfiles F) ≃ₜ extremal F (CodePools.pool p q hpq) t p q := by
  letI : CompactSpace (SetFamily.extremalProfiles F) :=
    isCompact_iff_compactSpace.mp (SetFamily.isCompact_extremalProfiles F)
  let e := Equiv.ofBijective (phasePairMap F p q hpq hq t hz)
    ⟨phasePairMap_injective F p q hpq hq t hz, phasePairMap_surjective F hedges p q hpq hq t hz⟩
  have he : Continuous e := continuous_phasePairMap F p q hpq hq t hz
  exact he.homeoOfEquivCompactToT2

end TuranUniversality.Structural.CanonicalProfiles
