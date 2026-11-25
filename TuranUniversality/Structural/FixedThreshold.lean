module

public import TuranUniversality.Reduction.Universality
public import TuranUniversality.Structural.OrdinaryPhases
public import TuranUniversality.Structural.NeutralFiniteProfile

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

/-! # The fixed structural parameters and the literal binary input family

The threshold is the already proved fixed rational of Theorem 1.1. The
inner graph is the same actual singleton compiler, including its isolated
vertices. No substitute halting predicate is introduced.
-/

namespace TuranUniversality.Structural.Fixed

open TuranUniversality.Computation Effective

theorem positive_rat_nat_fraction (τ : ℚ) (hτ : 0 < τ) (hτ1 : τ < 1) :
    0 < τ.num.natAbs ∧ τ.num.natAbs < τ.den ∧
      ((τ.num.natAbs : ℕ) : ℝ) / τ.den = (τ : ℝ) := by
  have hnum : 0 < τ.num := Rat.num_pos.mpr hτ
  have hnumcast : (τ.num.natAbs : ℤ) = τ.num := Int.natAbs_of_nonneg hnum.le
  have hnumRat : ((τ.num.natAbs : ℕ) : ℚ) = (τ.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hnumcast
  have hval : ((τ.num.natAbs : ℕ) : ℚ) / τ.den = τ := by
    rw [hnumRat, Rat.num_div_den]
  have hlt : ((τ.num.natAbs : ℕ) : ℚ) < τ.den := by
    apply (div_lt_one (show (0 : ℚ) < τ.den by exact_mod_cast τ.den_pos)).mp
    rw [hval]
    exact hτ1
  refine ⟨Int.natAbs_pos.mpr (ne_of_gt hnum), by exact_mod_cast hlt, ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun z : ℚ => (z : ℝ)) hval

noncomputable def numerator : ℕ := tau3.num.natAbs
noncomputable def denominator : ℕ := tau3.den

theorem numerator_pos : 0 < numerator := (positive_rat_nat_fraction tau3 tau3_bounds.1 tau3_bounds.2).1
theorem numerator_lt_denominator : numerator < denominator :=
  (positive_rat_nat_fraction tau3 tau3_bounds.1 tau3_bounds.2).2.1
theorem denominator_pos : 0 < denominator := tau3.den_pos
theorem numerator_le_denominator : numerator ≤ denominator := numerator_lt_denominator.le
theorem fraction_eq : (numerator : ℝ) / denominator = (tau3 : ℝ) :=
  (positive_rat_nat_fraction tau3 tau3_bounds.1 tau3_bounds.2).2.2

noncomputable def blockCount : ℕ := CodePools.blockCount denominator
noncomputable def uniformityThreshold : ℕ := 3 * blockCount + 4
noncomputable def pools : Label → Finset (Cube.Word blockCount) :=
  CodePools.pool numerator denominator numerator_le_denominator

noncomputable def innerFamily (β : BinaryWord) : Finset (FiniteGraph 3) :=
  {decodeGraphCode (forbiddenCompiler β)}

theorem singleton_code_density (g : GraphCode) :
    familyTuranDensity ({decodeGraphCode g} : Finset (FiniteGraph 3)) = turanDensity (decodeGraph g) :=
  familyTuranDensity_singleton (decodeGraphCode g)

theorem singleton_code_has_edges (g : GraphCode) (hg : (decodeGraph g).edges.Nonempty) :
    ∀ A ∈ ({decodeGraphCode g} : Finset (FiniteGraph 3)), A.2.edges.Nonempty := by
  intro A hA
  have he : A = decodeGraphCode g := Finset.mem_singleton.mp hA
  subst A
  exact hg

theorem inner_has_edges (β : BinaryWord) : ∀ A ∈ innerFamily β, A.2.edges.Nonempty :=
  singleton_code_has_edges (forbiddenCompiler β) (forbiddenCompiler_has_edges β)

theorem inner_density_eq_iff (β : BinaryWord) :
    familyTuranDensity (innerFamily β) = (numerator : ℝ) / denominator ↔ ¬ WordHalts β := by
  rw [fraction_eq, innerFamily, singleton_code_density]
  exact forbiddenCompiler_density_eq_iff β

theorem inner_density_gt_iff (β : BinaryWord) :
    (numerator : ℝ) / denominator < familyTuranDensity (innerFamily β) ↔ WordHalts β := by
  rw [fraction_eq, innerFamily, singleton_code_density]
  exact forbiddenCompiler_density_strict_iff β

theorem inner_density_ge (β : BinaryWord) :
    (numerator : ℝ) / denominator ≤ familyTuranDensity (innerFamily β) := by
  classical
  by_cases hh : WordHalts β
  · exact ((inner_density_gt_iff β).mpr hh).le
  · exact ((inner_density_eq_iff β).mpr hh).ge

noncomputable def outerFamily (t : ℕ) (β : BinaryWord) :
    Finset (FiniteGraph (t + (3 * blockCount + 4))) := Ordinary.forbidden (innerFamily β) pools t

noncomputable def test (t : ℕ) (s : Bool) : FiniteGraph (t + (3 * blockCount + 4)) :=
  Separation.test numerator denominator numerator_le_denominator denominator_pos t s

noncomputable def neutralPattern (t : ℕ) :
    FiniteRolePattern (NeutralRoles.Role blockCount t) (t + (3 * blockCount + 4)) :=
  NeutralRoles.pattern pools

noncomputable def neutralWeight (t : ℕ) : NeutralRoles.Role blockCount t → ℝ :=
  NeutralRoles.optimalRoleWeight blockCount t

noncomputable def neutralProfile (t : ℕ) : SetFamily.Profile (t + (3 * blockCount + 4)) :=
  (neutralPattern t).profile (neutralWeight t)

theorem neutralWeight_probability (t : ℕ) : ProbabilityWeights (neutralWeight t) :=
  NeutralRoles.optimalRoleWeight_probability blockCount t

theorem neutralProfile_eq (t : ℕ) : neutralProfile t = NeutralRoles.neutralProfile pools t :=
  NeutralRoles.pattern_profile pools _

theorem nonhalting_profiles (t : ℕ) (β : BinaryWord) (h : ¬ WordHalts β) :
    SetFamily.extremalProfiles (outerFamily t β) = {neutralProfile t} := by
  rw [neutralProfile_eq]
  exact Ordinary.zero_profile_classification_actual (innerFamily β) (inner_has_edges β)
    numerator denominator numerator_le_denominator denominator_pos t ((inner_density_eq_iff β).mpr h)

theorem neutral_separator (t : ℕ) :
    neutralProfile t (test t false) - neutralProfile t (test t true) = 0 := by
  rw [neutralProfile_eq]
  exact Separation.neutral_separator numerator denominator numerator_le_denominator denominator_pos t

noncomputable def haltingHomeomorph (t : ℕ) (β : BinaryWord) (h : WordHalts β) :
    (Bool × SetFamily.extremalProfiles (innerFamily β)) ≃ₜ
      SetFamily.extremalProfiles (outerFamily t β) :=
  Ordinary.positiveHomeomorph (innerFamily β) (inner_has_edges β)
    numerator denominator numerator_le_denominator denominator_pos t ((inner_density_gt_iff β).mpr h)

end TuranUniversality.Structural.Fixed
