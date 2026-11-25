module

public import TuranUniversality.Structural.EffectiveUniversality
public import TuranUniversality.Density.FiniteProfileRelabel
public import TuranUniversality.RegistryStructuralStatement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

/-! # Numbered fixed roles and the exact public phase statements -/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.Fixed

open Density Computation

noncomputable def roleCount (t : ℕ) : ℕ := Fintype.card (NeutralRoles.Role blockCount t)

noncomputable def roleEquiv (t : ℕ) : NeutralRoles.Role blockCount t ≃ Fin (roleCount t) :=
  Fintype.equivFin _

noncomputable def numberedPattern (t : ℕ) :
    FiniteRolePattern (Fin (roleCount t)) (t + uniformityThreshold) :=
  (neutralPattern t).relabel (roleEquiv t)

noncomputable def numberedWeight (t : ℕ) : Fin (roleCount t) → ℝ :=
  pushforwardWeight (roleEquiv t) (neutralWeight t)

noncomputable def numberedCounts (t n : ℕ) (a : Fin (roleCount t)) : ℕ :=
  NeutralRoles.targetCounts blockCount t n ((roleEquiv t).symm a)

theorem roleCount_pos (t : ℕ) : 0 < roleCount t :=
  Fintype.card_pos_iff.mpr ⟨Sum.inr ()⟩

theorem numberedWeight_probability (t : ℕ) : ProbabilityWeights (numberedWeight t) :=
  pushforwardWeight_probability _ _ (neutralWeight_probability t)

theorem numbered_profile (t : ℕ) :
    (numberedPattern t).profile (numberedWeight t) = neutralProfile t :=
  FiniteRolePattern.profile_relabel _ _ _

theorem numberedCounts_balanced (t : ℕ) :
    Registry.Structural.BalancedCounts (numberedWeight t) (numberedCounts t) := by
  intro n
  constructor
  · unfold numberedCounts
    rw [Equiv.sum_comp]
    exact NeutralRoles.targetCounts_sum blockCount t n
  · intro a
    simp only [numberedWeight, FiniteRolePattern.pushforward_equiv]
    exact NeutralRoles.targetCounts_floor_ceil blockCount t n ((roleEquiv t).symm a)

theorem numbered_stable (t : ℕ) (β : BinaryWord) (hβ : ¬ WordHalts β) :
    Registry.Structural.StableWithPattern (outerFamily t β)
      (numberedPattern t) (numberedCounts t) := by
  intro n G hn hsize hG hlim
  obtain ⟨θ, hθ, hedge⟩ := nonhalting_finite_profile t β hβ G hG
    (by simpa only [Fintype.card_fin] using hn) atTop
    (by simpa only [Fintype.card_fin] using hsize) hlim
  refine ⟨fun i => roleEquiv t ∘ θ i, ?_, ?_⟩
  · intro i a
    rw [FiniteRolePattern.fiberSize_relabel, hθ]
    simp only [numberedCounts, Fintype.card_fin]
  · simpa only [numberedPattern, FiniteRolePattern.graph_relabel] using hedge

theorem single_twoPhases (g : Effective.GraphCode)
    (hg : ∀ A ∈ ({Effective.decodeGraphCode g} : Finset (FiniteGraph 3)), A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity {Effective.decodeGraphCode g}) :
    Registry.Structural.TwoPhases
      (Ordinary.forbidden {Effective.decodeGraphCode g} (CodePools.pool p q hpq) t)
      (Effective.decodeGraphCode g)
      (Separation.test p q hpq hq t false) (Separation.test p q hpq hq t true) := by
  obtain ⟨heq, hdis, hc, hs⟩ := Ordinary.positive_phases {Effective.decodeGraphCode g} hg
    p q hpq hq t hz
  refine ⟨_, hc, Ordinary.phase {Effective.decodeGraphCode g} p q hpq t,
    heq, hdis, ?_, ⟨Ordinary.positiveHomeomorph {Effective.decodeGraphCode g} hg
      p q hpq hq t hz⟩⟩
  intro s
  obtain ⟨hcompact, hne, hhome, hsep⟩ := hs s
  exact ⟨hcompact, hne, hhome, hsep⟩

theorem halting_twoPhases (t : ℕ) (β : BinaryWord) (hβ : WordHalts β) :
    Registry.Structural.TwoPhases (outerFamily t β)
      (Effective.decodeGraphCode (forbiddenCompiler β)) (test t false) (test t true) :=
  single_twoPhases (forbiddenCompiler β) (inner_has_edges β)
    numerator denominator numerator_le_denominator denominator_pos t
    ((inner_density_gt_iff β).mpr hβ)

end TuranUniversality.Structural.Fixed
