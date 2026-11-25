module

public import TuranUniversality.Structural.NeutralStability
public import TuranUniversality.Structural.NeutralImage
public import TuranUniversality.Density.FiniteProfiles
public import TuranUniversality.Density.FiniteProfileRounding

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The fixed finite-profile limit and exact integer realizations

The coordinate definition, actual finite pattern, and prescribed rounded
class sizes refer to the same model. Its four neutral occurrences on an
edge are retained in the multiset semantics.
-/

open Filter Topology

namespace TuranUniversality.Structural.NeutralRoles

open Density

variable {U : Type*} [DecidableEq U] [Fintype U] {b t : ℕ}

theorem pattern_coordinate (Ω : Label → Finset (Cube.Word b))
    (H : RGraph U (t + (3 * b + 4))) (z : Role b t → ℝ) :
    (pattern Ω).coordinate H z = coordinate Ω H z := by
  unfold FiniteRolePattern.coordinate coordinate
  apply weightedMean_congr
  intro θ
  congr 1
  apply propext
  have h1 := (pattern Ω).compatible_iff_of_injective H θ id Function.injective_id
  simp only [Function.comp_id] at h1
  rw [← graph_eq_pattern Ω θ, graph, RGraph.isHom_inverseImage_iff] at h1
  simp only [Function.comp_id] at h1
  have h2 := sampled_compatible_iff (B := ∅) (by simp) θ id Function.injective_id Ω H
  exact h1.trans h2.symm

theorem pattern_profile (Ω : Label → Finset (Cube.Word b)) (z : Role b t → ℝ) :
    (pattern Ω).profile z = profile Ω z := by
  funext H
  exact pattern_coordinate Ω H.2 z

theorem neutralProfile_eq_pattern (Ω : Label → Finset (Cube.Word b)) (t : ℕ) :
    neutralProfile Ω t = (pattern Ω).profile (optimalRoleWeight b t) :=
  (pattern_profile Ω _).symm

noncomputable def targetCounts (b t n : ℕ) : Role b t → ℕ :=
  FiniteRolePattern.roundedCounts (optimalRoleWeight b t) (optimalRoleWeight_probability b t) n

theorem targetCounts_sum (b t n : ℕ) : ∑ a, targetCounts b t n a = n :=
  FiniteRolePattern.roundedCounts_sum _ _ n

theorem targetCounts_floor_ceil (b t n : ℕ) (a : Role b t) :
    targetCounts b t n a = ⌊(n : ℝ) * optimalRoleWeight b t a⌋₊ ∨
      targetCounts b t n a = ⌈(n : ℝ) * optimalRoleWeight b t a⌉₊ :=
  FiniteRolePattern.roundedCounts_floor_ceil _ _ n a

theorem targetCounts_error (b t n : ℕ) (a : Role b t) :
    |(targetCounts b t n a : ℝ) - n * optimalRoleWeight b t a| ≤ Fintype.card (Role b t) :=
  FiniteRolePattern.roundedCounts_error _ _ n a

end NeutralRoles

namespace Ordinary

universe u v

theorem zero_finite_profile_rounded
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : familyTuranDensity F = (p : ℝ) / q)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * CodePools.blockCount q + 4)))
    (hG : ∀ i, familyFree (forbidden F (CodePools.pool p q hpq) t) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l
      (𝓝 (optimum F (CodePools.blockCount q) t p q))) :
    ∃ θ : ∀ i, V i → NeutralRoles.Role (CodePools.blockCount q) t,
      (∀ i a, PartitionRounding.fiberSize (θ i) a =
        NeutralRoles.targetCounts (CodePools.blockCount q) t (Fintype.card (V i)) a) ∧
      Tendsto (fun i => (G i).normalizedEditDistance
        ((NeutralRoles.pattern (CodePools.pool p q hpq)).graph (θ i))) l (𝓝 0) := by
  obtain ⟨ρ, hρ, hGρ⟩ := zero_finite_profile_approximation F hedges p q hpq hq t hz
    G hG hn l hsize hlim
  obtain ⟨σ, hσ, _, hρσ⟩ := (NeutralRoles.pattern (CodePools.pool p q hpq)).round_presentations
    (by omega) ρ hn l hsize (NeutralRoles.optimalRoleWeight (CodePools.blockCount q) t)
    (NeutralRoles.optimalRoleWeight_probability (CodePools.blockCount q) t) hρ
  exact ⟨σ, hσ, RGraph.normalizedEditDistance_tendsto_zero_trans G _ _ l hGρ hρσ⟩

end Ordinary
end TuranUniversality.Structural
