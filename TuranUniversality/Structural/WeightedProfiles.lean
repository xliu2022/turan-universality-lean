module

public import TuranUniversality.Structural.WeightedBlowups
public import TuranUniversality.Density.FreeRealization
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Weighted profiles live in the ordinary dense limit space

Positive integer clone counts approximate every real probability weighting.
Their ordinary homomorphism-density vectors converge coordinatewise to the
actual weighted vector. No replacement definition of the dense limit space
is used: the target is `SetFamily.IsLimitProfile`.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.WeightedProfile

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

noncomputable def cloneCount (x : V → ℝ) (n : ℕ) (v : V) : ℕ :=
  ⌊x v * (n : ℝ)⌋₊ + 1

theorem cloneCount_pos (x : V → ℝ) (n : ℕ) (v : V) : 0 < cloneCount x n v := by
  exact Nat.zero_lt_succ _

noncomputable def cloneWeight (x : V → ℝ) (n : ℕ) (v : V) : ℝ :=
  (cloneCount x n v : ℝ) / (∑ w, cloneCount x n w : ℕ)

theorem cloneCount_ratio_tendsto (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (v : V) :
    Tendsto (fun n : ℕ => (cloneCount x n v : ℝ) / n) atTop (𝓝 (x v)) := by
  have hf := (tendsto_nat_floor_mul_div_atTop (hx v)).comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [cloneCount, Nat.cast_add, Nat.cast_one, add_div, one_div, add_zero,
    Function.comp_apply] using hf.add hi

theorem cloneCount_sum_ratio_tendsto (x : V → ℝ) (hx : ProbabilityWeights x) :
    Tendsto (fun n : ℕ => ((∑ v, cloneCount x n v : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h := tendsto_finsetSum (Finset.univ : Finset V)
    (fun v _ => cloneCount_ratio_tendsto x hx.1 v)
  simpa only [← Finset.sum_div, ← Nat.cast_sum, hx.2] using h

theorem cloneWeight_tendsto (x : V → ℝ) (hx : ProbabilityWeights x) :
    Tendsto (cloneWeight x) atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro v
  have h := (cloneCount_ratio_tendsto x hx.1 v).div
    (cloneCount_sum_ratio_tendsto x hx) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change ((cloneCount x n v : ℝ) / n) / (((∑ w, cloneCount x n w : ℕ) : ℝ) / n) = _
  rw [div_div_div_cancel_right₀ hn0]
  rfl

theorem cloneCount_sum_pos [Nonempty V] (x : V → ℝ) (n : ℕ) :
    0 < ∑ v, cloneCount x n v := by
  exact Finset.sum_pos (fun v _ => cloneCount_pos x n v) Finset.univ_nonempty

end TuranUniversality.Structural.WeightedProfile

namespace TuranUniversality.SetFamily

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

noncomputable def weightedProfile (G : RGraph V r) (x : V → ℝ) : Profile r :=
  fun A => A.2.weightedHomDensity G x

theorem continuous_weightedProfile (G : RGraph V r) :
    Continuous (weightedProfile G) := by
  apply continuous_pi
  intro A
  exact A.2.continuous_weightedHomDensity G

theorem weightedProfile_uniform (G : FiniteGraph r) :
    weightedProfile G.2 (fun _ => (G.1 : ℝ)⁻¹) = profile G := by
  funext A
  simpa only [weightedProfile, profile, Fintype.card_fin] using A.2.weightedHomDensity_uniform G.2

theorem profile_blowup_tendsto (G : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x) :
    Tendsto (fun n => profile (FiniteGraph.ofRGraph
      (G.blowup (Structural.WeightedProfile.cloneCount x n)))) atTop (𝓝 (weightedProfile G x)) := by
  have h := (continuous_weightedProfile G).tendsto x |>.comp
    (Structural.WeightedProfile.cloneWeight_tendsto x hx)
  convert h using 1
  funext n A
  exact (A.2.homDensity_ofRGraph _).trans (A.2.homDensity_blowup _ _)

/-- Every actual finite real-weight probability template has an ordinary
dense limit profile, including when some vertex weights are zero. -/
theorem isLimitProfile_weighted (G : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x) :
    IsLimitProfile (weightedProfile G x) := by
  classical
  have hs : (∑ v, x v) ≠ 0 := by rw [hx.2]; norm_num
  obtain ⟨v, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  letI : Nonempty V := ⟨v⟩
  apply isClosed_closure.mem_of_tendsto (profile_blowup_tendsto G x hx)
  apply Eventually.of_forall
  intro n
  apply subset_closure
  refine ⟨FiniteGraph.ofRGraph (G.blowup (Structural.WeightedProfile.cloneCount x n)), ?_, rfl⟩
  change 0 < Fintype.card (RGraph.BlowupVertex (Structural.WeightedProfile.cloneCount x n))
  simpa only [RGraph.BlowupVertex, Fintype.card_sigma, Fintype.card_fin] using
    Structural.WeightedProfile.cloneCount_sum_pos x n

noncomputable def weightedFiniteProfiles (r : ℕ) : Set (Profile r) :=
  {W | ∃ (G : FiniteGraph r) (x : Fin G.1 → ℝ), ProbabilityWeights x ∧ W = weightedProfile G.2 x}

theorem finiteProfiles_subset_weightedFiniteProfiles (r : ℕ) :
    finiteProfiles r ⊆ weightedFiniteProfiles r := by
  rintro W ⟨G, hG, rfl⟩
  refine ⟨G, fun _ => (G.1 : ℝ)⁻¹, ?_, (weightedProfile_uniform G).symm⟩
  refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), ?_⟩
  simp [ne_of_gt hG]

/-- Weighted and ordinary finite templates generate exactly the same
homomorphism-density compactification. -/
theorem closure_weightedFiniteProfiles (r : ℕ) :
    closure (weightedFiniteProfiles r) = closure (finiteProfiles r) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro W ⟨G, x, hx, rfl⟩
    exact isLimitProfile_weighted G.2 x hx
  · exact closure_mono (finiteProfiles_subset_weightedFiniteProfiles r)

theorem isCompact_limitProfiles (r : ℕ) : IsCompact {W : Profile r | IsLimitProfile W} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : FiniteGraph r => (0 : ℝ))
    (fun _ => (1 : ℝ)))).of_isClosed_subset isClosed_closure
  intro W hW
  exact ⟨fun A => (IsLimitProfile.bounds hW A).1, fun A => (IsLimitProfile.bounds hW A).2⟩

end TuranUniversality.SetFamily
