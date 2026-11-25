module

public import TuranUniversality.Density.FreeRealizationApprox

@[expose] public section

/-! # Free realization of limit profiles (Lemma 2.1)

For an arbitrary forbidden family, a dense limit profile has vanishing
forbidden coordinates exactly when it is approached by ordinary free graphs
whose orders tend to infinity. The proof constructs the sequence from the
finite-coordinate sampling theorem and proves necessity by collision bounds.
-/

open Filter Topology

namespace TuranUniversality.SetFamily

variable {r : ℕ}
noncomputable section

/-- Ordinary free hosts, unbounded order, and convergence in the actual
product topology on all finite homomorphism-density coordinates. -/
def IsFreeLimit (F : Set (FiniteGraph r)) (W : Profile r) : Prop :=
  ∃ G : ℕ → FiniteGraph r,
    (∀ n, Free F (G n).2) ∧
    Tendsto (fun n => (G n).1) atTop atTop ∧
    Tendsto (fun n => profile (G n)) atTop (𝓝 W)

theorem IsLimitProfile.bounds {W : Profile r} (hW : IsLimitProfile W) (A : FiniteGraph r) :
    0 ≤ W A ∧ W A ≤ 1 := by
  have hclosed : IsClosed {p : Profile r | 0 ≤ p A ∧ p A ≤ 1} :=
    (isClosed_le continuous_const (continuous_apply A)).inter
      (isClosed_le (continuous_apply A) continuous_const)
  apply closure_minimal _ hclosed hW
  rintro p ⟨G, hG, rfl⟩
  let : Nonempty (Fin G.1) := ⟨⟨0, hG⟩⟩
  exact ⟨A.2.homDensity_nonneg G.2, A.2.homDensity_le_one G.2⟩

theorem isFreeLimit_of_vanishing (F : Set (FiniteGraph r)) (W : Profile r)
    (hW : IsLimitProfile W) (hzero : ∀ A ∈ F, W A = 0) : IsFreeLimit F W := by
  classical
  have hex (n : ℕ) : ∃ G : FiniteGraph r, n + 1 ≤ G.1 ∧ 0 < G.1 ∧ Free F G.2 ∧
      ∀ A ∈ FiniteGraph.bounded r n, |profile G A - W A| < 1 / ((n + 1 : ℕ) : ℝ) :=
    exists_free_close_of_vanishing F W hW hzero (FiniteGraph.bounded r n)
      (1 / ((n + 1 : ℕ) : ℝ)) (by positivity) (n + 1)
  choose G hsize hpos hfree hclose using hex
  refine ⟨G, hfree, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (hsize n)) tendsto_id
  · apply tendsto_pi_nhds.mpr
    intro A
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have herror : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_add_atTop_iff_nat 1).mpr hinv
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (dist_nonneg))
    · intro ε hε
      filter_upwards [herror.eventually (gt_mem_nhds hε), eventually_ge_atTop A.1] with n hn hAn
      have hA : A ∈ FiniteGraph.bounded r n := (FiniteGraph.mem_bounded A).mpr hAn
      simpa only [Real.dist_eq] using (hclose n A hA).trans hn

theorem vanishing_of_isFreeLimit (F : Set (FiniteGraph r)) (W : Profile r)
    (hW : IsFreeLimit F W) : ∀ A ∈ F, W A = 0 := by
  obtain ⟨G, hfree, horder, hprofile⟩ := hW
  intro A hA
  have hcoord : Tendsto (fun n => profile (G n) A) atTop (𝓝 (W A)) :=
    (tendsto_pi_nhds.mp hprofile) A
  have hinv : Tendsto (fun n => ((G n).1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp horder)
  have hbound : Tendsto (fun n => (A.1 : ℝ) ^ 2 / (G n).1) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul ((A.1 : ℝ) ^ 2)
  have hz : Tendsto (fun n => profile (G n) A) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (A.2.homDensity_nonneg (G n).2))
    · intro ε hε
      filter_upwards [hbound.eventually (gt_mem_nhds hε),
        horder.eventually (eventually_ge_atTop 1)] with n hn hpos
      let : Nonempty (Fin (G n).1) := ⟨⟨0, by omega⟩⟩
      have hb : profile (G n) A ≤ (A.1 : ℝ) ^ 2 / (G n).1 := by
        simpa only [profile, Fintype.card_fin] using
          A.2.homDensity_le_collision_bound (G n).2 (hfree n A hA)
      exact hb.trans_lt hn
  exact tendsto_nhds_unique hcoord hz

/-- Lemma 2.1, with an explicit dense-limit-space hypothesis and the
ordinary (globally injective) meaning of forbidden-freeness. -/
theorem free_realization_iff (F : Set (FiniteGraph r)) (W : Profile r)
    (hW : IsLimitProfile W) :
    IsFreeLimit F W ↔ ∀ A ∈ F, W A = 0 :=
  ⟨vanishing_of_isFreeLimit F W, isFreeLimit_of_vanishing F W hW⟩

end
end TuranUniversality.SetFamily
