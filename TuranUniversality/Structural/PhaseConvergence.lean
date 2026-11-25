module

public import TuranUniversality.Structural.PhaseExpansion
public import TuranUniversality.Hypergraph.Relabel

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Convergence of actual compiled profiles to the phase map

Both conditional collision terms are controlled by the original data
second moment and the actual active and neutral masses. The resulting
statement allows the finite carrier to vary along an arbitrary filter.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.PhaseRoles

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

theorem activeWeight_squares_le (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ) :
    (∑ v, (activeWeight O x v) ^ 2) ≤
      (∑ v : V, (x (.inr (.inr v))) ^ 2) / (roleWeight O x (.inr false)) ^ 2 := by
  simp only [activeWeight, div_pow, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.ext h) (Finset.subset_univ _)
    (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)

theorem neutralWeight_squares_le (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ) :
    (∑ v, (neutralWeight O x v) ^ 2) ≤
      (∑ v : V, (x (.inr (.inr v))) ^ 2) / (roleWeight O x (.inr true)) ^ 2 := by
  simp only [neutralWeight, div_pow, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.ext h) (Finset.subset_univ _)
    (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)

noncomputable def innerProfile (O : LegalObject B V) (phase : Bool)
    (x : Compiled.Vertex b t V → ℝ) : SetFamily.Profile 3 :=
  SetFamily.weightedProfile ((O.inner phase).pullback (Function.Embedding.subtype _))
    (activeWeight O x)

variable {I : Type*} {X : I → Type*}
variable [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]

theorem activeWeight_squares_tendsto (O : ∀ i, LegalObject B (X i))
    (x : ∀ i, Compiled.Vertex b t (X i) → ℝ) (l : Filter I) (a : ℝ) (ha : 0 < a)
    (hm : Tendsto (fun i => roleWeight (O i) (x i) (.inr false)) l (𝓝 a))
    (hs : Tendsto (fun i => ∑ v : X i, (x i (.inr (.inr v))) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ∑ v, (activeWeight (O i) (x i) v) ^ 2) l (𝓝 0) := by
  apply squeeze_zero (fun i => Finset.sum_nonneg (fun v _ => sq_nonneg _))
    (fun i => activeWeight_squares_le (O i) (x i))
  have h := hs.div (hm.pow 2) (pow_ne_zero 2 (ne_of_gt ha))
  change Tendsto (fun i => (∑ v : X i, (x i (.inr (.inr v))) ^ 2) /
    (roleWeight (O i) (x i) (.inr false)) ^ 2) l (𝓝 (0 / a ^ 2)) at h
  simpa only [zero_div] using h

theorem neutralWeight_squares_tendsto (O : ∀ i, LegalObject B (X i))
    (x : ∀ i, Compiled.Vertex b t (X i) → ℝ) (l : Filter I) (w : ℝ) (hw : 0 < w)
    (hm : Tendsto (fun i => roleWeight (O i) (x i) (.inr true)) l (𝓝 w))
    (hs : Tendsto (fun i => ∑ v : X i, (x i (.inr (.inr v))) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ∑ v, (neutralWeight (O i) (x i) v) ^ 2) l (𝓝 0) := by
  apply squeeze_zero (fun i => Finset.sum_nonneg (fun v _ => sq_nonneg _))
    (fun i => neutralWeight_squares_le (O i) (x i))
  have h := hs.div (hm.pow 2) (pow_ne_zero 2 (ne_of_gt hw))
  change Tendsto (fun i => (∑ v : X i, (x i (.inr (.inr v))) ^ 2) /
    (roleWeight (O i) (x i) (.inr true)) ^ 2) l (𝓝 (0 / w ^ 2)) at h
  simpa only [zero_div] using h

/-- The phase-coordinate polynomial is the actual limit of a fixed-phase
sequence, proved from the finite-model expansion and vanishing collisions. -/
theorem phaseMap_tendsto (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (O : ∀ i, LegalObject B (X i)) (hphase : ∀ i s, s ≠ phase → ((O i).inner s).edges = ∅)
    (x : ∀ i, Compiled.Vertex b t (X i) → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I) (z : Role b t → ℝ) (W : SetFamily.Profile 3)
    (ha : 0 < z (.inr false)) (hw : 0 < z (.inr true))
    (hz : Tendsto (fun i => roleWeight (O i) (x i)) l (𝓝 z))
    (hW : Tendsto (fun i => innerProfile (O i) phase (x i)) l (𝓝 W))
    (hs : Tendsto (fun i => ∑ v : X i, (x i (.inr (.inr v))) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => SetFamily.weightedProfile (Compiled.graph t Ω (O i).records) (x i))
      l (𝓝 (phaseMap Ω phase z W)) := by
  have hma := (tendsto_pi_nhds.mp hz) (.inr false)
  have hmw := (tendsto_pi_nhds.mp hz) (.inr true)
  have heA := hma.eventually (lt_mem_nhds ha)
  have heW := hmw.eventually (lt_mem_nhds hw)
  have hsA := activeWeight_squares_tendsto O x l _ ha hma hs
  have hsW := neutralWeight_squares_tendsto O x l _ hw hmw hs
  have hΦ := (continuous_phaseMap Ω phase).tendsto (z, W) |>.comp (hz.prodMk_nhds hW)
  change Tendsto (fun i => phaseMap Ω phase (roleWeight (O i) (x i))
    (innerProfile (O i) phase (x i))) l (𝓝 (phaseMap Ω phase z W)) at hΦ
  apply tendsto_pi_nhds.mpr
  intro H
  have hsmall : Tendsto (fun i => (H.1 : ℝ) ^ 2 *
      ((∑ v, (activeWeight (O i) (x i) v) ^ 2) + ∑ v, (neutralWeight (O i) (x i) v) ^ 2))
      l (𝓝 0) := by
    simpa only [zero_add, mul_zero] using (hsA.add hsW).const_mul ((H.1 : ℝ) ^ 2)
  have herr : Tendsto (fun i =>
      SetFamily.weightedProfile (Compiled.graph t Ω (O i).records) (x i) H -
        phaseMap Ω phase (roleWeight (O i) (x i)) (innerProfile (O i) phase (x i)) H)
      l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg _)) _ hsmall
    filter_upwards [heA, heW] with i hiA hiW
    simpa only [SetFamily.weightedProfile, innerProfile, phaseMap, Fintype.card_fin] using
      coordinate_error Ω phase H.2 (O i) (hphase i) (x i) (hx i) hiA hiW
  have h := herr.add ((tendsto_pi_nhds.mp hΦ) H)
  simpa only [sub_add_cancel, zero_add] using h

end TuranUniversality.Structural.PhaseRoles
