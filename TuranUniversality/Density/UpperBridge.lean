module

public import TuranUniversality.Density.SampleMoments
public import TuranUniversality.Density.Extremal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-!
# Ordinary Turán upper bounds from hom-free templates

This proves the upper half of the homomorphism–Lagrangian bridge by finite
sampling and the ordinary extremal-density limit. No hypergraph limit space,
removal lemma, or axiomatized density identity is used.
-/

open Filter Topology

namespace TuranUniversality

theorem tendsto_zero_of_power_le {f g : ℕ → ℝ} (k : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hbound : ∀ n, f n ^ k ≤ g n)
    (hg : Tendsto g atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hf n)
  · intro e he
    filter_upwards [hg.eventually (gt_mem_nhds (pow_pos he k))] with n hn
    by_contra h
    have hp : e ^ k ≤ f n ^ k := pow_le_pow_left₀ he.le (le_of_not_gt h) k
    exact (not_le_of_gt ((hbound n).trans_lt hn)) hp

theorem samplingFactor_three {n : ℕ} (hn : 3 ≤ n) :
    samplingFactor 3 n = (1 - (n : ℝ)⁻¹) * (1 - 2 * (n : ℝ)⁻¹) := by
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h := congrArg (fun k : ℕ => (k : ℝ))
    (Nat.descFactorial_eq_factorial_mul_choose n 3)
  norm_num [Nat.descFactorial_succ, Nat.cast_sub h1, Nat.cast_sub h2] at h
  unfold samplingFactor
  norm_num
  rw [← h]
  field_simp

theorem samplingFactor_three_tendsto :
    Tendsto (samplingFactor 3) atTop (𝓝 1) := by
  have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) * (1 - 2 * (n : ℝ)⁻¹))
      atTop (𝓝 1) := by
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using (hone.sub hz).mul (hone.sub (hz.const_mul 2))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (samplingFactor_three hn).symm

namespace RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem badSampleProbability_tendsto (F : RGraph V r)
    (G : ∀ n : ℕ, RGraph (Fin (n + 1)) r)
    (hfree : ∀ n, ¬ ∃ f, F.IsEmbedding (G n) f) (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => F.badSampleProbability (G n) m) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hz' : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hz
  apply tendsto_zero_of_power_le ((Fintype.card V + 1) ^ m)
    (fun n => F.badSampleProbability_nonneg (G n) m)
    (fun n => F.badSampleProbability_power_bound (G n) m hm (hfree n))
  simpa [Fintype.card_fin, div_eq_mul_inv] using
    (hz'.const_mul ((Fintype.card V : ℝ) ^ 2)).const_mul
      ((Fintype.card (V → Fin m) : ℝ) ^ ((Fintype.card V + 1) ^ m))

end RGraph

/-- A fixed choice of actual ordinary extremal graphs, on nonempty vertex sets. -/
noncomputable def extremalHost {k : ℕ} (F : RGraph (Fin k) 3)
    (hF : 1 ≤ F.edges.card) (n : ℕ) : RGraph (Fin (n + 1)) 3 :=
  Classical.choose (F.exists_extremal hF (n + 1))

theorem extremalHost_free {k : ℕ} (F : RGraph (Fin k) 3)
    (hF : 1 ≤ F.edges.card) (n : ℕ) :
    ¬ ∃ f, F.IsEmbedding (extremalHost F hF n) f :=
  (Classical.choose_spec (F.exists_extremal hF (n + 1))).1

theorem extremalHost_card {k : ℕ} (F : RGraph (Fin k) 3)
    (hF : 1 ≤ F.edges.card) (n : ℕ) :
    (extremalHost F hF n).edges.card = extremalNumber F (n + 1) :=
  (Classical.choose_spec (F.exists_extremal hF (n + 1))).2

theorem extremalHost_edgeDensity_tendsto {k : ℕ} (F : RGraph (Fin k) 3)
    (hF : 1 ≤ F.edges.card) :
    Tendsto (fun n => (RGraph.oneEdge 3).homDensity (extremalHost F hF n))
      atTop (𝓝 (turanDensity F)) := by
  have ha : Tendsto (fun n => samplingFactor 3 (n + 1)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr samplingFactor_three_tendsto
  have hb : Tendsto (fun n => extremalDensity F (n + 1)) atTop (𝓝 (turanDensity F)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (extremalDensity_tendsto F hF)
  have h := ha.mul hb
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [RGraph.oneEdge_homDensity, extremalHost_card]
  unfold samplingFactor extremalDensity
  have hc : ((n + 1).choose 3 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (show 3 ≤ n + 1 by omega))
  simp only [Fintype.card_fin]
  field_simp

/-- The ordinary Turán density is bounded by any common bound for the
normalized uniform edge polynomials of all finite F-hom-free templates. -/
theorem turanDensity_upper_of_homFree {k : ℕ} (F : RGraph (Fin k) 3)
    (hF : 1 ≤ F.edges.card) (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ (m : ℕ) (H : RGraph (Fin m) 3),
      F.HomFree H → (RGraph.oneEdge 3).homDensity H ≤ c) :
    turanDensity F ≤ c := by
  have hlim := extremalHost_edgeDensity_tendsto F hF
  have hm (m : ℕ) (hmpos : 0 < m) : samplingFactor 3 m * turanDensity F ≤ c := by
    have hb := F.badSampleProbability_tendsto (extremalHost F hF)
      (extremalHost_free F hF) m hmpos
    have hl := hlim.const_mul (samplingFactor 3 m)
    have hr : Tendsto (fun n => c + F.badSampleProbability (extremalHost F hF n) m)
        atTop (𝓝 c) := by simpa using hb.const_add c
    exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n =>
      F.sampled_upper_bound (extremalHost F hF n) m hmpos c hc (hclass m))
  have hfinal : Tendsto (fun m => samplingFactor 3 m * turanDensity F)
      atTop (𝓝 (turanDensity F)) := by
    simpa using samplingFactor_three_tendsto.mul_const (turanDensity F)
  apply le_of_tendsto hfinal
  filter_upwards [eventually_ge_atTop 1] with m hpos
  exact hm m hpos

end TuranUniversality
