module

public import TuranUniversality.Density.FamilyUpper
public import TuranUniversality.Density.UpperBridge

@[expose] public section

/-! # The finite-family homomorphism upper bridge

A sample from an ordinary family-free extremal graph can contain a forbidden
homomorphism. The probability of each such event tends to zero, and a finite
sum controls the event that any member of the family occurs. This extends
the ordinary-density upper bridge to every uniformity and finite family.
-/

open Filter Topology

namespace TuranUniversality

open Selector Density

universe u

variable {r : ℕ}

theorem family_sampled_upper_bound {W : Type u} [DecidableEq W] [Fintype W]
    [Nonempty W] (F : Finset (FiniteGraph r)) (G : RGraph W r)
    (m : ℕ) (hm : 0 < m) (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ H : RGraph (Fin m) r,
      familyHomFree F H → (RGraph.oneEdge r).homDensity H ≤ c) :
    samplingFactor r m * (RGraph.oneEdge r).homDensity G ≤
      c + ∑ A ∈ F, A.2.badSampleProbability G m := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [← G.mean_sample_edgeDensity]
  calc
    mean (fun f : Fin m → W => (RGraph.oneEdge r).homDensity (G.sample m f)) ≤
        mean (fun f : Fin m → W => c + ∑ A ∈ F,
          truth (∃ g, A.2.IsHom (G.sample m f) g)) := by
      apply mean_mono
      intro f
      have hsum0 : 0 ≤ ∑ A ∈ F,
          truth (∃ g, A.2.IsHom (G.sample m f) g) :=
        Finset.sum_nonneg fun _ _ => truth_nonneg _
      by_cases hgood : familyHomFree F (G.sample m f)
      · exact (hclass _ hgood).trans (le_add_of_nonneg_right hsum0)
      · have hex : ∃ A ∈ F, ∃ g, A.2.IsHom (G.sample m f) g := by
          by_contra h
          exact hgood (fun A hA hHom => h ⟨A, hA, hHom⟩)
        obtain ⟨A, hA, g, hg⟩ := hex
        have hone : (1 : ℝ) ≤ ∑ B ∈ F,
            truth (∃ g, B.2.IsHom (G.sample m f) g) := by
          have h := Finset.single_le_sum
            (fun B (_ : B ∈ F) => truth_nonneg
              (∃ g, B.2.IsHom (G.sample m f) g)) hA
          simpa [truth, show ∃ g, A.2.IsHom (G.sample m f) g from ⟨g, hg⟩]
            using h
        exact ((RGraph.oneEdge r).homDensity_le_one (G.sample m f)).trans
          (by linarith)
    _ = c + ∑ A ∈ F, A.2.badSampleProbability G m := by
      rw [mean_add, mean_const]
      congr 1
      exact Finset.expect_sum_comm _ _ _

theorem family_badSample_sum_tendsto (F : Finset (FiniteGraph r))
    (G : ∀ n : ℕ, RGraph (Fin (n + 1)) r)
    (hfree : ∀ n, familyFree F (G n)) (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => ∑ A ∈ F, A.2.badSampleProbability (G n) m)
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum F fun A hA =>
    A.2.badSampleProbability_tendsto G (fun n => hfree n A hA) m hm
  simpa using h

/-- A fixed sample size already bounds the ordinary density, with the
explicit probability of sampling distinct vertices as the loss factor. -/
theorem family_samplingFactor_mul_density_le (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) (hm : 0 < m)
    (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ H : RGraph (Fin m) r,
      familyHomFree F H → (RGraph.oneEdge r).homDensity H ≤ c) :
    samplingFactor r m * familyTuranDensity F ≤ c := by
  have hlim := familyExtremalHost_edgeDensity_tendsto F hedges
  have hb := family_badSample_sum_tendsto F (familyExtremalHost F hedges)
    (familyExtremalHost_free F hedges) m hm
  have hl := hlim.const_mul (samplingFactor r m)
  have hr : Tendsto
      (fun n => c + ∑ A ∈ F, A.2.badSampleProbability (familyExtremalHost F hedges n) m)
      atTop (𝓝 c) := by simpa using hb.const_add c
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n =>
    family_sampled_upper_bound F (familyExtremalHost F hedges n) m hm c hc hclass)

/-- A common bound for uniform edge densities of all finite family-hom-free
graphs bounds the ordinary Turán density of the finite family. -/
theorem familyTuranDensity_upper_of_homFree (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ m (H : RGraph (Fin m) r),
      familyHomFree F H → (RGraph.oneEdge r).homDensity H ≤ c) :
    familyTuranDensity F ≤ c := by
  have hfinal : Tendsto (fun m => samplingFactor r m * familyTuranDensity F)
      atTop (𝓝 (familyTuranDensity F)) := by
    simpa using (samplingFactor_tendsto r).mul_const (familyTuranDensity F)
  apply le_of_tendsto hfinal
  filter_upwards [eventually_ge_atTop 1] with m hpos
  exact family_samplingFactor_mul_density_le F hedges m hpos c hc (hclass m)

end TuranUniversality
