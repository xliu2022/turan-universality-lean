module

public import TuranUniversality.Density.Sampling
public import TuranUniversality.Density.EdgeDensity

@[expose] public section

/-! # The exact first moment of a sampled edge count -/

open scoped BigOperators

namespace TuranUniversality

open Selector Density

/-- The probability that r independent indices in an m-element set are distinct. -/
noncomputable def samplingFactor (r m : ℕ) : ℝ := (r.factorial : ℝ) * m.choose r / (m : ℝ) ^ r

namespace RGraph

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

theorem mean_sample_edge [Fintype W] [Nonempty W]
    (G : RGraph W r) (m : ℕ) (e : Finset (Fin m)) (he : e.card = r) :
    mean (fun f : Fin m → W => truth (e ∈ (G.sample m f).edges)) =
      (oneEdge r).homDensity G := by
  classical
  let a : Fin r ≃ e := Fintype.equivOfCardEq (by simp [he])
  let i : Fin r → Fin m := fun j => (a j).val
  have hi : Function.Injective i := fun x y h => a.injective (Subtype.ext h)
  have him : Finset.univ.image i = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact (a j).property
    · intro hv
      obtain ⟨j, hj⟩ := a.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  have hpoint (f : Fin m → W) : truth (e ∈ (G.sample m f).edges) =
      (oneEdge r).homIndicator G (f ∘ i) := by
    unfold truth homIndicator
    congr 1
    apply propext
    rw [G.mem_sample, G.oneEdge_isHom, ← Finset.image_image, him]
    simp [he]
  calc
    mean (fun f : Fin m → W => truth (e ∈ (G.sample m f).edges)) =
        mean (fun f : Fin m → W => (oneEdge r).homIndicator G (f ∘ i)) :=
      mean_congr hpoint
    _ = (oneEdge r).homDensity G := mean_restrict_injective i hi _

theorem mean_sample_card [Fintype W] [Nonempty W]
    (G : RGraph W r) (m : ℕ) :
    mean (fun f : Fin m → W => ((G.sample m f).edges.card : ℝ)) =
      (m.choose r : ℝ) * (oneEdge r).homDensity G := by
  classical
  have hcount (f : Fin m → W) : ((G.sample m f).edges.card : ℝ) =
      ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        truth (e ∈ (G.sample m f).edges) := by
    calc
      ((G.sample m f).edges.card : ℝ) = ∑ _e ∈ (G.sample m f).edges, (1 : ℝ) := by simp
      _ = ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
          if e.image f ∈ G.edges then (1 : ℝ) else 0 := by
        rw [sample, Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        have hcard := (Finset.mem_powersetCard.mp he).2
        simp [truth, G.mem_sample, hcard]
  calc
    mean (fun f : Fin m → W => ((G.sample m f).edges.card : ℝ)) =
        mean (fun f : Fin m → W => ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
          truth (e ∈ (G.sample m f).edges)) := mean_congr hcount
    _ = ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        mean (fun f : Fin m → W => truth (e ∈ (G.sample m f).edges)) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin m)).powersetCard r, (oneEdge r).homDensity G := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.mean_sample_edge m e (Finset.mem_powersetCard.mp he).2
    _ = _ := by simp [Finset.card_powersetCard]

theorem mean_sample_edgeDensity [Fintype W] [Nonempty W]
    (G : RGraph W r) (m : ℕ) :
    mean (fun f : Fin m → W => (oneEdge r).homDensity (G.sample m f)) =
      samplingFactor r m * (oneEdge r).homDensity G := by
  simp_rw [oneEdge_homDensity (G.sample m _), Fintype.card_fin]
  calc
    mean (fun f : Fin m → W => (r.factorial : ℝ) * (G.sample m f).edges.card / (m : ℝ) ^ r) =
        ((r.factorial : ℝ) / (m : ℝ) ^ r) *
          mean (fun f : Fin m → W => ((G.sample m f).edges.card : ℝ)) := by
      rw [← mean_const_mul]
      apply mean_congr
      intro f
      ring
    _ = _ := by rw [G.mean_sample_card]; unfold samplingFactor; ring

/-- A uniform hom-free edge-density bound controls a finite sample up to its
bad-event probability. This is the finite inequality used in the density limit. -/
theorem sampled_upper_bound [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) (m : ℕ) (hm : 0 < m)
    (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ H : RGraph (Fin m) r, F.HomFree H → (oneEdge r).homDensity H ≤ c) :
    samplingFactor r m * (oneEdge r).homDensity G ≤
      c + F.badSampleProbability G m := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [← G.mean_sample_edgeDensity]
  calc
    mean (fun f : Fin m → W => (oneEdge r).homDensity (G.sample m f)) ≤
        mean (fun f : Fin m → W => c + truth
          (∃ g, F.IsHom (G.sample m f) g)) := by
      apply mean_mono
      intro f
      by_cases hbad : ∃ g, F.IsHom (G.sample m f) g
      · simp only [truth, ite_eq_left hbad]
        exact (oneEdge r).homDensity_le_one (G.sample m f) |>.trans (by linarith)
      · simpa [truth, hbad] using hclass (G.sample m f) hbad
    _ = c + F.badSampleProbability G m := by rw [mean_add, mean_const]; rfl

end RGraph
end TuranUniversality
