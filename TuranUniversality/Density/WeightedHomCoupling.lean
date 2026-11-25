module

public import TuranUniversality.Density.WeightedHom
public import Mathlib.Data.Finset.SymmDiff

@[expose] public section

/-! # Coupling homomorphism densities under edge changes

All comparisons use the same actual finite carrier and its real probability
weighting. A failed edge is detected by one source edge, so a finite union
bound gives the exact factor `r! * |E(F)|`. The mismatch graph consists of
the actual symmetric difference of the two target edge sets.
-/

open scoped BigOperators symmDiff

namespace TuranUniversality.RGraph

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V] {r : ℕ}

def edgeDifference (G H : RGraph V r) : RGraph V r where
  edges := G.edges \ H.edges
  uniform e he := G.uniform e (Finset.mem_sdiff.mp he).1

def edgeSymmDifference (G H : RGraph V r) : RGraph V r where
  edges := G.edges ∆ H.edges
  uniform e he := by
    rcases Finset.mem_symmDiff.mp he with h | h
    · exact G.uniform e h.1
    · exact H.uniform e h.1

theorem edgeDifference_polynomial (G H : RGraph V r) (h : H.edges ⊆ G.edges)
    (x : V → ℝ) :
    (G.edgeDifference H).edgePolynomial x = G.edgePolynomial x - H.edgePolynomial x :=
  Finset.sum_sdiff_eq_sub h

theorem edgeDifference_subset_symmDifference (G H : RGraph V r) :
    (G.edgeDifference H).edges ⊆ (G.edgeSymmDifference H).edges := by
  intro e he
  exact Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp he))

theorem edgeSymmDifference_comm (G H : RGraph V r) :
    G.edgeSymmDifference H = H.edgeSymmDifference G := by
  apply RGraph.ext
  exact symmDiff_comm _ _

theorem weightedMean_edgeImage [Fintype U] [Fintype V]
    (G : RGraph V r) (x : V → ℝ) (hx : ∑ v, x v = 1)
    (e : Finset U) (he : e.card = r) :
    weightedMean x (fun f : U → V => if e.image f ∈ G.edges then (1 : ℝ) else 0) =
      (r.factorial : ℝ) * G.edgePolynomial x := by
  classical
  let a : Fin r ≃ e := Fintype.equivOfCardEq (by simp [he])
  let i : Fin r → U := fun j => (a j).val
  have hi : Function.Injective i := fun j k h => a.injective (Subtype.ext h)
  have him : Finset.univ.image i = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact (a j).property
    · intro hv
      obtain ⟨j, hj⟩ := a.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  calc
    _ = weightedMean x (fun f : U → V => (oneEdge r).homIndicator G (f ∘ i)) := by
      apply weightedMean_congr
      intro f
      simp only [homIndicator, oneEdge_isHom, ← Finset.image_image, him]
    _ = weightedMean x ((oneEdge r).homIndicator G) :=
      weightedMean_restrict_injective x hx i hi _
    _ = _ := G.weightedMean_oneEdge x

theorem homIndicator_sub_le_edgeDifference (F : RGraph U r) (G H : RGraph V r)
    (f : U → V) :
    F.homIndicator G f - F.homIndicator H f ≤
      ∑ e ∈ F.edges, if e.image f ∈ (G.edgeDifference H).edges then (1 : ℝ) else 0 := by
  classical
  have hnonneg : 0 ≤ ∑ e ∈ F.edges,
      if e.image f ∈ (G.edgeDifference H).edges then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun e _ => by split <;> norm_num)
  by_cases hg : F.IsHom G f
  · by_cases hh : F.IsHom H f
    · simpa [hg, hh] using hnonneg
    · have hn : ∃ e ∈ F.edges, e.image f ∉ H.edges := by
        simpa only [IsHom, not_forall, exists_prop] using hh
      obtain ⟨e, he, hn⟩ := hn
      have hm : e.image f ∈ (G.edgeDifference H).edges :=
        Finset.mem_sdiff.mpr ⟨hg e he, hn⟩
      have hsingle := Finset.single_le_sum
        (f := fun e : Finset U =>
          if e.image f ∈ (G.edgeDifference H).edges then (1 : ℝ) else 0)
        (fun e _ => by split <;> norm_num) he
      simpa [hg, hh, hm] using hsingle
  · have hh := F.homIndicator_nonneg H f
    rw [homIndicator_of_not_hom F G hg]
    linarith

/-- The one-sided coupling bound also applies to incomparable target graphs. -/
theorem weightedHomDensity_sub_le_edgeDifference [Fintype U] [Fintype V]
    (F : RGraph U r) (G H : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x) :
    F.weightedHomDensity G x - F.weightedHomDensity H x ≤
      (r.factorial : ℝ) * F.edges.card * (G.edgeDifference H).edgePolynomial x := by
  calc
    _ = weightedMean x (fun f => F.homIndicator G f - F.homIndicator H f) := by
      simp only [weightedHomDensity, weightedMean, mul_sub, Finset.sum_sub_distrib]
    _ ≤ weightedMean x (fun f : U → V => ∑ e ∈ F.edges,
        if e.image f ∈ (G.edgeDifference H).edges then (1 : ℝ) else 0) :=
      weightedMean_mono x hx.1 (F.homIndicator_sub_le_edgeDifference G H)
    _ = ∑ e ∈ F.edges, weightedMean x (fun f : U → V =>
        if e.image f ∈ (G.edgeDifference H).edges then (1 : ℝ) else 0) :=
      weightedMean_sum x _ _
    _ = ∑ _e ∈ F.edges, (r.factorial : ℝ) * (G.edgeDifference H).edgePolynomial x := by
      apply Finset.sum_congr rfl
      intro e he
      exact (G.edgeDifference H).weightedMean_edgeImage x hx.2 e (F.uniform e he)
    _ = _ := by simp; ring

theorem weightedHomDensity_mono [Fintype U] [Fintype V]
    (F : RGraph U r) (G H : RGraph V r) (h : G.edges ⊆ H.edges)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    F.weightedHomDensity G x ≤ F.weightedHomDensity H x := by
  apply weightedMean_mono x hx
  intro f
  by_cases hg : F.IsHom G f
  · have hh : F.IsHom H f := fun e he => h (hg e he)
    simp [hg, hh]
  · rw [homIndicator_of_not_hom F G hg]
    exact F.homIndicator_nonneg H f

/-- Completion/deletion changes every test coordinate by at most the
normalized edge-weight deficit times its number of edges. -/
theorem weightedHomDensity_sub_bounds [Fintype U] [Fintype V]
    (F : RGraph U r) (G H : RGraph V r) (h : G.edges ⊆ H.edges)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    0 ≤ F.weightedHomDensity H x - F.weightedHomDensity G x ∧
      F.weightedHomDensity H x - F.weightedHomDensity G x ≤
        (r.factorial : ℝ) * F.edges.card * (H.edgePolynomial x - G.edgePolynomial x) := by
  refine ⟨sub_nonneg.mpr (F.weightedHomDensity_mono G H h x hx.1), ?_⟩
  simpa only [edgeDifference_polynomial H G h x] using
    F.weightedHomDensity_sub_le_edgeDifference H G x hx

/-- A symmetric edge mismatch bound for two actual weighted target graphs. -/
theorem weightedHomDensity_abs_sub_le [Fintype U] [Fintype V]
    (F : RGraph U r) (G H : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x) :
    |F.weightedHomDensity G x - F.weightedHomDensity H x| ≤
      (r.factorial : ℝ) * F.edges.card * (G.edgeSymmDifference H).edgePolynomial x := by
  have hcoef : 0 ≤ (r.factorial : ℝ) * F.edges.card := by positivity
  have hgh := (F.weightedHomDensity_sub_le_edgeDifference G H x hx).trans
    (mul_le_mul_of_nonneg_left
      ((G.edgeDifference H).edgePolynomial_mono _
        (edgeDifference_subset_symmDifference G H) hx.1) hcoef)
  have hhg := (F.weightedHomDensity_sub_le_edgeDifference H G x hx).trans
    (mul_le_mul_of_nonneg_left
      ((H.edgeDifference G).edgePolynomial_mono _
        (edgeDifference_subset_symmDifference H G) hx.1) hcoef)
  rw [edgeSymmDifference_comm H G] at hhg
  exact abs_le.mpr ⟨by linarith, hgh⟩

end TuranUniversality.RGraph
