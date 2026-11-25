module

public import TuranUniversality.Density.WeightedHomConvergence

@[expose] public section

/-! # Actual normalized edge-edit distance on a fixed finite carrier -/

open scoped symmDiff
open Filter Topology

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

noncomputable def normalizedEditDistance (G H : RGraph V r) : ℝ :=
  ((G.edgeSymmDifference H).edges.card : ℝ) / (Fintype.card V : ℝ) ^ r

theorem normalizedEditDistance_nonneg (G H : RGraph V r) :
    0 ≤ G.normalizedEditDistance H := by unfold normalizedEditDistance; positivity

theorem edgeSymmDifference_eq_difference {G H : RGraph V r} (h : G.edges ⊆ H.edges) :
    G.edgeSymmDifference H = H.edgeDifference G := by
  apply RGraph.ext
  ext e
  have he : e ∈ G.edges → e ∈ H.edges := fun he => h he
  simp only [edgeSymmDifference, edgeDifference, Finset.mem_symmDiff, Finset.mem_sdiff]
  tauto

theorem normalizedEditDistance_eq_polynomial (G H : RGraph V r) :
    G.normalizedEditDistance H = (G.edgeSymmDifference H).edgePolynomial
      (fun _ => (Fintype.card V : ℝ)⁻¹) := by
  rw [edgePolynomial_uniform]
  simp only [normalizedEditDistance, inv_pow, div_eq_mul_inv]

theorem normalizedEditDistance_eq_sub {G H : RGraph V r} (h : G.edges ⊆ H.edges) :
    G.normalizedEditDistance H =
      H.edgePolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) -
        G.edgePolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) := by
  rw [normalizedEditDistance_eq_polynomial, edgeSymmDifference_eq_difference h,
    edgeDifference_polynomial _ _ h]

theorem normalizedEditDistance_triangle (G H K : RGraph V r) :
    G.normalizedEditDistance K ≤ G.normalizedEditDistance H + H.normalizedEditDistance K := by
  have hsub : (G.edgeSymmDifference K).edges ⊆
      (G.edgeSymmDifference H).edges ∪ (H.edgeSymmDifference K).edges := by
    intro e he
    simp only [edgeSymmDifference, Finset.mem_symmDiff, Finset.mem_union] at he ⊢
    tauto
  have hc : ((G.edgeSymmDifference K).edges.card : ℝ) ≤
      (G.edgeSymmDifference H).edges.card + (H.edgeSymmDifference K).edges.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold normalizedEditDistance
  rw [← add_div]
  exact div_le_div_of_nonneg_right hc (by positivity)

theorem normalizedEditDistance_tendsto_zero_trans
    {I : Type*} {W : I → Type*} [∀ i, DecidableEq (W i)] [∀ i, Fintype (W i)]
    (G H K : ∀ i, RGraph (W i) r) (l : Filter I)
    (hGH : Tendsto (fun i => (G i).normalizedEditDistance (H i)) l (𝓝 0))
    (hHK : Tendsto (fun i => (H i).normalizedEditDistance (K i)) l (𝓝 0)) :
    Tendsto (fun i => (G i).normalizedEditDistance (K i)) l (𝓝 0) := by
  apply squeeze_zero (fun i => (G i).normalizedEditDistance_nonneg (K i))
    (fun i => (G i).normalizedEditDistance_triangle (H i) (K i))
  simpa only [add_zero] using hGH.add hHK

end TuranUniversality.RGraph
