module

public import TuranUniversality.Hypergraph.InducedDegree
public import TuranUniversality.Density.WeightedHomCoupling
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! # Vertex deletion on the original carrier and actual edge-edit bounds

Vertices outside the retained set become isolated; no vertex is removed
from the ambient type. When the retained set is nonempty, the resulting
graph maps to the actual induced graph. The symmetric edge difference
is bounded by the number of deleted vertices times `n^(r-1)`.
-/

open Filter Topology

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

def keepVertices (G : RGraph V r) (S : Finset V) : RGraph V r where
  edges := G.edges.filter (fun e => e ⊆ S)
  uniform e he := G.uniform e (Finset.mem_filter.mp he).1

@[simp] theorem mem_keepVertices (G : RGraph V r) (S : Finset V) (e : Finset V) :
    e ∈ (G.keepVertices S).edges ↔ e ∈ G.edges ∧ e ⊆ S := Finset.mem_filter

theorem keepVertices_subset (G : RGraph V r) (S : Finset V) :
    (G.keepVertices S).edges ⊆ G.edges := Finset.filter_subset _ _

theorem keepVertices_hom_induced (G : RGraph V r) (S : Finset V) (hs : S.Nonempty) :
    ∃ f : V → S, (G.keepVertices S).IsHom (G.induced S) f := by
  classical
  obtain ⟨a, ha⟩ := hs
  let f : V → S := fun v => if h : v ∈ S then ⟨v, h⟩ else ⟨a, ha⟩
  refine ⟨f, ?_⟩
  intro e he
  obtain ⟨he, hes⟩ := (G.mem_keepVertices S e).mp he
  have hf v (hv : v ∈ e) : (f v).val = v := by simp [f, hes hv]
  have him : (e.image f).map (Function.Embedding.subtype (· ∈ S)) = e := by
    rw [Finset.map_eq_image, Finset.image_image]
    calc
      _ = e.image id := Finset.image_congr (fun v hv => hf v hv)
      _ = e := Finset.image_id
  apply (G.mem_pullback (Function.Embedding.subtype (· ∈ S)) (e.image f)).mpr
  constructor
  · have hc := congrArg Finset.card him
    rw [Finset.card_map, G.uniform e he] at hc
    exact hc
  · rw [him]
    exact he

theorem edgeSymmDifference_keepVertices (G : RGraph V r) (S : Finset V) :
    (G.edgeSymmDifference (G.keepVertices S)).edges =
      G.edges.filter (fun e => ¬ e ⊆ S) := by
  classical
  ext e
  simp only [edgeSymmDifference, Finset.mem_symmDiff, mem_keepVertices, Finset.mem_filter]
  tauto

theorem keepVertices_edit_bound (G : RGraph V r) (S : Finset V) :
    (G.edgeSymmDifference (G.keepVertices S)).edges.card ≤
      (Finset.univ \ S).card * Fintype.card V ^ (r - 1) := by
  rw [G.edgeSymmDifference_keepVertices S]
  exact G.edges_lost_le S

theorem keepVertices_card_add_edit (G : RGraph V r) (S : Finset V) :
    (G.keepVertices S).edges.card + (G.edgeSymmDifference (G.keepVertices S)).edges.card =
      G.edges.card := by
  rw [G.edgeSymmDifference_keepVertices S]
  exact Finset.card_filter_add_card_filter_not (s := G.edges) (fun e => e ⊆ S)

theorem keepVertices_edit_ratio_le (G : RGraph V r) (hr : 1 ≤ r)
    (hn : 0 < Fintype.card V) (S : Finset V) :
    ((G.edgeSymmDifference (G.keepVertices S)).edges.card : ℝ) /
        (Fintype.card V : ℝ) ^ r ≤
      ((Finset.univ \ S).card : ℝ) / Fintype.card V := by
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hc : ((G.edgeSymmDifference (G.keepVertices S)).edges.card : ℝ) ≤
      ((Finset.univ \ S).card : ℝ) * (Fintype.card V : ℝ) ^ (r - 1) := by
    exact_mod_cast G.keepVertices_edit_bound S
  have hp : (Fintype.card V : ℝ) ^ r =
      (Fintype.card V : ℝ) ^ (r - 1) * Fintype.card V := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  calc
    _ ≤ (((Finset.univ \ S).card : ℝ) * (Fintype.card V : ℝ) ^ (r - 1)) /
        (Fintype.card V : ℝ) ^ r := div_le_div_of_nonneg_right hc (pow_nonneg hn0.le _)
    _ = _ := by rw [hp]; field_simp

theorem keepVertices_edit_ratio_tendsto_zero
    {I : Type*} {W : I → Type*} [∀ i, DecidableEq (W i)] [∀ i, Fintype (W i)]
    (G : ∀ i, RGraph (W i) r) (hr : 1 ≤ r) (hn : ∀ i, 0 < Fintype.card (W i))
    (S : ∀ i, Finset (W i)) (l : Filter I)
    (hsmall : Tendsto (fun i => ((Finset.univ \ S i).card : ℝ) /
      Fintype.card (W i)) l (𝓝 0)) :
    Tendsto (fun i => (((G i).edgeSymmDifference ((G i).keepVertices (S i))).edges.card : ℝ) /
      (Fintype.card (W i) : ℝ) ^ r) l (𝓝 0) := by
  apply squeeze_zero (fun i => by positivity)
    (fun i => (G i).keepVertices_edit_ratio_le hr (hn i) (S i)) hsmall

theorem keepVertices_edge_ratio_tendsto
    {I : Type*} {W : I → Type*} [∀ i, DecidableEq (W i)] [∀ i, Fintype (W i)]
    (G : ∀ i, RGraph (W i) r) (hr : 1 ≤ r) (hn : ∀ i, 0 < Fintype.card (W i))
    (S : ∀ i, Finset (W i)) (l : Filter I)
    (hsmall : Tendsto (fun i => ((Finset.univ \ S i).card : ℝ) /
      Fintype.card (W i)) l (𝓝 0))
    {Λ : ℝ} (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (W i) : ℝ) ^ r) l (𝓝 Λ)) :
    Tendsto (fun i => (((G i).keepVertices (S i)).edges.card : ℝ) /
      (Fintype.card (W i) : ℝ) ^ r) l (𝓝 Λ) := by
  have hedit := keepVertices_edit_ratio_tendsto_zero G hr hn S l hsmall
  have heq i : ((G i).edges.card : ℝ) -
      ((G i).edgeSymmDifference ((G i).keepVertices (S i))).edges.card =
        ((G i).keepVertices (S i)).edges.card := by
    have h : (((G i).keepVertices (S i)).edges.card : ℝ) +
        ((G i).edgeSymmDifference ((G i).keepVertices (S i))).edges.card = (G i).edges.card := by
      exact_mod_cast (G i).keepVertices_card_add_edit (S i)
    linarith
  simpa only [← sub_div, heq, sub_zero] using hlim.sub hedit

end TuranUniversality.RGraph
