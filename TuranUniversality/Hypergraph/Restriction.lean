module

public import TuranUniversality.Hypergraph.Compression
public import TuranUniversality.Density.Extremal

@[expose] public section

/-! # Restriction to a finite weighted support -/

open scoped BigOperators

namespace TuranUniversality

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

namespace RGraph

@[simp] theorem mem_pullback [Fintype V] (G : RGraph W r) (f : V ↪ W)
    (e : Finset V) :
    e ∈ (G.pullback f).edges ↔ e.card = r ∧ e.map f ∈ G.edges := by
  classical
  simp [pullback, Finset.mem_powersetCard]

theorem pullback_isHom [Fintype V] (G : RGraph W r) (f : V ↪ W) :
    (G.pullback f).IsHom G f := by
  intro e he
  simpa [Finset.map_eq_image] using ((G.mem_pullback f e).mp he).2

theorem pullback_edges_image [Fintype V] (G : RGraph W r) (f : V ↪ W) :
    (G.pullback f).edges.image (fun e => e.map f) =
      G.edges.filter (fun e => ∀ x ∈ e, x ∈ Set.range f) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_filter.mpr ⟨((G.mem_pullback f d).mp hd).2, ?_⟩
    intro x hx
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hx
    exact ⟨v, hv⟩
  · intro he
    obtain ⟨he, hrange⟩ := Finset.mem_filter.mp he
    let d := e.preimage f f.injective.injOn
    have him : d.map f = e := by
      rw [Finset.map_eq_image, Finset.image_preimage]
      exact Finset.filter_true_of_mem (fun x hx => hrange x hx)
    have hd : d.card = r := by
      calc
        d.card = (d.map f).card := (Finset.card_map _).symm
        _ = e.card := congrArg Finset.card him
        _ = r := G.uniform e he
    exact Finset.mem_image.mpr ⟨d,
      (G.mem_pullback f d).mpr ⟨hd, him ▸ he⟩, him⟩

/-- Pulling a graph back along an injection preserves its weighted polynomial
when all omitted vertices have weight zero. -/
theorem edgePolynomial_pullback [Fintype V] (G : RGraph W r) (f : V ↪ W)
    (x : W → ℝ) (hz : ∀ w, w ∉ Set.range f → x w = 0) :
    (G.pullback f).edgePolynomial (x ∘ f) = G.edgePolynomial x := by
  classical
  unfold edgePolynomial
  calc
    (∑ e ∈ (G.pullback f).edges, ∏ v ∈ e, (x ∘ f) v) =
        ∑ e ∈ (G.pullback f).edges, ∏ w ∈ e.map f, x w := by
      simp only [Finset.prod_map, Function.comp_apply]
    _ = ∑ e ∈ (G.pullback f).edges.image (fun e => e.map f), ∏ w ∈ e, x w := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact Finset.map_injective f hab
    _ = ∑ e ∈ G.edges.filter (fun e => ∀ w ∈ e, w ∈ Set.range f), ∏ w ∈ e, x w := by
      rw [G.pullback_edges_image f]
    _ = ∑ e ∈ G.edges, ∏ w ∈ e, x w := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs with h
      · rfl
      · push Not at h
        obtain ⟨w, hw, hn⟩ := h
        exact (Finset.prod_eq_zero hw (hz w hn)).symm

end RGraph

/-- Vertex type of the finite support of a weighting. -/
abbrev WeightVertex [Fintype V] (x : V → ℝ) := {v : V // v ∈ weightSupport x}

omit [DecidableEq V] in
@[simp] theorem mem_weightSupport [Fintype V] (x : V → ℝ) (v : V) :
    v ∈ weightSupport x ↔ x v ≠ 0 := by
  classical
  simp [weightSupport]

omit [DecidableEq V] in
theorem weightSupport_range [Fintype V] (x : V → ℝ) (v : V) :
    v ∈ Set.range (Subtype.val : WeightVertex x → V) ↔ x v ≠ 0 := by
  simp

noncomputable def RGraph.supportGraph [Fintype V] (G : RGraph V r) (x : V → ℝ) :
    RGraph (WeightVertex x) r :=
  G.pullback (Function.Embedding.subtype _)

theorem RGraph.supportGraph_isHom [Fintype V] (G : RGraph V r) (x : V → ℝ) :
    (G.supportGraph x).IsHom G Subtype.val :=
  G.pullback_isHom _

theorem RGraph.supportGraph_polynomial [Fintype V] (G : RGraph V r) (x : V → ℝ) :
    (G.supportGraph x).edgePolynomial (fun v => x v.val) = G.edgePolynomial x := by
  classical
  apply G.edgePolynomial_pullback
  intro v hv
  simpa [weightSupport_range] using hv

omit [DecidableEq V] in
theorem support_probability [Fintype V] (x : V → ℝ) (hx : ProbabilityWeights x) :
    ProbabilityWeights (fun v : WeightVertex x => x v.val) := by
  classical
  refine ⟨fun v => hx.1 v.val, ?_⟩
  calc
    (∑ v : WeightVertex x, x v.val) = ∑ v : V, x v := by
      apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
      · intro v hv
        simpa [weightSupport_range] using hv
      · intro v
        rfl
    _ = 1 := hx.2

theorem RGraph.CoversWeightSupport.support_covers_pairs [Fintype V]
    (G : RGraph V r) (x : V → ℝ) (h : G.CoversWeightSupport x) :
    (G.supportGraph x).CoversPairs := by
  classical
  intro u v huv
  have hune := (mem_weightSupport x u.val).mp u.property
  have hvne := (mem_weightSupport x v.val).mp v.property
  obtain ⟨e, he, heu, hev, hew⟩ := h u.val v.val hune hvne
    (fun eq => huv (Subtype.ext eq))
  let f : WeightVertex x ↪ V := Function.Embedding.subtype _
  have hi := Finset.ext_iff.mp (G.pullback_edges_image f) e
  simp only [Finset.mem_image, Finset.mem_filter] at hi
  obtain ⟨d, hd, hde⟩ := hi.mpr ⟨he,
    fun w hw => (weightSupport_range x w).mpr (hew w hw)⟩
  refine ⟨d, hd, ?_, ?_⟩
  · rw [← hde] at heu
    exact (Finset.mem_map' f).mp heu
  · rw [← hde] at hev
    exact (Finset.mem_map' f).mp hev

end TuranUniversality
