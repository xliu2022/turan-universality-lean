module

public import TuranUniversality.Density.WeightedHomCoupling
public import TuranUniversality.Hypergraph.Degree
public import TuranUniversality.Structural.WeightedExpectations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Independent sampling with finitely many pinned replacements

A pinned source edge samples an actual target link. Its failure probability
is at most `(r-1)!` times the weighted missing link. A finite union bound
then produces one homomorphism whose prescribed replacements avoid every
missing edge. No independence between the different failure events is
assumed.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V] {r : ℕ}

theorem pinned_image_mem_link (D : RGraph V r) (e : Finset U) (he : e.card = r)
    (a : U) (ha : a ∈ e) (f : U → V) (y : V)
    (hm : e.image (Function.update f a y) ∈ D.edges) :
    (e.erase a).image f ∈ (D.linkGraph y).edges := by
  have hi : Set.InjOn (Function.update f a y) e :=
    Finset.card_image_iff.mp ((D.uniform _ hm).trans he.symm)
  have hy : y ∈ e.image (Function.update f a y) :=
    Finset.mem_image.mpr ⟨a, ha, Function.update_self _ _ _⟩
  have him : (e.image (Function.update f a y)).erase y = (e.erase a).image f := by
    ext v
    constructor
    · intro hv
      obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hv
      obtain ⟨c, hc, hcv⟩ := Finset.mem_image.mp hv
      have hca : c ≠ a := by
        intro h
        subst c
        exact hne (by simpa using hcv.symm)
      exact Finset.mem_image.mpr ⟨c, Finset.mem_erase.mpr ⟨hca, hc⟩,
        (Function.update_of_ne hca _ _).symm.trans hcv⟩
    · intro hv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hca, hce⟩ := Finset.mem_erase.mp hc
      have hcy : f c ≠ y := by
        intro h
        apply hca
        apply hi hce ha
        simp [hca, h]
      exact Finset.mem_erase.mpr ⟨hcy, Finset.mem_image.mpr
        ⟨c, hce, Function.update_of_ne hca _ _⟩⟩
  exact Finset.mem_image.mpr ⟨e.image (Function.update f a y),
    Finset.mem_filter.mpr ⟨hm, hy⟩, him⟩

theorem weightedMean_pinned_edge_le [Fintype U] [Fintype V]
    (D : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x)
    (e : Finset U) (he : e.card = r) (a : U) (y : V) :
    weightedMean x (fun f : U → V =>
      if a ∈ e ∧ e.image (Function.update f a y) ∈ D.edges then (1 : ℝ) else 0) ≤
      ((r - 1).factorial : ℝ) * D.linkPolynomial x y := by
  classical
  by_cases ha : a ∈ e
  · calc
      _ ≤ weightedMean x (fun f : U → V =>
          if (e.erase a).image f ∈ (D.linkGraph y).edges then (1 : ℝ) else 0) := by
        apply weightedMean_mono x hx.1
        intro f
        by_cases hm : e.image (Function.update f a y) ∈ D.edges
        · simp [ha, hm, pinned_image_mem_link D e he a ha f y hm]
        · simp only [hm, and_false, ite_false]
          split <;> norm_num
      _ = _ := by
        rw [(D.linkGraph y).weightedMean_edgeImage x hx.2 (e.erase a)
          (by rw [Finset.card_erase_of_mem ha, he]), D.linkGraph_polynomial]
  · simp only [ha, false_and, ite_false, weightedMean_const x hx.2]
    exact mul_nonneg (Nat.cast_nonneg _) (D.linkPolynomial_nonneg hx.1 y)

noncomputable def pinnedFailureCost [Fintype U]
    (J : RGraph U r) (D : RGraph V r) (S : Finset V) (f : U → V) : ℝ :=
  ∑ y ∈ S, ∑ a : U, ∑ e ∈ J.edges,
    if a ∈ e ∧ e.image (Function.update f a y) ∈ D.edges then 1 else 0

theorem pinnedFailureCost_nonneg [Fintype U]
    (J : RGraph U r) (D : RGraph V r) (S : Finset V) (f : U → V) :
    0 ≤ pinnedFailureCost J D S f := by
  classical
  unfold pinnedFailureCost
  positivity

theorem weightedMean_pinnedFailureCost_le [Fintype U] [Fintype V]
    (J : RGraph U r) (D : RGraph V r) (S : Finset V)
    (x : V → ℝ) (hx : ProbabilityWeights x) (ε : ℝ)
    (hlink : ∀ y ∈ S, D.linkPolynomial x y ≤ ε) :
    weightedMean x (pinnedFailureCost J D S) ≤
      (S.card : ℝ) * Fintype.card U * J.edges.card * (r - 1).factorial * ε := by
  unfold pinnedFailureCost
  simp only [weightedMean_sum]
  calc
    _ ≤ ∑ y ∈ S, ∑ _a : U, ∑ _e ∈ J.edges, ((r - 1).factorial : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro y hy
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro e he
      exact (weightedMean_pinned_edge_le D x hx e (J.uniform e he) a y).trans
        (mul_le_mul_of_nonneg_left (hlink y hy) (Nat.cast_nonneg _))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem exists_hom_avoiding_pinned_difference [Fintype U] [Fintype V]
    (J : RGraph U r) (G H : RGraph V r) (S : Finset V)
    (x : V → ℝ) (hx : ProbabilityWeights x) (ε : ℝ)
    (hlink : ∀ y ∈ S, (H.edgeDifference G).linkPolynomial x y ≤ ε)
    (hpos : (S.card : ℝ) * Fintype.card U * J.edges.card * (r - 1).factorial * ε <
      J.weightedHomDensity G x) :
    ∃ f : U → V, J.IsHom G f ∧ ∀ y ∈ S, ∀ a : U, ∀ e ∈ J.edges, a ∈ e →
      e.image (Function.update f a y) ∉ (H.edgeDifference G).edges := by
  classical
  by_contra! hn
  have hpoint (f : U → V) : J.homIndicator G f ≤ pinnedFailureCost J (H.edgeDifference G) S f := by
    by_cases hf : J.IsHom G f
    · obtain ⟨y, hy, a, e, he, ha, hm⟩ := hn f hf
      have h1 : (1 : ℝ) ≤ ∑ d ∈ J.edges,
          if a ∈ d ∧ d.image (Function.update f a y) ∈ (H.edgeDifference G).edges then 1 else 0 := by
        simpa only [ha, hm, and_self, ite_true] using Finset.single_le_sum
          (f := fun d : Finset U => if a ∈ d ∧
            d.image (Function.update f a y) ∈ (H.edgeDifference G).edges then (1 : ℝ) else 0)
          (fun _ _ => by positivity) he
      have h2 := Finset.single_le_sum
        (f := fun a : U => ∑ d ∈ J.edges,
          if a ∈ d ∧ d.image (Function.update f a y) ∈ (H.edgeDifference G).edges then (1 : ℝ) else 0)
        (fun _ _ => by positivity) (Finset.mem_univ a)
      have h3 := Finset.single_le_sum
        (f := fun y : V => ∑ a : U, ∑ d ∈ J.edges,
          if a ∈ d ∧ d.image (Function.update f a y) ∈ (H.edgeDifference G).edges then (1 : ℝ) else 0)
        (fun _ _ => by positivity) hy
      rw [J.homIndicator_of_hom G hf]
      exact h1.trans (h2.trans h3)
    · rw [J.homIndicator_of_not_hom G hf]
      exact pinnedFailureCost_nonneg J _ S f
  have hm := weightedMean_mono x hx.1 hpoint
  exact (not_le_of_gt hpos) (hm.trans (weightedMean_pinnedFailureCost_le J _ S x hx ε hlink))

end TuranUniversality.RGraph
