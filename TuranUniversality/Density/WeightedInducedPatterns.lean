module

public import TuranUniversality.Density.WeightedHomPushforward
public import TuranUniversality.Hypergraph.FiniteBasis
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Full induced sampling distributions and finite inclusion-exclusion

The sampled graph is the actual complete inverse image on the entire source
carrier. Vertex collisions and isolated source vertices are retained. Its
induced distribution is a finite linear combination of ordinary weighted
homomorphism coordinates, with the usual powerset inclusion-exclusion signs.
-/

open scoped BigOperators

namespace TuranUniversality.Density

theorem indicator_finset_forall {A : Type*} (s : Finset A) (p : A → Prop)
    [DecidablePred p] :
    (if ∀ a ∈ s, p a then (1 : ℝ) else 0) = ∏ a ∈ s, if p a then (1 : ℝ) else 0 := by
  classical
  by_cases h : ∀ a ∈ s, p a
  · rw [if_pos h]
    symm
    exact Finset.prod_eq_one (fun a ha => if_pos (h a ha))
  · have hn := h
    push_neg at hn
    obtain ⟨a, ha, hn⟩ := hn
    rw [if_neg h]
    exact (Finset.prod_eq_zero ha (if_neg hn)).symm

theorem weightedMean_const_mul [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (c : ℝ) (F : (A → V) → ℝ) :
    weightedMean x (fun f => c * F f) = c * weightedMean x F := by
  simp only [weightedMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

end TuranUniversality.Density

namespace TuranUniversality.RGraph

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {r : ℕ}

def nonedges (K : RGraph U r) : Finset (Finset U) :=
  Finset.univ.powersetCard r \ K.edges

def withExtraEdges (K : RGraph U r) (S : Finset (Finset U)) : RGraph U r where
  edges := K.edges ∪ S.filter (fun e => e.card = r)
  uniform e he := by
    rcases Finset.mem_union.mp he with he | he
    · exact K.uniform e he
    · exact (Finset.mem_filter.mp he).2

theorem withExtraEdges_edges (K : RGraph U r) (S : Finset (Finset U))
    (hS : S ⊆ K.nonedges) : (K.withExtraEdges S).edges = K.edges ∪ S := by
  change K.edges ∪ _ = K.edges ∪ S
  congr 1
  apply Finset.filter_true_of_mem
  intro e he
  exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (hS he)).1).2

theorem isHom_withExtraEdges_iff (K : RGraph U r) (G : RGraph V r)
    (S : Finset (Finset U)) (hS : S ⊆ K.nonedges) (f : U → V) :
    (K.withExtraEdges S).IsHom G f ↔ K.IsHom G f ∧ ∀ e ∈ S, e.image f ∈ G.edges := by
  simp only [IsHom, withExtraEdges_edges K S hS, Finset.mem_union, or_imp,
    forall_and]

theorem inverseImage_eq_iff (K : RGraph U r) (G : RGraph V r) (f : U → V) :
    G.inverseImage f = K ↔ K.IsHom G f ∧ ∀ e ∈ K.nonedges, e.image f ∉ G.edges := by
  constructor
  · intro h
    constructor
    · intro e he
      have hm : e ∈ (G.inverseImage f).edges := h.symm ▸ he
      exact ((G.mem_inverseImage f e).mp hm).2
    · intro e he hh
      have hN := Finset.mem_sdiff.mp he
      have hcard := (Finset.mem_powersetCard.mp hN.1).2
      have hm : e ∈ (G.inverseImage f).edges := (G.mem_inverseImage f e).mpr ⟨hcard, hh⟩
      exact hN.2 (h ▸ hm)
  · rintro ⟨hK, hN⟩
    apply RGraph.ext
    ext e
    constructor
    · intro he
      have hm := (G.mem_inverseImage f e).mp he
      by_contra hn
      exact hN e (Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, hm.1⟩, hn⟩) hm.2
    · intro he
      exact (G.mem_inverseImage f e).mpr ⟨K.uniform e he, hK e he⟩

noncomputable def inducedIndicator (K : RGraph U r) (G : RGraph V r) (f : U → V) : ℝ :=
  if G.inverseImage f = K then 1 else 0

noncomputable def inducedDensity (K : RGraph U r) (G : RGraph V r) (x : V → ℝ) : ℝ :=
  weightedMean x (K.inducedIndicator G)

noncomputable def inducedPolynomial (K : RGraph U r) (z : RGraph U r → ℝ) : ℝ :=
  ∑ S ∈ K.nonedges.powerset, (-1 : ℝ) ^ S.card * z (K.withExtraEdges S)

theorem homIndicator_withExtraEdges (K : RGraph U r) (G : RGraph V r)
    (S : Finset (Finset U)) (hS : S ⊆ K.nonedges) (f : U → V) :
    (K.withExtraEdges S).homIndicator G f = K.homIndicator G f *
      ∏ e ∈ S, if e.image f ∈ G.edges then (1 : ℝ) else 0 := by
  rw [← indicator_finset_forall]
  simp only [homIndicator, isHom_withExtraEdges_iff K G S hS f]
  by_cases hK : K.IsHom G f <;>
    by_cases hS : ∀ e ∈ S, e.image f ∈ G.edges <;> simp [hK, hS]

theorem inducedIndicator_factor (K : RGraph U r) (G : RGraph V r) (f : U → V) :
    K.inducedIndicator G f = K.homIndicator G f *
      ∏ e ∈ K.nonedges, (1 - if e.image f ∈ G.edges then (1 : ℝ) else 0) := by
  have hpoint (e : Finset U) :
      (1 - if e.image f ∈ G.edges then (1 : ℝ) else 0) =
        if e.image f ∉ G.edges then (1 : ℝ) else 0 := by
    by_cases he : e.image f ∈ G.edges <;> simp [he]
  simp_rw [hpoint]
  rw [← indicator_finset_forall]
  simp only [inducedIndicator, inverseImage_eq_iff, homIndicator]
  by_cases hK : K.IsHom G f <;>
    by_cases hN : ∀ e ∈ K.nonedges, e.image f ∉ G.edges <;> simp [hK, hN]

theorem inducedIndicator_inclusionExclusion (K : RGraph U r) (G : RGraph V r)
    (f : U → V) :
    K.inducedIndicator G f =
      ∑ S ∈ K.nonedges.powerset, (-1 : ℝ) ^ S.card * (K.withExtraEdges S).homIndicator G f := by
  rw [inducedIndicator_factor, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [homIndicator_withExtraEdges K G S (Finset.mem_powerset.mp hS) f]
  ring

/-- The full induced sampling probability is an explicit finite polynomial
in actual ordinary weighted homomorphism densities. -/
theorem inducedDensity_eq_polynomial (K : RGraph U r) (G : RGraph V r) (x : V → ℝ) :
    K.inducedDensity G x = K.inducedPolynomial (fun L => L.weightedHomDensity G x) := by
  unfold inducedDensity inducedPolynomial
  calc
    _ = weightedMean x (fun f => ∑ S ∈ K.nonedges.powerset,
        (-1 : ℝ) ^ S.card * (K.withExtraEdges S).homIndicator G f) :=
      weightedMean_congr x (K.inducedIndicator_inclusionExclusion G)
    _ = ∑ S ∈ K.nonedges.powerset,
        weightedMean x (fun f => (-1 : ℝ) ^ S.card * (K.withExtraEdges S).homIndicator G f) :=
      weightedMean_sum x _ _
    _ = _ := by simp only [weightedMean_const_mul, weightedHomDensity]

theorem inducedDensity_nonneg (K : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) : 0 ≤ K.inducedDensity G x := by
  classical
  unfold inducedDensity weightedMean
  exact Finset.sum_nonneg (fun f _ => mul_nonneg
    (Finset.prod_nonneg fun _ _ => hx _) (by unfold inducedIndicator; split <;> norm_num))

theorem sum_inducedIndicator (G : RGraph V r) (f : U → V) :
    (∑ K : RGraph U r, K.inducedIndicator G f) = 1 := by
  classical
  simp [inducedIndicator, eq_comm]

theorem sum_inducedDensity (G : RGraph V r) (x : V → ℝ) (hx : ProbabilityWeights x) :
    (∑ K : RGraph U r, K.inducedDensity G x) = 1 := by
  classical
  unfold inducedDensity
  rw [← weightedMean_sum]
  calc
    _ = weightedMean x (fun _ : U → V => (1 : ℝ)) :=
      weightedMean_congr x (G.sum_inducedIndicator)
    _ = 1 := weightedMean_const x hx.2 1

theorem weightedMean_inverseImage (G : RGraph V r) (x : V → ℝ) (S : RGraph U r → ℝ) :
    weightedMean x (fun f : U → V => S (G.inverseImage f)) =
      ∑ K : RGraph U r, S K * K.inducedDensity G x := by
  classical
  calc
    _ = weightedMean x (fun f : U → V =>
        ∑ K : RGraph U r, S K * K.inducedIndicator G f) := by
      apply weightedMean_congr
      intro f
      simp [inducedIndicator, mul_ite]
    _ = ∑ K : RGraph U r, weightedMean x (fun f => S K * K.inducedIndicator G f) :=
      weightedMean_sum x _ _
    _ = _ := by simp only [weightedMean_const_mul, inducedDensity]

theorem weightedMean_inverseImage_polynomial (G : RGraph V r) (x : V → ℝ)
    (S : RGraph U r → ℝ) :
    weightedMean x (fun f : U → V => S (G.inverseImage f)) =
      ∑ K : RGraph U r, S K * K.inducedPolynomial (fun L => L.weightedHomDensity G x) := by
  rw [weightedMean_inverseImage]
  simp_rw [inducedDensity_eq_polynomial]

theorem continuous_inducedPolynomial (K : RGraph U r) :
    Continuous (K.inducedPolynomial : (RGraph U r → ℝ) → ℝ) := by
  unfold inducedPolynomial
  fun_prop

end TuranUniversality.RGraph
