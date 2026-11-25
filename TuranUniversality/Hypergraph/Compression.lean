module

public import TuranUniversality.Hypergraph.Polynomial
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-!
# Finite support compression

The proof uses induction on positive support, rather than the existence of an
optimal weighting. Each step transfers the mass of one uncovered vertex to the
other endpoint with the larger linear coefficient.
-/

open scoped BigOperators

namespace TuranUniversality

universe u
variable {V : Type u} [DecidableEq V] {r : ℕ}

def RGraph.linkPolynomial (G : RGraph V r) (x : V → ℝ) (u : V) : ℝ :=
  ∑ e ∈ G.edges.filter (fun e => u ∈ e), ∏ v ∈ e.erase u, x v

theorem prod_update_affine (e : Finset V) (x : V → ℝ) (u : V) (a : ℝ) :
    (∏ v ∈ e, Function.update x u a v) =
      (∏ v ∈ e, x v) +
        (a - x u) * (if u ∈ e then ∏ v ∈ e.erase u, x v else 0) := by
  by_cases hu : u ∈ e
  · rw [Finset.prod_update_of_mem hu, ite_eq_left hu,
      Finset.sdiff_singleton_eq_erase,
      ← Finset.mul_prod_erase e x hu]
    ring
  · simp [Finset.prod_update_of_notMem hu, hu]

theorem RGraph.edgePolynomial_update (G : RGraph V r) (x : V → ℝ)
    (u : V) (a : ℝ) :
    G.edgePolynomial (Function.update x u a) =
      G.edgePolynomial x + (a - x u) * G.linkPolynomial x u := by
  unfold RGraph.edgePolynomial RGraph.linkPolynomial
  simp_rw [prod_update_affine]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]

/-- Move all of v's mass to u. -/
def transferWeight (x : V → ℝ) (u v : V) : V → ℝ :=
  Function.update (Function.update x v 0) u (x u + x v)

theorem RGraph.linkPolynomial_update_of_uncovered (G : RGraph V r)
    (x : V → ℝ) (u v : V)
    (h : ∀ e ∈ G.edges, u ∈ e → v ∉ e) :
    G.linkPolynomial (Function.update x v 0) u = G.linkPolynomial x u := by
  unfold RGraph.linkPolynomial
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_filter.mp he
  apply Finset.prod_congr rfl
  intro w hw
  apply Function.update_of_ne
  intro hwv
  subst w
  exact h e he'.1 he'.2 (Finset.mem_of_mem_erase hw)

theorem RGraph.edgePolynomial_transfer (G : RGraph V r)
    (x : V → ℝ) (u v : V) (huv : u ≠ v)
    (h : ∀ e ∈ G.edges, u ∈ e → v ∉ e) :
    G.edgePolynomial (transferWeight x u v) = G.edgePolynomial x +
      x v * (G.linkPolynomial x u - G.linkPolynomial x v) := by
  unfold transferWeight
  rw [G.edgePolynomial_update, G.edgePolynomial_update,
    G.linkPolynomial_update_of_uncovered x u v h,
    Function.update_of_ne huv]
  ring

theorem sum_update_affine [Fintype V] (x : V → ℝ) (u : V) (a : ℝ) :
    (∑ v, Function.update x u a v) = (∑ v, x v) + a - x u := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ u)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.add_sum_erase Finset.univ x (Finset.mem_univ u)]
  ring

theorem transferWeight_probability [Fintype V] (x : V → ℝ)
    (hx : ProbabilityWeights x) (u v : V) (huv : u ≠ v) :
    ProbabilityWeights (transferWeight x u v) := by
  constructor
  · intro w
    by_cases hwu : w = u
    · subst w
      simp [transferWeight, hx.1 u, hx.1 v, add_nonneg]
    · by_cases hwv : w = v
      · subst w
        simp [transferWeight, Ne.symm huv]
      · simpa [transferWeight, hwu, hwv] using hx.1 w
  · unfold transferWeight
    rw [sum_update_affine, sum_update_affine, Function.update_of_ne huv, hx.2]
    ring

noncomputable def weightSupport [Fintype V] (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => x v ≠ 0)

theorem transferWeight_support_subset [Fintype V] (x : V → ℝ)
    (u v : V) (hu : x u ≠ 0) :
    weightSupport (transferWeight x u v) ⊆ weightSupport x := by
  classical
  intro w hw
  simp only [weightSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  by_cases hwu : w = u
  · simpa [hwu] using hu
  · by_cases hwv : w = v
    · subst w
      simp [transferWeight, hwu] at hw
    · simpa [transferWeight, hwu, hwv] using hw

theorem transferWeight_support_card_lt [Fintype V] (x : V → ℝ)
    (u v : V) (huv : u ≠ v) (hu : x u ≠ 0) (hv : x v ≠ 0) :
    (weightSupport (transferWeight x u v)).card < (weightSupport x).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨transferWeight_support_subset x u v hu, ?_⟩
  intro heq
  have hm : v ∈ weightSupport x := by simp [weightSupport, hv]
  rw [← heq] at hm
  have hn := (Finset.mem_filter.mp hm).2
  apply hn
  simp [transferWeight, Ne.symm huv]

/-- The part of a graph whose edges lie entirely in the nonzero support. -/
noncomputable def RGraph.activeGraph (G : RGraph V r) (x : V → ℝ) : RGraph V r := by
  classical
  exact ⟨G.edges.filter (fun e => ∀ v ∈ e, x v ≠ 0),
    fun e he => G.uniform e (Finset.mem_filter.mp he).1⟩

@[simp] theorem RGraph.mem_activeGraph (G : RGraph V r) (x : V → ℝ) (e : Finset V) :
    e ∈ (G.activeGraph x).edges ↔ e ∈ G.edges ∧ ∀ v ∈ e, x v ≠ 0 := by
  classical
  simp [RGraph.activeGraph]

theorem RGraph.activeGraph_polynomial (G : RGraph V r) (x : V → ℝ) :
    (G.activeGraph x).edgePolynomial x = G.edgePolynomial x := by
  classical
  unfold RGraph.activeGraph RGraph.edgePolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with h
  · rfl
  · push Not at h
    obtain ⟨v, hv, hz⟩ := h
    exact (Finset.prod_eq_zero hv hz).symm

/-- The graph induced by the nonzero weight support covers all pairs. -/
def RGraph.CoversWeightSupport (G : RGraph V r) (x : V → ℝ) : Prop :=
  ∀ u v, x u ≠ 0 → x v ≠ 0 → u ≠ v →
    ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e ∧ ∀ w ∈ e, x w ≠ 0

/-- One mass transfer strictly reduces the support if its induced graph does not
cover every pair, without decreasing the edge polynomial. -/
theorem RGraph.compression_step [Fintype V] (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) (hc : ¬ G.CoversWeightSupport x) :
    ∃ y, ProbabilityWeights y ∧ G.edgePolynomial x ≤ G.edgePolynomial y ∧
      (weightSupport y).card < (weightSupport x).card := by
  classical
  simp only [RGraph.CoversWeightSupport, not_forall] at hc
  obtain ⟨u, v, hu, hv, huv, hpair⟩ := hc
  let H := G.activeGraph x
  have hunc : ∀ e ∈ H.edges, u ∈ e → v ∉ e := by
    intro e he heu hev
    obtain ⟨heG, hew⟩ := (G.mem_activeGraph x e).mp he
    exact hpair ⟨e, heG, heu, hev, hew⟩
  have hunc' : ∀ e ∈ H.edges, v ∈ e → u ∉ e := by
    intro e he hev heu
    exact hunc e he heu hev
  have hsub : H.edges ⊆ G.edges := fun e he => ((G.mem_activeGraph x e).mp he).1
  have hsame : H.edgePolynomial x = G.edgePolynomial x :=
    G.activeGraph_polynomial x
  by_cases hlink : H.linkPolynomial x v ≤ H.linkPolynomial x u
  · let y := transferWeight x u v
    have hy : ProbabilityWeights y := transferWeight_probability x hx u v huv
    refine ⟨y, hy, ?_, transferWeight_support_card_lt x u v huv hu hv⟩
    calc
      G.edgePolynomial x = H.edgePolynomial x := hsame.symm
      _ ≤ H.edgePolynomial y := by
        rw [H.edgePolynomial_transfer x u v huv hunc]
        exact le_add_of_nonneg_right (mul_nonneg (hx.1 v) (sub_nonneg.mpr hlink))
      _ ≤ G.edgePolynomial y := H.edgePolynomial_mono G hsub hy.1
  · let y := transferWeight x v u
    have hy : ProbabilityWeights y := transferWeight_probability x hx v u huv.symm
    refine ⟨y, hy, ?_, transferWeight_support_card_lt x v u huv.symm hv hu⟩
    calc
      G.edgePolynomial x = H.edgePolynomial x := hsame.symm
      _ ≤ H.edgePolynomial y := by
        rw [H.edgePolynomial_transfer x v u huv.symm hunc']
        exact le_add_of_nonneg_right
          (mul_nonneg (hx.1 u) (sub_nonneg.mpr (le_of_not_ge hlink)))
      _ ≤ G.edgePolynomial y := H.edgePolynomial_mono G hsub hy.1

/-- Every probability weighting can be compressed to one whose induced support
covers pairs, while weakly increasing the edge polynomial. No maximizer is used. -/
theorem RGraph.exists_compressed_weights [Fintype V] (G : RGraph V r)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    ∃ y, ProbabilityWeights y ∧ G.edgePolynomial x ≤ G.edgePolynomial y ∧
      G.CoversWeightSupport y := by
  classical
  generalize hn : (weightSupport x).card = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hc : G.CoversWeightSupport x
    · exact ⟨x, hx, le_rfl, hc⟩
    · obtain ⟨y, hy, hxy, hcard⟩ := G.compression_step x hx hc
      obtain ⟨z, hz, hyz, hzc⟩ := ih (weightSupport y).card (hn ▸ hcard) y hy rfl
      exact ⟨z, hz, hxy.trans hyz, hzc⟩

end TuranUniversality
