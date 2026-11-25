module

public import TuranUniversality.Hypergraph.Degree
public import TuranUniversality.Uniformity.MassOptimization
public import TuranUniversality.Density.FamilyLower
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section

/-! # Uniform link bounds near a global polynomial maximum

Putting a small extra mass at any single vertex gives a quantitative bound
which is uniform in the finite carrier. It applies to actual completions
of canonical graphs and avoids an unproved differentiability assumption
for a varying sequence of hypergraphs.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality

namespace Density

noncomputable def linkStep (r : ℕ) (ε : ℝ) : ℝ := min (1 / 2) (ε / (2 * ((r : ℝ) + 1)))

noncomputable def linkTolerance (r : ℕ) (ε : ℝ) : ℝ := linkStep r ε * ε / 2

theorem linkStep_pos (r : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < linkStep r ε := by
  unfold linkStep
  apply lt_min
  · norm_num
  · positivity

theorem linkTolerance_pos (r : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < linkTolerance r ε := by
  unfold linkTolerance
  exact div_pos (mul_pos (linkStep_pos r hε) hε) (by norm_num)

theorem linkStep_le_one (r : ℕ) (ε : ℝ) : linkStep r ε ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

theorem mul_linkStep_le (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (r : ℝ) * linkStep r ε ≤ ε / 2 := by
  have h := (min_le_right (1 / 2 : ℝ) (ε / (2 * ((r : ℝ) + 1))))
  have hd : 0 < 2 * ((r : ℝ) + 1) := by positivity
  have hprod := (le_div_iff₀ hd).mp h
  have hs := linkStep_pos r hε
  change linkStep r ε * (2 * ((r : ℝ) + 1)) ≤ ε at hprod
  nlinarith

end Density

namespace RGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

theorem edgePolynomial_le_one (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) : G.edgePolynomial x ≤ 1 := by
  have hb := (familyTuranDensity_lower_of_homFree ∅ G
    (familyHomFree_empty_family G) x hx).trans (familyTuranDensity_le_one ∅)
  have hf : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hp := G.edgePolynomial_nonneg hx.1
  nlinarith

theorem linkPolynomial_le_one (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) (v : V) : G.linkPolynomial x v ≤ 1 := by
  rw [← G.linkGraph_polynomial]
  exact (G.linkGraph v).edgePolynomial_le_one x hx

theorem linkPolynomial_scale (G : RGraph V r) (x : V → ℝ) (c : ℝ) (v : V) :
    G.linkPolynomial (fun w => c * x w) v = c ^ (r - 1) * G.linkPolynomial x v := by
  rw [← G.linkGraph_polynomial, (G.linkGraph v).edgePolynomial_scale,
    G.linkGraph_polynomial]

def vertexMixture (x : V → ℝ) (v : V) (s : ℝ) : V → ℝ :=
  Function.update (fun w => (1 - s) * x w) v ((1 - s) * x v + s)

theorem vertexMixture_probability (x : V → ℝ) (hx : ProbabilityWeights x)
    (v : V) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ProbabilityWeights (vertexMixture x v s) := by
  constructor
  · intro w
    by_cases hw : w = v
    · subst w
      simp only [vertexMixture, Function.update_self]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (hx.1 v)) hs
    · simp only [vertexMixture, Function.update_of_ne hw]
      exact mul_nonneg (sub_nonneg.mpr hs1) (hx.1 w)
  · unfold vertexMixture
    rw [sum_update_affine, ← Finset.mul_sum, hx.2]
    ring

theorem edgePolynomial_vertexMixture (G : RGraph V r) (x : V → ℝ) (v : V) (s : ℝ) :
    G.edgePolynomial (vertexMixture x v s) =
      (1 - s) ^ r * G.edgePolynomial x +
        s * (1 - s) ^ (r - 1) * G.linkPolynomial x v := by
  unfold vertexMixture
  rw [G.edgePolynomial_update, G.edgePolynomial_scale, G.linkPolynomial_scale]
  ring

theorem linkPolynomial_step_bound (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) {Λ : ℝ}
    (hbound : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ Λ)
    (v : V) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s * (G.linkPolynomial x v - (r : ℝ) * Λ) ≤
      Λ - G.edgePolynomial x + (r : ℝ) * s ^ 2 := by
  have hp := G.edgePolynomial_nonneg hx.1
  have hpΛ := hbound x hx
  have hL := G.linkPolynomial_nonneg hx.1 v
  have hL1 := G.linkPolynomial_le_one x hx v
  have hP := hbound (vertexMixture x v s) (vertexMixture_probability x hx v hs hs1)
  rw [G.edgePolynomial_vertexMixture] at hP
  have bern (k : ℕ) : 1 - (k : ℝ) * s ≤ (1 - s) ^ k := by
    have h := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 1 - s by linarith) k
    convert h using 1 <;> ring
  have hp' := mul_le_mul_of_nonneg_right (bern r) hp
  have hL' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (bern (r - 1)) hL) hs
  have hrem := mul_le_mul_of_nonneg_left hL1
    (mul_nonneg (Nat.cast_nonneg (r - 1)) (sq_nonneg s))
  have hr : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hrem' := mul_le_mul_of_nonneg_right hr (sq_nonneg s)
  have hpΛ' := mul_le_mul_of_nonneg_left hpΛ (mul_nonneg hs (Nat.cast_nonneg r))
  nlinarith

theorem linkPolynomial_le_near_max (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) {Λ ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ Λ)
    (hnear : Λ - Density.linkTolerance r ε ≤ G.edgePolynomial x) (v : V) :
    G.linkPolynomial x v ≤ (r : ℝ) * Λ + ε := by
  have hs := Density.linkStep_pos r hε
  have h := G.linkPolynomial_step_bound x hx hbound v hs.le (Density.linkStep_le_one r ε)
  have hc := mul_le_mul_of_nonneg_right (Density.mul_linkStep_le r hε) hs.le
  dsimp [Density.linkTolerance] at hnear
  nlinarith

end RGraph

namespace Density

theorem eventually_uniform_link_bound {r : ℕ} {V : ℕ → Type*}
    [∀ n, DecidableEq (V n)] [∀ n, Fintype (V n)]
    (G : ∀ n, RGraph (V n) r) (x : ∀ n, V n → ℝ)
    (hx : ∀ n, ProbabilityWeights (x n)) {Λ : ℝ}
    (hbound : ∀ n y, ProbabilityWeights y → (G n).edgePolynomial y ≤ Λ)
    (hlim : Tendsto (fun n => (G n).edgePolynomial (x n)) atTop (𝓝 Λ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v, (G n).linkPolynomial (x n) v ≤ (r : ℝ) * Λ + ε := by
  have hη := linkTolerance_pos r hε
  have he := (tendsto_order.1 hlim).1 (Λ - linkTolerance r ε) (by linarith)
  filter_upwards [he] with n hn
  exact fun v => (G n).linkPolynomial_le_near_max (x n) (hx n) hε (hbound n) hn.le v

end Density

end TuranUniversality
