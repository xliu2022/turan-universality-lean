module

public import TuranUniversality.Density.WeightedHomCoupling
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! # Edge coupling for sequences of varying finite carriers

These consequences keep the actual weighted graph coordinates. They allow
completion and repair errors to tend to zero without assuming the target
vertex type is fixed along a sequence.
-/

open Filter Topology

namespace TuranUniversality.RGraph

variable {I U : Type*} {V : I → Type*}
variable [DecidableEq U] [Fintype U]
variable [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] {r : ℕ}

theorem weightedHomDensity_sub_tendsto_zero_of_mismatch
    (F : RGraph U r) (G H : ∀ i, RGraph (V i) r)
    (x : ∀ i, V i → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I)
    (hsmall : Tendsto (fun i => ((G i).edgeSymmDifference (H i)).edgePolynomial (x i))
      l (𝓝 0)) :
    Tendsto (fun i => F.weightedHomDensity (G i) (x i) -
      F.weightedHomDensity (H i) (x i)) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun i => abs_nonneg _)
    (fun i => F.weightedHomDensity_abs_sub_le (G i) (H i) (x i) (hx i))
  simpa only [mul_zero] using hsmall.const_mul ((r.factorial : ℝ) * F.edges.card)

theorem weightedHomDensity_sub_tendsto_zero_of_completion
    (F : RGraph U r) (G H : ∀ i, RGraph (V i) r)
    (hsub : ∀ i, (G i).edges ⊆ (H i).edges)
    (x : ∀ i, V i → ℝ) (hx : ∀ i, ProbabilityWeights (x i))
    (l : Filter I) (c : ℝ)
    (hbound : ∀ i, (H i).edgePolynomial (x i) ≤ c)
    (hnear : Tendsto (fun i => (G i).edgePolynomial (x i)) l (𝓝 c)) :
    Tendsto (fun i => F.weightedHomDensity (H i) (x i) -
      F.weightedHomDensity (G i) (x i)) l (𝓝 0) := by
  have hcoef : 0 ≤ (r.factorial : ℝ) * F.edges.card := by positivity
  apply squeeze_zero
    (fun i => (F.weightedHomDensity_sub_bounds (G i) (H i) (hsub i) (x i) (hx i)).1)
    (fun i => ((F.weightedHomDensity_sub_bounds (G i) (H i) (hsub i) (x i) (hx i)).2).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (hbound i) _) hcoef))
  simpa only [sub_self, mul_zero] using
    (hnear.const_sub c).const_mul ((r.factorial : ℝ) * F.edges.card)

end TuranUniversality.RGraph
