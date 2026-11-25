module

public import TuranUniversality.Density.WeightedHomPushforward
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Products of finite independent sampling laws -/

open scoped BigOperators

namespace TuranUniversality.Density

variable {A V W : Type*} [Fintype A] [DecidableEq A] [Fintype V] [Fintype W]

theorem probabilityWeights_product (x : V → ℝ) (y : W → ℝ)
    (hx : ProbabilityWeights x) (hy : ProbabilityWeights y) :
    ProbabilityWeights (fun p : V × W => x p.1 * y p.2) := by
  refine ⟨fun p => mul_nonneg (hx.1 p.1) (hy.1 p.2), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hy.2, mul_one, hx.2]

theorem weightedMean_product (x : V → ℝ) (y : W → ℝ) (F : (A → V × W) → ℝ) :
    weightedMean (fun p : V × W => x p.1 * y p.2) F =
      weightedMean x (fun f => weightedMean y (fun g => F (fun a => (f a, g a)))) := by
  classical
  unfold weightedMean
  calc
    _ = ∑ p : (A → V) × (A → W),
        (productWeight x p.1 * productWeight y p.2) * F (fun a => (p.1 a, p.2 a)) := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow A (fun _ => V) (fun _ => W))
      intro f
      simp only [productWeight, Finset.prod_mul_distrib]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring

theorem weightedMean_product_three {Z : Type*} [Fintype Z]
    (x : V → ℝ) (y : W → ℝ) (z : Z → ℝ) (F : (A → V × (W × Z)) → ℝ) :
    weightedMean (fun p : V × (W × Z) => x p.1 * (y p.2.1 * z p.2.2)) F =
      weightedMean x (fun f => weightedMean y (fun g => weightedMean z
        (fun h => F (fun a => (f a, (g a, h a)))))) := by
  rw [weightedMean_product x (fun p : W × Z => y p.1 * z p.2) F]
  apply weightedMean_congr
  intro f
  exact weightedMean_product y z _

end TuranUniversality.Density
