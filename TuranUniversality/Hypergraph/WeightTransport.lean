module

public import TuranUniversality.Hypergraph.Polynomial

@[expose] public section

/-! # Probability weights transported along an actual embedding -/

namespace TuranUniversality

open scoped BigOperators

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [Fintype V]
  [DecidableEq W] [Fintype W]

def pushWeights (f : V → W) (x : V → ℝ) (w : W) : ℝ :=
  ∑ v, if f v = w then x v else 0

theorem pushWeights_nonneg (f : V → W) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (w : W) :
    0 ≤ pushWeights f x w := by
  apply Finset.sum_nonneg
  intro v _
  split
  · exact hx v
  · exact le_refl 0

theorem pushWeights_sum (f : V → W) (x : V → ℝ) :
    (∑ w, pushWeights f x w) = ∑ v, x v := by
  unfold pushWeights
  rw [Finset.sum_comm]
  simp

theorem pushWeights_probability (f : V → W) (x : V → ℝ) (hx : ProbabilityWeights x) :
    ProbabilityWeights (pushWeights f x) :=
  ⟨pushWeights_nonneg f x hx.1, (pushWeights_sum f x).trans hx.2⟩

theorem pushWeights_apply (f : V → W) (hf : Function.Injective f) (x : V → ℝ) (v : V) :
    pushWeights f x (f v) = x v := by
  unfold pushWeights
  simp only [hf.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

namespace RGraph

theorem embedding_weight_transport {r : ℕ} (F : RGraph V r) (G : RGraph W r)
    (f : V → W) (hf : F.IsEmbedding G f) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    F.edgePolynomial x ≤ G.edgePolynomial (pushWeights f x) := by
  have hprod (e : Finset V) : (∏ w ∈ e.image f, pushWeights f x w) = ∏ v ∈ e, x v := by
    rw [Finset.prod_image (fun a _ b _ h => hf.1 h)]
    exact Finset.prod_congr rfl (fun v _ => pushWeights_apply f hf.1 x v)
  have heq : (∑ e ∈ F.edges.image (fun e => e.image f), ∏ w ∈ e, pushWeights f x w) =
      F.edgePolynomial x := by
    rw [Finset.sum_image (fun a _ b _ h => Finset.image_injective hf.1 h)]
    exact Finset.sum_congr rfl (fun e _ => hprod e)
  rw [← heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact hf.2 d hd
  · exact fun e _ _ => Finset.prod_nonneg fun w _ => pushWeights_nonneg f x hx w

end RGraph
end TuranUniversality
