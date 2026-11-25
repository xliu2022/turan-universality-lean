module

public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-! # Edge polynomials and probability weights -/

open scoped BigOperators

namespace TuranUniversality

universe u
variable {V : Type u} [DecidableEq V]

/-- The unnormalized edge polynomial; its normalization in uniformity three is 6. -/
def RGraph.edgePolynomial {r : ℕ} (G : RGraph V r) (x : V → ℝ) : ℝ :=
  ∑ e ∈ G.edges, ∏ v ∈ e, x v

/-- A vertex probability weighting. -/
def ProbabilityWeights [Fintype V] (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1

theorem RGraph.edgePolynomial_nonneg {r : ℕ} (G : RGraph V r)
    {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) : 0 ≤ G.edgePolynomial x := by
  exact Finset.sum_nonneg (fun e _ => Finset.prod_nonneg (fun v _ => hx v))

theorem RGraph.edgePolynomial_mono {r : ℕ} (G H : RGraph V r)
    (h : G.edges ⊆ H.edges) {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) :
    G.edgePolynomial x ≤ H.edgePolynomial x := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun e _ _ => Finset.prod_nonneg (fun v _ => hx v))

theorem RGraph.edgePolynomial_uniform {r : ℕ} (G : RGraph V r) (c : ℝ) :
    G.edgePolynomial (fun _ => c) = (G.edges.card : ℝ) * c ^ r := by
  unfold RGraph.edgePolynomial
  simp only [Finset.prod_const]
  calc
    (∑ e ∈ G.edges, c ^ e.card) = ∑ _e ∈ G.edges, c ^ r :=
      Finset.sum_congr rfl (fun e he => by rw [G.uniform e he])
    _ = _ := by simp

/-- The normalized weight polynomial agrees with 6|E|/n^3 at uniform weights. -/
theorem RGraph.edgePolynomial_uniform_three {n : ℕ} (G : RGraph (Fin n) 3) :
    6 * G.edgePolynomial (fun _ => (n : ℝ)⁻¹) =
      6 * (G.edges.card : ℝ) / (n : ℝ) ^ 3 := by
  rw [G.edgePolynomial_uniform]
  simp [div_eq_mul_inv, mul_assoc]

end TuranUniversality
