module

public import TuranUniversality.Stability.Degree
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! # Weighted convergence forced by ordinary minimum degree

The uniform link lower bound and Euler's identity turn minimum degree
approaching r times the polynomial optimum into actual polynomial
convergence. Both statements allow varying finite carriers.
-/

open Filter Topology

namespace TuranUniversality.Stability

universe u v
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem MinimumDegree.uniform_link_lower {G : RGraph V r} {d : ℝ}
    (h : MinimumDegree G d) (hn : 0 < Fintype.card V) (v : V) :
    d ≤ G.linkPolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) v := by
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  rw [G.linkPolynomial_uniform, inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hn' _)).mpr (h v)

theorem edgePolynomial_near_of_minimumDegree (G : RGraph V r) (hr : 1 ≤ r)
    (hn : 0 < Fintype.card V) {Λ ε : ℝ}
    (hmin : MinimumDegree G ((r : ℝ) * Λ - ε)) :
    Λ - ε / r ≤ G.edgePolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hnear := edge_near_of_minimumDegree G hr hmin (by
    rw [mul_div_cancel₀ _ hr'] : ε ≤ (r : ℝ) * (ε / r))
  rw [G.edgePolynomial_uniform, inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hn' _)).mpr hnear

theorem polynomial_tendsto_of_minimumDegree {I : Type v} {X : I → Type u}
    [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)]
    (G : ∀ i, RGraph (X i) r) (hr : 1 ≤ r)
    (hn : ∀ i, 0 < Fintype.card (X i)) {Λ : ℝ}
    (hbound : ∀ i, (G i).edgePolynomial (fun _ => (Fintype.card (X i) : ℝ)⁻¹) ≤ Λ)
    (l : Filter I) (ε : I → ℝ) (hε : Tendsto ε l (𝓝 0))
    (hmin : ∀ i, MinimumDegree (G i) ((r : ℝ) * Λ - ε i)) :
    Tendsto (fun i => (G i).edgePolynomial (fun _ => (Fintype.card (X i) : ℝ)⁻¹))
      l (𝓝 Λ) := by
  have hlo : Tendsto (fun i => Λ - ε i / r) l (𝓝 Λ) := by
    simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (hε.div_const (r : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun i => edgePolynomial_near_of_minimumDegree (G i) hr (hn i) (hmin i)) hbound

end TuranUniversality.Stability
