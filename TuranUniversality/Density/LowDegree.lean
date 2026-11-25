module

public import TuranUniversality.Density.NearMaxLinks

@[expose] public section

/-! # Few low-degree vertices near a genuine polynomial maximum

This is the quantitative deletion input for the Ψ argument. It follows from
the actual single-vertex perturbation bound and Euler's identity for the
edge polynomial, so no unproved asymptotic extremal estimate is assumed.
-/

open scoped BigOperators

namespace TuranUniversality

namespace Density

noncomputable def lowDegreeTolerance (r : ℕ) (δ : ℝ) : ℝ :=
  min (linkTolerance r (δ ^ 2 / 4)) (δ ^ 2 / (4 * ((r : ℝ) + 1)))

theorem lowDegreeTolerance_pos (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < lowDegreeTolerance r δ := by
  apply lt_min
  · exact linkTolerance_pos r (by positivity)
  · positivity

end Density

namespace RGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

theorem sum_weight_mul_link (G : RGraph V r) (x : V → ℝ) :
    ∑ v, x v * G.linkPolynomial x v = (r : ℝ) * G.edgePolynomial x := by
  simp only [linkPolynomial, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ G.edges, ∑ v, if v ∈ e then x v * ∏ w ∈ e.erase v, x w else 0) =
        ∑ e ∈ G.edges, (r : ℝ) * ∏ w ∈ e, x w := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        (∑ v, if v ∈ e then x v * ∏ w ∈ e.erase v, x w else 0) =
            ∑ v ∈ e, x v * ∏ w ∈ e.erase v, x w := by
          rw [← Finset.sum_filter]
          simp
        _ = ∑ _v ∈ e, ∏ w ∈ e, x w :=
          Finset.sum_congr rfl (fun v hv => Finset.mul_prod_erase e x hv)
        _ = _ := by simp [G.uniform e he]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem low_link_mass_le (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) {Λ δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ Λ)
    (hnear : Λ - Density.lowDegreeTolerance r δ ≤ G.edgePolynomial x) :
    ∑ v ∈ Finset.univ.filter (fun v => G.linkPolynomial x v ≤ (r : ℝ) * Λ - δ), x v ≤ δ := by
  classical
  let S := Finset.univ.filter (fun v => G.linkPolynomial x v ≤ (r : ℝ) * Λ - δ)
  let η : ℝ := δ ^ 2 / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have htol : Density.lowDegreeTolerance r δ ≤ Density.linkTolerance r η := min_le_left _ _
  have hL (v : V) : G.linkPolynomial x v ≤ (r : ℝ) * Λ + η :=
    G.linkPolynomial_le_near_max x hx hη hbound (by linarith) v
  have hpoint (v : V) : x v * G.linkPolynomial x v ≤
      x v * ((r : ℝ) * Λ + η - if v ∈ S then δ + η else 0) := by
    apply mul_le_mul_of_nonneg_left _ (hx.1 v)
    by_cases hv : v ∈ S
    · have hl := (Finset.mem_filter.mp hv).2
      simpa only [if_pos hv] using (show G.linkPolynomial x v ≤
        (r : ℝ) * Λ + η - (δ + η) by linarith)
    · simpa only [if_neg hv, sub_zero] using hL v
  have hmass : (∑ v, if v ∈ S then x v * (δ + η) else 0) =
      (∑ v ∈ S, x v) * (δ + η) := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_mul]
  have havg : (r : ℝ) * G.edgePolynomial x ≤
      (r : ℝ) * Λ + η - (∑ v ∈ S, x v) * (δ + η) := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hpoint v)
    rw [G.sum_weight_mul_link] at h
    simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hx.2, one_mul] at h
    rwa [hmass] at h
  have hsmall : Density.lowDegreeTolerance r δ ≤ δ ^ 2 / (4 * ((r : ℝ) + 1)) :=
    min_le_right _ _
  have hden : 0 < 4 * ((r : ℝ) + 1) := by positivity
  have hs := (le_div_iff₀ hden).mp hsmall
  have htol0 := (Density.lowDegreeTolerance_pos r hδ).le
  have hrnear := mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg r)
  have hS0 : 0 ≤ ∑ v ∈ S, x v := Finset.sum_nonneg (fun v _ => hx.1 v)
  have hηS : 0 ≤ η * (∑ v ∈ S, x v) := mul_nonneg hη.le hS0
  change (∑ v ∈ S, x v) ≤ δ
  dsimp [η] at havg hηS
  nlinarith

noncomputable def lowDegreeSet (G : RGraph V r) (Λ δ : ℝ) : Finset V :=
  Finset.univ.filter (fun v => (G.degree v : ℝ) ≤
    ((r : ℝ) * Λ - δ) * (Fintype.card V : ℝ) ^ (r - 1))

theorem lowDegreeSet_card_le (G : RGraph V r) (hn : 0 < Fintype.card V)
    {Λ δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ y, ProbabilityWeights y → G.edgePolynomial y ≤ Λ)
    (hnear : (Λ - Density.lowDegreeTolerance r δ) * (Fintype.card V : ℝ) ^ r ≤
      (G.edges.card : ℝ)) :
    ((G.lowDegreeSet Λ δ).card : ℝ) ≤ δ * Fintype.card V := by
  classical
  let n : ℝ := Fintype.card V
  have hn0 : 0 < n := by
    dsimp [n]
    exact_mod_cast hn
  let x : V → ℝ := fun _ => n⁻¹
  have hx : ProbabilityWeights x := by
    refine ⟨fun _ => inv_nonneg.mpr hn0.le, ?_⟩
    simp [x, n, ne_of_gt hn0]
  have heq : G.lowDegreeSet Λ δ =
      Finset.univ.filter (fun v => G.linkPolynomial x v ≤ (r : ℝ) * Λ - δ) := by
    ext v
    simp only [lowDegreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [G.linkPolynomial_uniform, inv_pow, ← div_eq_mul_inv]
    exact (div_le_iff₀ (pow_pos hn0 _)).symm
  have hweight : Λ - Density.lowDegreeTolerance r δ ≤ G.edgePolynomial x := by
    rw [G.edgePolynomial_uniform, inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos hn0 _)).mpr hnear
  have h := G.low_link_mass_le x hx hδ hbound hweight
  rw [← heq] at h
  have h' : ((G.lowDegreeSet Λ δ).card : ℝ) / n ≤ δ := by
    simpa only [x, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using h
  exact (div_le_iff₀ hn0).mp h'

end RGraph
end TuranUniversality
