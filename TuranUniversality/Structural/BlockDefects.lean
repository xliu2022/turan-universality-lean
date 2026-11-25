module

public import TuranUniversality.Structural.CompiledWeights
public import TuranUniversality.Structural.PentagonDefect

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A single block defect controls the whole compiled polynomial

The argument applies the same five-point defect to every support word before
summing the actual edges. Thus near-optimality controls individual root
weights, beyond the already established block-mass limits.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural

theorem product_le_factor_product {J : Type*} [Fintype J] [DecidableEq J]
    (a c : J → ℝ) (k : ℝ) (i : J) (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 ≤ c j)
    (hk : 0 ≤ k) (hbound : ∀ j, a j ≤ c j) (hi : a i ≤ k * c i) :
    (∏ j, a j) ≤ k * ∏ j, c j := by
  have hrest : (∏ j ∈ Finset.univ.erase i, a j) ≤ ∏ j ∈ Finset.univ.erase i, c j :=
    Finset.prod_le_prod₀ (fun j _ => ha j) (fun j _ => hbound j)
  have h := mul_le_mul hi hrest (Finset.prod_nonneg (fun j _ => ha j)) (mul_nonneg hk (hc i))
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  calc
    (∏ j, a j) ≤ (k * c i) * ∏ j ∈ Finset.univ.erase i, c j := h
    _ = k * ∏ j, c j := by
      rw [mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

namespace Pentagon

theorem polynomial_le_normalizedDefect_all (phase : Bool) {x : Fin 5 → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    (graph phase).edgePolynomial x ≤ (mass x ^ 3 / 25) * (1 - normalizedDefect x / 16) := by
  by_cases hm : mass x = 0
  · simpa [hm] using edgePolynomial_le phase hx
  · exact polynomial_le_normalizedDefect phase hx
      (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hx i)) (Ne.symm hm))

end Pentagon

namespace Support

theorem blockGraph_average {b : ℕ} (w : Cube.Word b) (x : Vertex b → ℝ) (i : Fin b) :
    (blockGraph w i).edgePolynomial (fun j => average x ⟨i, j⟩) = blockMass x i ^ 3 / 25 := by
  change (Pentagon.graph _).edgePolynomial (fun _ => blockMass x i / 5) = _
  rw [Pentagon.uniform_polynomial]
  ring

theorem wordGraph_le_defect {b : ℕ} (w : Cube.Word b) (x : Vertex b → ℝ)
    (hx : ∀ v, 0 ≤ x v) (i : Fin b) :
    (wordGraph w).edgePolynomial x ≤
      (1 - Pentagon.normalizedDefect (fun j => x ⟨i, j⟩) / 16) *
        (wordGraph w).edgePolynomial (average x) := by
  rw [wordGraph_polynomial, wordGraph_polynomial]
  apply product_le_factor_product
  · intro j
    exact (blockGraph w j).edgePolynomial_nonneg (fun a => hx ⟨j, a⟩)
  · intro j
    rw [blockGraph_average]
    apply div_nonneg
    · exact pow_nonneg (Finset.sum_nonneg (fun a _ => hx ⟨j, a⟩)) 3
    · norm_num
  · exact Pentagon.normalized_factor_nonneg (fun j => hx ⟨i, j⟩)
  · intro j
    rw [blockGraph_average]
    exact Pentagon.edgePolynomial_le _ (fun a => hx ⟨j, a⟩)
  · rw [blockGraph_average, mul_comm]
    exact Pentagon.polynomial_le_normalizedDefect_all _ (fun j => hx ⟨i, j⟩)

theorem poolGraph_le_defect {b : ℕ} (Ω : Finset (Cube.Word b)) (x : Vertex b → ℝ)
    (hx : ∀ v, 0 ≤ x v) (i : Fin b) :
    (poolGraph Ω).edgePolynomial x ≤
      (1 - Pentagon.normalizedDefect (fun j => x ⟨i, j⟩) / 16) *
        (poolGraph Ω).edgePolynomial (average x) := by
  rw [poolGraph_polynomial, poolGraph_polynomial, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  simpa only [← wordGraph_polynomial] using wordGraph_le_defect w x hx i

end Support

namespace Compiled

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

noncomputable def averageRoots (x : Vertex b t V → ℝ) : Vertex b t V → ℝ :=
  Sum.elim (suspensionWeight x) (Sum.elim (Support.average (rootWeight x)) (dataWeight x))

theorem averageRoots_nonneg (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    ∀ v, 0 ≤ averageRoots x v := by
  intro v
  rcases v with i | (⟨i, j⟩ | v)
  · exact hx _
  · change 0 ≤ blockMass x i / 5
    exact div_nonneg (blockMass_nonneg x hx i) (by norm_num)
  · exact hx _

theorem averageRoots_probability (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    ProbabilityWeights (averageRoots x) := by
  refine ⟨averageRoots_nonneg x hx.1, ?_⟩
  have hi (i : Fin b) : (∑ j : Fin 5, Support.average (rootWeight x) ⟨i, j⟩) =
      ∑ j : Fin 5, rootWeight x ⟨i, j⟩ := by
    simp only [Support.average, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    change 5 * (blockMass x i / 5) = blockMass x i
    ring
  have h := hx.2
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma] at h
  simp only [averageRoots, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_sigma, hi]
  exact h

theorem polynomial_le_averaged_defect (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) (i : Fin b) :
    (graph t Ω R).edgePolynomial x ≤
      (1 - Pentagon.normalizedDefect (fun j => rootWeight x ⟨i, j⟩) / 16) *
        (graph t Ω R).edgePolynomial (averageRoots x) := by
  let c := 1 - Pentagon.normalizedDefect (fun j => rootWeight x ⟨i, j⟩) / 16
  rw [polynomial, polynomial]
  change (∏ j, suspensionWeight x j) * ∑ X ∈ R.recorded.edges,
    (Support.poolGraph (Ω (R.label X))).edgePolynomial (rootWeight x) * ∏ v ∈ X, dataWeight x v ≤
    c * ((∏ j, suspensionWeight x j) * ∑ X ∈ R.recorded.edges,
      (Support.poolGraph (Ω (R.label X))).edgePolynomial (Support.average (rootWeight x)) *
        ∏ v ∈ X, dataWeight x v)
  calc
    _ ≤ (∏ j, suspensionWeight x j) * ∑ X ∈ R.recorded.edges,
        (c * (Support.poolGraph (Ω (R.label X))).edgePolynomial
          (Support.average (rootWeight x))) * ∏ v ∈ X, dataWeight x v := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun j _ => hx _))
      apply Finset.sum_le_sum
      intro X _
      exact mul_le_mul_of_nonneg_right
        (Support.poolGraph_le_defect _ (rootWeight x) (fun v => hx _) i)
        (Finset.prod_nonneg (fun v _ => hx _))
    _ = _ := by
      simp only [mul_assoc, ← Finset.mul_sum]
      ring

theorem polynomial_le_defect_upper (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (hlocal : R.LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ l, ((Ω l).card : ℝ) = Label.payoff p q l)
    (x : Vertex b t V → ℝ) (hx : ProbabilityWeights x) (i : Fin b) :
    (graph t Ω R).edgePolynomial x ≤
      (1 - Pentagon.normalizedDefect (fun j => rootWeight x ⟨i, j⟩) / 16) *
        (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)) := by
  exact (polynomial_le_averaged_defect Ω R x hx.1 i).trans
    (mul_le_mul_of_nonneg_left
      (polynomial_upper F hedges Ω R hlocal p q hp hpq hq hz hΩ (averageRoots x)
        (averageRoots_probability x hx))
      (Pentagon.normalized_factor_nonneg (fun j => hx.1 _)))

end Compiled
end TuranUniversality.Structural
