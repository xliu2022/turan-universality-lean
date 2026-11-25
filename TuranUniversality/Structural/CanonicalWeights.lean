module

public import TuranUniversality.Structural.Canonical
public import TuranUniversality.Structural.CompiledOptimum
public import TuranUniversality.Density.WeightedHomPushforward
public import TuranUniversality.Uniformity.GeneralTransfer

@[expose] public section

/-! # Actual root-class completion, compression, and the admissible supremum -/

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem Canonical.polynomial_upper (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) (hG : Canonical (homomorphicClosure F) Ω G)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    G.edgePolynomial x ≤ OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  obtain ⟨ρ, R, hR, hhom⟩ := hG
  exact (G.edgePolynomial_le_pushforward (Compiled.graph t Ω R) (Rooted.place ρ) hhom x hx.1).trans
    (Compiled.polynomial_upper F hedges Ω R hR p q hp hpq hq hz hΩ
      (pushforwardWeight (Rooted.place ρ) x) (pushforwardWeight_probability _ _ hx))

/-- The completion is on the original vertex set. Its quotient weights sum
within root classes and retain individual data vertices; all test coordinates
agree exactly, including tests with isolated vertices. -/
theorem Canonical.completion (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) (hG : Canonical B Ω G) (x : V → ℝ) :
    ∃ (ρ : V → Option (Rooted.Roots b t)) (R : RecordSystem V)
      (H : RGraph V (t + (3 * b + 4))),
      R.LocallyLegal B ∧ G.edges ⊆ H.edges ∧
      H.edgePolynomial x = (Compiled.graph t Ω R).edgePolynomial (pushforwardWeight (Rooted.place ρ) x) ∧
      ∀ (n : ℕ) (A : RGraph (Fin n) (t + (3 * b + 4))),
        A.weightedHomDensity H x = A.weightedHomDensity (Compiled.graph t Ω R)
          (pushforwardWeight (Rooted.place ρ) x) := by
  obtain ⟨ρ, R, hR, hh⟩ := hG
  let D := Compiled.graph t Ω R
  refine ⟨ρ, R, D.inverseImage (Rooted.place ρ), hR, ?_,
    D.edgePolynomial_inverseImage (Rooted.place ρ) x, ?_⟩
  · intro e he
    exact (D.mem_inverseImage _ e).mpr ⟨G.uniform e he, hh e he⟩
  · intro n A
    exact A.weightedHomDensity_inverseImage D (Rooted.place ρ) x

theorem admissible_classLagrangian (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    PairTransfer.classLagrangian (Rooted.basis (homomorphicClosure F) Ω t) =
      OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  apply le_antisymm
  · apply PairTransfer.classLagrangian_le_of_bound _ _
      (mul_nonneg (OuterWeights.chi_pos b t).le (SwitchScalar.phaseScore_pos p q _ hq hz).le)
    intro n G x hfree hx
    have had := (Rooted.basis_spec (homomorphicClosure F) Ω hdis t ⟨n, G⟩).mpr hfree
    exact (Canonical.of_admits (homomorphicClosure F) Ω hdis had).polynomial_upper
      F hedges Ω G p q hp hpq hq hz hΩ x hx
  · apply (Compiled.weightedValues_isLUB F hedges Ω p q hp hpq hq hz hΩ).2
    rintro z ⟨V, d, f, R, x, hR, hx, rfl⟩
    letI : DecidableEq V := d
    letI : Fintype V := f
    exact PairTransfer.polynomial_le_classLagrangian _ (Compiled.graph t Ω R)
      ((Rooted.basis_spec_finite (homomorphicClosure F) Ω hdis _).mp
        (Compiled.admits (homomorphicClosure F) Ω R hR)) x hx

end TuranUniversality.Structural
