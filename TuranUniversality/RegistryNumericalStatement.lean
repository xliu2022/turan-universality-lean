module

public import TuranUniversality.Effective.UniformDecodeFamily
public import TuranUniversality.Density.FamilyExtremal
public import TuranUniversality.Hypergraph.Polynomial
public import TuranUniversality.Uniformity.Thresholds

@[expose] public section

/-! # Complete statement of Theorem 1.2, including effective fixed templates -/

open Filter Topology

namespace TuranUniversality.Registry

noncomputable section

/-- The uniformity lift uses one joint primitive-recursive family compiler
and one primitive-recursive template compiler. Both strengthen the requested
uniform computability. Optimality is stated explicitly for every real
probability weighting, with the uniform weighting attaining the bound. -/
def numericalStatement : Prop :=
  ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
    (∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧ τ = Weighted.rationalThreshold (m : ℚ)) ∧
    ∃ single : List Bool → Effective.GraphCode, Primrec single ∧
    ∃ families : ℕ × List Bool → List Effective.Uniform.Code, Primrec families ∧
    ∃ templates : ℕ → Effective.Uniform.Code, Primrec templates ∧
      (∀ w, Effective.Uniform.decodeFamily 3 (families (3, w)) =
        {Effective.decodeGraphCode (single w)}) ∧
      ∀ r : ℕ, 3 ≤ r →
        let τr := Uniformity.densityScale r * τ
        let K := Effective.Uniform.decode r (templates r)
        0 < τr ∧ τr < 1 ∧ 0 < (templates r).1 ∧
        (r.factorial : ℝ) * K.edgePolynomial (fun _ => ((templates r).1 : ℝ)⁻¹) = (τr : ℝ) ∧
        (∀ x, ProbabilityWeights x → (r.factorial : ℝ) * K.edgePolynomial x ≤ (τr : ℝ)) ∧
        ∀ w : List Bool,
          let F := Effective.Uniform.decodeFamily r (families (r, w))
          (∀ A ∈ F, 1 ≤ A.2.edges.card) ∧
          Tendsto (familyExtremalDensity F) atTop (𝓝 (familyTuranDensity F)) ∧
          familyTuranDensity F = (Uniformity.densityScale r : ℝ) *
            turanDensity (Effective.decodeGraph (single w)) ∧
          (familyTuranDensity F = (τr : ℝ) ↔ ¬ Computation.WordHalts w) ∧
          ((τr : ℝ) < familyTuranDensity F ↔ Computation.WordHalts w) ∧
          familyHomFree F K ∧
          ∀ sizes, familyFree F (K.blowup sizes)

end
end TuranUniversality.Registry
