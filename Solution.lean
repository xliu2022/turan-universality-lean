module

public import TuranUniversality.Reduction.Universality
public import TuranUniversality.Reduction.NumericalUniversality
public import TuranUniversality.Structural.Main

/-!
# Completed proofs of Theorems 1.1, 1.2 and 1.3

Formalization author and maintainer: Xizhi Liu.
The independent Challenge is not imported. Each theorem below reuses the
original completed proof and keeps its original advertised statement.
-/

@[expose] public section

open Filter Topology

namespace TuranUniversality.Registry

/-- The complete, unconditional statement corresponding to V4 Theorem 1.1.
Its mathematical definitions are independently restated in Challenge.lean;
this proof does not import the Challenge or its statement placeholder. -/
theorem main_theorem :
    ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
      (∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧ τ = Weighted.rationalThreshold (m : ℚ)) ∧
      ∃ compiler : List Bool → Effective.GraphCode, Primrec compiler ∧
        ∀ w : List Bool,
          1 ≤ (Effective.decodeGraph (compiler w)).edges.card ∧
          Tendsto (extremalDensity (Effective.decodeGraph (compiler w))) atTop
            (𝓝 (turanDensity (Effective.decodeGraph (compiler w)))) ∧
          (turanDensity (Effective.decodeGraph (compiler w)) = (τ : ℝ) ↔
            ¬ Computation.WordHalts w) ∧
          ((τ : ℝ) < turanDensity (Effective.decodeGraph (compiler w)) ↔
            Computation.WordHalts w) := singleton_universality

/-- Complete unconditional Theorem 1.2. The independent challenge contains
its own mathematical definitions and is not imported by this solution. -/
theorem numerical_main_theorem :
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
          ∀ sizes, familyFree F (K.blowup sizes) := numerical_universality

/-- Theorem 1.3, with the original complete structural statement. -/
theorem structural_main_theorem : structuralStatement :=
  TuranUniversality.Structural.registry_main

end TuranUniversality.Registry
