module

public import TuranUniversality.Effective.GraphEncoding
public import TuranUniversality.Effective.UniformDecodeFamily
public import TuranUniversality.Computation.Program
public import TuranUniversality.Structural.ExtremalProfiles
public import TuranUniversality.Density.FiniteProfiles
public import TuranUniversality.Hypergraph.PartitionRounding

@[expose] public section

/-! # Independent public statement for the structural phase transition

All limits below are ordinary hom-density profiles of finite simple graphs.
Finite profiles use allowed multisets of finitely many numbered roles. Their
rounding counts are fixed before the binary input, have the exact total, and
each equal either the floor or ceiling of the prescribed role mass.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Registry.Structural

/-- A fixed balanced rounding for the role proportions, valid at every order. -/
def BalancedCounts {k : ℕ} (z : Fin k → ℝ) (d : ℕ → Fin k → ℕ) : Prop :=
  ∀ n, (∑ a, d n a) = n ∧
    ∀ a, d n a = ⌊(n : ℝ) * z a⌋₊ ∨ d n a = ⌈(n : ℝ) * z a⌉₊

/-- Every ordinary near-extremal free sequence is close, on its original
vertex set, to the same finite multiset pattern with the fixed class sizes. -/
def StableWithPattern {r k : ℕ} (F : Finset (FiniteGraph r))
    (P : FiniteRolePattern (Fin k) r) (d : ℕ → Fin k → ℕ) : Prop :=
  ∀ (n : ℕ → ℕ) (G : ∀ i, RGraph (Fin (n i)) r),
    (∀ i, 0 < n i) → Tendsto n atTop atTop →
    (∀ i, familyFree F (G i)) →
    Tendsto (fun i => (RGraph.oneEdge r).homDensity (G i)) atTop
      (𝓝 (familyTuranDensity F)) →
    ∃ θ : ∀ i, Fin (n i) → Fin k,
      (∀ i a, PartitionRounding.fiberSize (θ i) a = d (n i) a) ∧
      Tendsto (fun i => (G i).normalizedEditDistance (P.graph (θ i))) atTop (𝓝 0)

/-- The separator uses two fixed ordinary finite test graphs. -/
def Separator {r : ℕ} (T₁ T₂ : FiniteGraph r) (W : SetFamily.Profile r) : ℝ :=
  W T₁ - W T₂

/-- Both compact phases retain the entire inner extremal space. -/
def TwoPhases {r : ℕ} (F : Finset (FiniteGraph r)) (P : FiniteGraph 3)
    (T₁ T₂ : FiniteGraph r) : Prop :=
  ∃ (c : ℝ), 0 < c ∧ ∃ phase : Bool → Set (SetFamily.Profile r),
    SetFamily.extremalProfiles F = phase false ∪ phase true ∧
    Disjoint (phase false) (phase true) ∧
    (∀ s, IsCompact (phase s) ∧ (phase s).Nonempty ∧
      Nonempty (SetFamily.extremalProfiles {P} ≃ₜ phase s) ∧
      ∀ W ∈ phase s, Separator T₁ T₂ W = if s then -c else c) ∧
    Nonempty ((Bool × SetFamily.extremalProfiles {P}) ≃ₜ SetFamily.extremalProfiles F)

end Structural

/-- V4 Theorem 1.3, including the actual edge-edit conclusion. The fixed
rank threshold, numbered profile, rounding counts and separator graphs are
chosen independently of the binary input. The inner singleton compiler also
retains the ordinary density dichotomy of Theorem 1.1. -/
def structuralStatement : Prop :=
  ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
    ∃ inner : Computation.BinaryWord → Effective.GraphCode,
      Primrec inner ∧
      (∀ β, (Effective.decodeGraph (inner β)).edges.Nonempty ∧
        (turanDensity (Effective.decodeGraph (inner β)) = (τ : ℝ) ↔
          ¬ Computation.WordHalts β) ∧
        ((τ : ℝ) < turanDensity (Effective.decodeGraph (inner β)) ↔
          Computation.WordHalts β)) ∧
      ∃ R : ℕ, 4 ≤ R ∧
        ∃ compiler : ℕ → Computation.BinaryWord → List Effective.Uniform.Code,
          Primrec₂ compiler ∧
          ∀ r, R ≤ r →
            ∃ (k : ℕ) (P : FiniteRolePattern (Fin k) r) (z : Fin k → ℝ)
              (d : ℕ → Fin k → ℕ) (T₁ T₂ : FiniteGraph r),
              0 < k ∧ ProbabilityWeights z ∧ Structural.BalancedCounts z d ∧
              (∀ β,
                let F := Effective.Uniform.decodeFamily r (compiler r β)
                (¬ Computation.WordHalts β →
                  SetFamily.extremalProfiles F = {P.profile z} ∧
                    Structural.Separator T₁ T₂ (P.profile z) = 0 ∧
                    Structural.StableWithPattern F P d) ∧
                (Computation.WordHalts β →
                  Structural.TwoPhases F (Effective.decodeGraphCode (inner β)) T₁ T₂))

end TuranUniversality.Registry
