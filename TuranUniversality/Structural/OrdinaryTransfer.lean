module

public import TuranUniversality.Structural.OrdinaryProfiles
public import TuranUniversality.Structural.OrdinaryEditApproximation
public import TuranUniversality.Structural.VertexExtendability

@[expose] public section

/-! # Unconditional ordinary transfer for the seven concrete code pools

Every structural hypothesis in the finite stability theorem is now
discharged. These statements use the actual finite forbidden family and
the ordinary homomorphism-density compactification, as well as an actual
same-carrier edge-edit approximation at the finite level.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

universe u v

theorem extremal_eq_canonical_actual
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F) :
    SetFamily.extremalProfiles (forbidden F (CodePools.pool p q hpq) t) =
      CanonicalProfiles.extremal F (CodePools.pool p q hpq) t p q :=
  extremal_eq_canonical F hedges (CodePools.pool p q hpq)
    (fun _ _ h => CodePools.pools_disjoint p q hpq h) t p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) (vertex_extendable F hedges p q hpq hq t hz)

theorem positive_profile_classification_actual
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q < familyTuranDensity F) :
    SetFamily.extremalProfiles (forbidden F (CodePools.pool p q hpq) t) =
      (PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) false
        p q (familyTuranDensity F) '' SetFamily.extremalProfiles F) ∪
      (PhaseRoles.extremalPhaseMap (t := t) (CodePools.pool p q hpq) true
        p q (familyTuranDensity F) '' SetFamily.extremalProfiles F) := by
  rw [extremal_eq_canonical_actual F hedges p q hpq hq t hz.le]
  exact CanonicalProfiles.positive_classification F hedges (CodePools.pool p q hpq) p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq)

theorem zero_profile_classification_actual
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : familyTuranDensity F = (p : ℝ) / q) :
    SetFamily.extremalProfiles (forbidden F (CodePools.pool p q hpq) t) =
      {NeutralRoles.neutralProfile (CodePools.pool p q hpq) t} := by
  rw [extremal_eq_canonical_actual F hedges p q hpq hq t hz.ge]
  exact CanonicalProfiles.zero_classification F hedges (CodePools.pool p q hpq) p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq)

theorem near_extremal_edit_approximation_actual
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * CodePools.blockCount q + 4)))
    (hG : ∀ i, familyFree (forbidden F (CodePools.pool p q hpq) t) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l
      (𝓝 (optimum F (CodePools.blockCount q) t p q))) :
    ∃ H : ∀ i, RGraph (V i) (t + (3 * CodePools.blockCount q + 4)),
      (∀ i, (H i).edges ⊆ (G i).edges) ∧
      Tendsto (fun i => (((G i).edgeSymmDifference (H i)).edges.card : ℝ) /
        (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l (𝓝 0) ∧
      Tendsto (fun i => ((H i).edges.card : ℝ) /
        (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l
        (𝓝 (optimum F (CodePools.blockCount q) t p q)) ∧
      ∀ᶠ i in l, Canonical (homomorphicClosure F) (CodePools.pool p q hpq) (H i) :=
  near_extremal_edit_approximation F hedges (CodePools.pool p q hpq)
    (fun _ _ h => CodePools.pools_disjoint p q hpq h) t p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) (vertex_extendable F hedges p q hpq hq t hz)
    G hG hn l hsize hlim

end TuranUniversality.Structural.Ordinary
