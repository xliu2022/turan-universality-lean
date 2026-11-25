module

public import TuranUniversality.Structural.CompletedOrdinaryApproximation
public import TuranUniversality.Structural.NeutralConvergence
public import TuranUniversality.Density.EditPullback

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Ordinary near-extremal graphs are close to complete legal models

The quotient weights are the actual fiber sums of uniform weights on the
original vertex set. Repair is performed on those weights, and its
disagreement probability is transported back to an ordinary edge edit.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Density

universe u v

theorem legal_edit_approximation_actual
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
    ∃ (ρ : ∀ i, V i → Option (Rooted.Roots (CodePools.blockCount q) t))
      (O : ∀ i, LegalObject (homomorphicClosure F) (V i)),
      let Ω := CodePools.pool p q hpq
      let y i := pushforwardWeight (Rooted.place (ρ i))
        (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹)
      let K i := (Compiled.graph t Ω (O i).records).inverseImage (Rooted.place (ρ i))
      (∀ i, ProbabilityWeights (y i)) ∧
      Tendsto (fun i => (G i).normalizedEditDistance (K i)) l (𝓝 0) ∧
      Tendsto (fun i => NeutralRoles.roleWeight (y i)) l
        (𝓝 (NeutralRoles.optimalRoleWeight (CodePools.blockCount q) t)) ∧
      Tendsto (fun i => (O i).activeMass (Compiled.dataWeight (y i))) l
        (𝓝 (Compiled.activeLimit (CodePools.blockCount q) t
          (familyTuranDensity F - (p : ℝ) / q))) ∧
      Tendsto (fun i => (O i).neutralMass (Compiled.dataWeight (y i))) l
        (𝓝 (Compiled.neutralLimit (CodePools.blockCount q) t
          (familyTuranDensity F - (p : ℝ) / q))) ∧
      ((p : ℝ) / q < familyTuranDensity F →
        Tendsto (fun i => (O i).innerDensity (Compiled.normalizedData (y i))) l
          (𝓝 (familyTuranDensity F))) := by
  classical
  let Ω := CodePools.pool p q hpq
  obtain ⟨ρ, R, hR, hy, hGK, hmodel, _⟩ := completed_edit_approximation_actual
    F hedges p q hpq hq t hz G hG hn l hsize hlim
  let y i := pushforwardWeight (Rooted.place (ρ i))
    (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹)
  obtain ⟨O, _, hd, _, _, hactive, hneutral, hinner⟩ := Compiled.exists_decoded_models
    V F hedges Ω R hR p q (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq)
    (Nat.cast_pos.mpr hq) hz (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  have hT := Compiled.eventually_positive_dataMass V F hedges Ω R hR p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  have hm := Compiled.mismatch_tendsto l Ω R O y hy hT hd
  have hKO : Tendsto (fun i =>
      ((Compiled.graph t Ω (R i)).inverseImage (Rooted.place (ρ i))).normalizedEditDistance
        ((Compiled.graph t Ω (O i).records).inverseImage (Rooted.place (ρ i)))) l (𝓝 0) := by
    simpa only [RGraph.normalizedEditDistance_inverseImage] using hm
  have hroot := Compiled.near_optimal_root_limits V F hedges Ω R hR p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  refine ⟨ρ, O, hy,
    RGraph.normalizedEditDistance_tendsto_zero_trans G _ _ l hGK hKO,
    ?_, hactive, hneutral, hinner⟩
  apply tendsto_pi_nhds.mpr
  rintro ((j | ⟨i, j⟩) | a)
  · exact hroot.1 j
  · exact hroot.2.1 i j
  · exact hroot.2.2

end TuranUniversality.Structural.Ordinary
