module

public import TuranUniversality.Structural.LegalOrdinaryApproximation
public import TuranUniversality.Structural.NeutralRoleMass

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Ordinary zero-gap stability for the fixed finite multiset profile

The conclusion concerns actual graphs on the original vertex sets. Their
roles have the prescribed limiting proportions, and changing `o(n^r)`
edges makes each graph exactly a realization of one fixed finite pattern.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Density

universe u v

theorem zero_finite_profile_approximation
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : familyTuranDensity F = (p : ℝ) / q)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * CodePools.blockCount q + 4)))
    (hG : ∀ i, familyFree (forbidden F (CodePools.pool p q hpq) t) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l
      (𝓝 (optimum F (CodePools.blockCount q) t p q))) :
    ∃ θ : ∀ i, V i → NeutralRoles.Role (CodePools.blockCount q) t,
      (∀ a, Tendsto (fun i => (PartitionRounding.fiberSize (θ i) a : ℝ) /
        Fintype.card (V i)) l
        (𝓝 (NeutralRoles.optimalRoleWeight (CodePools.blockCount q) t a))) ∧
      Tendsto (fun i => (G i).normalizedEditDistance
        ((NeutralRoles.pattern (CodePools.pool p q hpq)).graph (θ i))) l (𝓝 0) := by
  classical
  let Ω := CodePools.pool p q hpq
  obtain ⟨ρ, R, hR, hy, hGK, hmodel, _⟩ := completed_edit_approximation_actual
    F hedges p q hpq hq t hz.ge G hG hn l hsize hlim
  let y i := pushforwardWeight (Rooted.place (ρ i))
    (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹)
  obtain ⟨O, _, hd, _, ha, _, _, _⟩ := Compiled.exists_decoded_models
    V F hedges Ω R hR p q (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq)
    (Nat.cast_pos.mpr hq) hz.ge (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  have hT := Compiled.eventually_positive_dataMass V F hedges Ω R hR p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz.ge
    (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  have hs := Compiled.normalized_squares_tendsto V F hedges Ω R hR p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz.ge
    (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  have hroot := Compiled.near_optimal_root_limits V F hedges Ω R hR p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz.ge
    (CodePools.pool_card_cast p q hpq hq) y hy hmodel
  have hprob : ∀ᶠ i in l, ProbabilityWeights (Compiled.normalizedData (y i)) :=
    hT.mono (fun i hi => Compiled.normalizedData_probability (y i) (hy i).1 hi)
  have ha0 : Tendsto (fun i => (O i).activeMass (Compiled.normalizedData (y i))) l (𝓝 0) := by
    simpa only [hz, sub_self, SwitchScalar.optimalMass, mul_zero, zero_div] using ha
  let N i := (NeutralRoles.object (homomorphicClosure F)
    (homomorphicClosure_has_edges F hedges) : LegalObject (homomorphicClosure F) (V i))
  have hd0 := NeutralRoles.object_disagreement_tendsto
    (homomorphicClosure_has_edges F hedges) O (fun i => Compiled.normalizedData (y i))
    l hprob hs ha0
  have hm1 := Compiled.mismatch_tendsto l Ω R O y hy hT hd
  have hm2 := Compiled.mismatch_tendsto l Ω (fun i => (O i).records) N y hy hT hd0
  have h1 : Tendsto (fun i =>
      ((Compiled.graph t Ω (R i)).inverseImage (Rooted.place (ρ i))).normalizedEditDistance
        ((Compiled.graph t Ω (O i).records).inverseImage (Rooted.place (ρ i)))) l (𝓝 0) := by
    simpa only [RGraph.normalizedEditDistance_inverseImage] using hm1
  have h2 : Tendsto (fun i =>
      ((Compiled.graph t Ω (O i).records).inverseImage (Rooted.place (ρ i))).normalizedEditDistance
        ((Compiled.graph t Ω (N i).records).inverseImage (Rooted.place (ρ i)))) l (𝓝 0) := by
    simpa only [RGraph.normalizedEditDistance_inverseImage] using hm2
  have hKN := RGraph.normalizedEditDistance_tendsto_zero_trans _ _ _ l h1 h2
  have hGN := RGraph.normalizedEditDistance_tendsto_zero_trans G _ _ l hGK hKN
  have heq i : Compiled.graph t Ω (N i).records = NeutralRoles.compiledNeutral Ω (V i) := by
    rfl
  refine ⟨fun i => NeutralRoles.roleOfRooting (ρ i), ?_, ?_⟩
  · intro a
    have he i := NeutralRoles.roleWeight_uniform (ρ i) a
    simp_rw [← he]
    rcases a with (j | ⟨i, j⟩) | a
    · exact hroot.1 j
    · exact hroot.2.1 i j
    · exact hroot.2.2
  · simpa only [← NeutralRoles.graph_eq_pattern, NeutralRoles.graph_roleOfRooting,
      heq, Ω] using hGN

end TuranUniversality.Structural.Ordinary
