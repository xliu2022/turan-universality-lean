module

public import TuranUniversality.Structural.ActualData
public import TuranUniversality.Structural.NeutralRoleMass

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual ordinary inner graphs in the positive-gap approximation

The retained active vertices are genuine data vertices of the original
graph. Their weights are uniform, so the optimized inner cubic ratio is
the ordinary edge hom-density of a real finite hom-free three-graph.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Density

theorem order_tendsto_of_positive_ratio {I : Type*} (l : Filter I) (a n : I → ℕ)
    (hn : Tendsto n l atTop) (z : ℝ) (hz : 0 < z)
    (h : Tendsto (fun i => (a i : ℝ) / n i) l (𝓝 z)) : Tendsto a l atTop := by
  apply tendsto_atTop.2
  intro K
  have hz2 : 0 < z / 2 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((K : ℝ) / (z / 2))
  have hsmall := h.eventually (lt_mem_nhds (show z / 2 < z by linarith))
  filter_upwards [hsmall, hn.eventually (eventually_ge_atTop N),
    hn.eventually (eventually_ge_atTop 1)] with i hi hin hip
  have hni : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
  have hmul : z / 2 * (n i : ℝ) < a i := (lt_div_iff₀ hni).mp hi
  have hKN : (K : ℝ) < (N : ℝ) * (z / 2) := (div_lt_iff₀ hz2).mp hN
  have hNn : (N : ℝ) ≤ n i := by exact_mod_cast hin
  have hK : (K : ℝ) ≤ a i := by nlinarith
  exact_mod_cast hK

universe u v

theorem legal_data_approximation_actual
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
      (∀ i, (O i).active ⊆ Rooted.ordinaryData (ρ i)) ∧
      (∀ i, familyHomFree F (O i).activeProjection) ∧
      Tendsto (fun i => (G i).normalizedEditDistance
        ((Compiled.graph t (CodePools.pool p q hpq) (O i).records).inverseImage
          (Rooted.place (ρ i)))) l (𝓝 0) ∧
      (∀ a, Tendsto (fun i => (PartitionRounding.fiberSize
        (NeutralRoles.roleOfRooting (ρ i)) a : ℝ) / Fintype.card (V i)) l
        (𝓝 (NeutralRoles.optimalRoleWeight (CodePools.blockCount q) t a))) ∧
      Tendsto (fun i => ((O i).active.card : ℝ) / Fintype.card (V i)) l
        (𝓝 (Compiled.activeLimit (CodePools.blockCount q) t
          (familyTuranDensity F - (p : ℝ) / q))) ∧
      ((p : ℝ) / q < familyTuranDensity F →
        Tendsto (fun i => (O i).active.card) l atTop ∧
        Tendsto (fun i => (RGraph.oneEdge 3).homDensity (O i).activeProjection) l
          (𝓝 (familyTuranDensity F))) := by
  classical
  obtain ⟨ρ, O, hy, hedit, hrole, hactive, _, hinner⟩ := legal_edit_approximation_actual
    F hedges p q hpq hq t hz G hG hn l hsize hlim
  let y i := pushforwardWeight (Rooted.place (ρ i))
    (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹)
  let Q i := (O i).restrict (Rooted.ordinaryData (ρ i))
  have hQ i : (Q i).active ⊆ Rooted.ordinaryData (ρ i) := Finset.inter_subset_right
  have hzero i v (hv : v ∉ Rooted.ordinaryData (ρ i)) : Compiled.dataWeight (y i) v = 0 := by
    rw [Rooted.dataWeight_pushforward]
    have hn : ρ i v ≠ none := by simpa using hv
    simp only [hn, ite_false]
  have hc i v (hv : v ∈ (Q i).active) :
      Compiled.dataWeight (y i) v = (Fintype.card (V i) : ℝ)⁻¹ := by
    rw [Rooted.dataWeight_pushforward, (Rooted.mem_ordinaryData _ _).mp (hQ i hv)]
    rfl
  have hmass i : ((Q i).active.card : ℝ) / Fintype.card (V i) =
      (O i).activeMass (Compiled.dataWeight (y i)) := by
    rw [← (O i).restrict_activeMass _ _ (hzero i)]
    change _ = ∑ v ∈ (Q i).active, Compiled.dataWeight (y i) v
    rw [Finset.sum_congr rfl (fun v hv => hc i v hv)]
    simp [div_eq_mul_inv]
  have hA : Tendsto (fun i => ((Q i).active.card : ℝ) / Fintype.card (V i)) l
      (𝓝 (Compiled.activeLimit (CodePools.blockCount q) t
        (familyTuranDensity F - (p : ℝ) / q))) := by
    simpa only [hmass] using hactive
  refine ⟨ρ, Q, hQ, ?_, ?_, ?_, hA, ?_⟩
  · intro i
    exact (familyFree_homomorphicClosure_iff F _).mp (Q i).activeProjection_free
  · simpa only [Q, LegalObject.restrict_data_realization] using hedit
  · intro a
    simpa only [NeutralRoles.roleWeight_uniform] using (tendsto_pi_nhds.mp hrole) a
  · intro hgap
    have ha : 0 < Compiled.activeLimit (CodePools.blockCount q) t
        (familyTuranDensity F - (p : ℝ) / q) := by
      unfold Compiled.activeLimit
      have hd := sub_pos.mpr hgap
      have hr : (0 : ℝ) < OuterWeights.arity (CodePools.blockCount q) t :=
        Nat.cast_pos.mpr (OuterWeights.arity_pos _ _)
      positivity
    refine ⟨order_tendsto_of_positive_ratio l _ _ hsize _ ha hA, ?_⟩
    have hTlim : Tendsto (fun i => Compiled.dataMass (y i)) l
        (𝓝 (4 / (OuterWeights.arity (CodePools.blockCount q) t : ℝ))) :=
      (tendsto_pi_nhds.mp hrole) (.inr ())
    have hT : ∀ᶠ i in l, 0 < Compiled.dataMass (y i) :=
      hTlim.eventually (lt_mem_nhds (by
        exact div_pos (by norm_num) (Nat.cast_pos.mpr (OuterWeights.arity_pos _ _))))
    apply (hinner hgap).congr'
    filter_upwards [hT] with i hi
    have hc0 : (Fintype.card (V i) : ℝ)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Nat.cast_pos.mpr (hn i)))
    rw [(Q i).active_constant_innerDensity _ _ hc0 (hc i),
      (O i).restrict_innerDensity _ _ (hzero i),
      PhaseRoles.innerDensity_normalizedData (O i) (y i) hi]

end TuranUniversality.Structural.Ordinary
