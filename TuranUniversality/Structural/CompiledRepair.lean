module

public import TuranUniversality.Structural.CompiledConvergence
public import TuranUniversality.Structural.RecordStability
public import TuranUniversality.Structural.SwitchEventual

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual decoded models and their limiting active and neutral masses

The repaired legal objects use the original data carriers and unchanged
weights. Their score, active proportion and positive-gap inner density are
derived from finite repair and the already proved global defect inequality.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural

namespace LegalObject

def neutralMass {V : Type*} [DecidableEq V] [Fintype V]
    {B : Finset (FiniteGraph 3)} (O : LegalObject B V) (x : V → ℝ) : ℝ :=
  ∑ v ∈ Finset.univ \ O.active, x v

theorem neutralMass_eq {V : Type*} [DecidableEq V] [Fintype V]
    {B : Finset (FiniteGraph 3)} (O : LegalObject B V) (x : V → ℝ) :
    O.neutralMass x = (∑ v, x v) - O.activeMass x :=
  Finset.sum_sdiff_eq_sub (Finset.subset_univ O.active)

end LegalObject

namespace Compiled

noncomputable def activeLimit (b t : ℕ) (δ : ℝ) : ℝ :=
  3 * δ / ((OuterWeights.arity b t : ℝ) * (1 + δ))

noncomputable def neutralLimit (b t : ℕ) (δ : ℝ) : ℝ :=
  (4 + δ) / ((OuterWeights.arity b t : ℝ) * (1 + δ))

theorem activeLimit_formula (b t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (4 / (OuterWeights.arity b t : ℝ)) * SwitchScalar.optimalMass δ = activeLimit b t δ := by
  have hr : (OuterWeights.arity b t : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  have hd : 1 + δ ≠ 0 := by linarith
  unfold SwitchScalar.optimalMass activeLimit
  field_simp [hr, hd]
  <;> ring

theorem neutralLimit_formula (b t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    4 / (OuterWeights.arity b t : ℝ) - activeLimit b t δ = neutralLimit b t δ := by
  have hr : (OuterWeights.arity b t : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  have hd : 1 + δ ≠ 0 := by linarith
  unfold activeLimit neutralLimit
  field_simp [hr, hd]
  <;> ring

theorem exists_decoded_models {I : Type*} {l : Filter I} {b t : ℕ}
    (V : I → Type*) [∀ n, DecidableEq (V n)] [∀ n, Fintype (V n)]
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (R : ∀ n, RecordSystem (V n))
    (hlocal : ∀ n, (R n).LocallyLegal (homomorphicClosure F))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (x : ∀ n, Vertex b t (V n) → ℝ) (hx : ∀ n, ProbabilityWeights (x n))
    (hlim : Tendsto (fun n => (graph t Ω (R n)).edgePolynomial (x n)) l
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    ∃ O : ∀ n, LegalObject (homomorphicClosure F) (V n),
      (∀ n, 0 < dataMass (x n) →
        sampleProbability (normalizedData (x n)) ((R n).Disagreement (O n)) ≤
          5 * (R n).erasure (normalizedData (x n))) ∧
      Tendsto (fun n => sampleProbability (normalizedData (x n)) ((R n).Disagreement (O n)))
        l (𝓝 0) ∧
      Tendsto (fun n => (O n).score p q (normalizedData (x n))) l
        (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F))) ∧
      Tendsto (fun n => (O n).activeMass (normalizedData (x n))) l
        (𝓝 (SwitchScalar.optimalMass (familyTuranDensity F - p / q))) ∧
      Tendsto (fun n => (O n).activeMass (dataWeight (x n))) l
        (𝓝 (activeLimit b t (familyTuranDensity F - p / q))) ∧
      Tendsto (fun n => (O n).neutralMass (dataWeight (x n))) l
        (𝓝 (neutralLimit b t (familyTuranDensity F - p / q))) ∧
      (p / q < familyTuranDensity F →
        Tendsto (fun n => (O n).innerDensity (normalizedData (x n))) l (𝓝 (familyTuranDensity F))) := by
  classical
  have hb := homomorphicClosure_has_edges F hedges
  have hex (n : I) : ∃ O : LegalObject (homomorphicClosure F) (V n),
      0 < dataMass (x n) →
        sampleProbability (normalizedData (x n)) ((R n).Disagreement O) ≤
          5 * (R n).erasure (normalizedData (x n)) := by
    by_cases hT : 0 < dataMass (x n)
    · obtain ⟨S, O, _, _, _, hd⟩ := RecordSystem.repair (hlocal n) hb
        (normalizedData (x n)) (normalizedData_probability (x n) (hx n).1 hT)
      exact ⟨O, fun _ => hd⟩
    · exact ⟨LegalObject.empty _ hb ∅, fun h => (hT h).elim⟩
  choose O hO using hex
  have hTevent := eventually_positive_dataMass V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim
  have hprob : ∀ᶠ n in l, ProbabilityWeights (normalizedData (x n)) :=
    hTevent.mono (fun n hn => normalizedData_probability (x n) (hx n).1 hn)
  have he := (near_optimal_factor_erasure V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).2
  have hs := near_optimal_score V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim
  have hd : Tendsto (fun n => sampleProbability (normalizedData (x n))
      ((R n).Disagreement (O n))) l (𝓝 0) := by
    refine squeeze_zero' (g := fun n => 5 * (R n).erasure (normalizedData (x n))) ?_ ?_ ?_
    · filter_upwards [hprob] with n hn
      exact sampleProbability_nonneg _ hn.1 _
    · filter_upwards [hTevent] with n hn
      exact hO n hn
    · simpa using he.const_mul 5
  have habs : Tendsto (fun n => |(O n).score p q (normalizedData (x n)) -
      (R n).score p q (normalizedData (x n))|) l (𝓝 0) := by
    refine squeeze_zero' (g := fun n => (805 * q / 24) * (R n).erasure (normalizedData (x n)))
      (Eventually.of_forall fun n => abs_nonneg _) ?_ ?_
    · filter_upwards [hTevent] with n hn
      exact (O n).repaired_score_distance_le p q hp hpq (normalizedData (x n))
        (normalizedData_probability (x n) (hx n).1 hn) (hO n hn)
    · simpa using he.const_mul (805 * q / 24)
  have hdiff : Tendsto (fun n => (O n).score p q (normalizedData (x n)) -
      (R n).score p q (normalizedData (x n))) l (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using habs
  have hscore : Tendsto (fun n => (O n).score p q (normalizedData (x n))) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F))) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  have hα := LegalObject.activeMass_tendsto_eventually V F O p q hp hpq hq hz
    (fun n => normalizedData (x n)) hprob hscore
  have hT := (near_optimal_mass_limits V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).2.2
  have hactive : Tendsto (fun n => (O n).activeMass (dataWeight (x n))) l
      (𝓝 (activeLimit b t (familyTuranDensity F - p / q))) := by
    have hprod := hT.mul hα
    rw [activeLimit_formula b t _ (sub_nonneg.mpr hz)] at hprod
    apply hprod.congr'
    filter_upwards [hTevent] with n hn
    change dataMass (x n) * (∑ v ∈ (O n).active, dataWeight (x n) v / dataMass (x n)) = _
    rw [← Finset.sum_div]
    exact mul_div_cancel₀ _ (ne_of_gt hn)
  have hneutral : Tendsto (fun n => (O n).neutralMass (dataWeight (x n))) l
      (𝓝 (neutralLimit b t (familyTuranDensity F - p / q))) := by
    have hsub := hT.sub hactive
    rw [neutralLimit_formula b t _ (sub_nonneg.mpr hz)] at hsub
    simpa only [LegalObject.neutralMass_eq, dataMass] using hsub
  refine ⟨O, hO, hd, hscore, hα, hactive, hneutral, ?_⟩
  intro hgap
  exact LegalObject.innerDensity_tendsto_eventually V F O p q hp hpq hq hz
    (fun n => normalizedData (x n)) hprob hgap hscore

end Compiled
end TuranUniversality.Structural
