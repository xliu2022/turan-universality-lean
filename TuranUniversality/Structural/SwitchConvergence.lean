module

public import TuranUniversality.Structural.RecordComplete
public import TuranUniversality.Structural.CompactOptimization

@[expose] public section

/-! # Near-optimal legal scores determine the actual phase masses

The finite carriers may vary arbitrarily along the filter.  The conclusions
are derived from actual legal objects and their finite record scores.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural

namespace SwitchScalar

theorem optimalMass_tendsto {I : Type*} {l : Filter I} (δ : ℝ) (hδ : 0 ≤ δ)
    (α : I → ℝ) (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1)
    (hv : Tendsto (fun i => value δ (α i)) l (𝓝 (gain δ))) :
    Tendsto α l (𝓝 (optimalMass δ)) := by
  apply tendsto_of_unique_value_on_compact isCompact_Icc (value δ)
    (by unfold value; fun_prop) (optimalMass δ) (gain δ)
    (fun a _ he => (value_eq_gain_iff δ a hδ).mp he) α
    (Eventually.of_forall hα) hv

end SwitchScalar

namespace LegalObject

variable {I : Type*} {l : Filter I}
variable (V : I → Type*) [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
variable (F : Finset (FiniteGraph 3))
variable (O : ∀ i, LegalObject (homomorphicClosure F) (V i))
variable (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
variable (hz : p / q ≤ familyTuranDensity F)
variable (x : ∀ i, V i → ℝ) (hx : ∀ i, ProbabilityWeights (x i))

include hp hpq hq hz hx

theorem scalar_deficit_tendsto
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => SwitchScalar.gain (familyTuranDensity F - p / q) -
      SwitchScalar.value (familyTuranDensity F - p / q) ((O i).activeMass (x i)))
      l (𝓝 0) := by
  have hscaled : Tendsto (fun i => (q / 6) *
      (SwitchScalar.gain (familyTuranDensity F - p / q) -
        SwitchScalar.value (familyTuranDensity F - p / q) ((O i).activeMass (x i))))
      l (𝓝 0) := by
    apply squeeze_zero
      (fun i => ((O i).phase_deficit_nonneg F p q hp hpq hq hz (x i) (hx i)).2.1)
      (fun i => (O i).scalar_deficit_le F p q hp hpq hq hz (x i) (hx i))
    simpa using hs.const_sub (SwitchScalar.phaseScore p q (familyTuranDensity F))
  have hn : q / 6 ≠ 0 := by positivity
  simpa only [mul_div_cancel_left₀ _ hn, zero_div] using hscaled.div_const (q / 6)

/-- The unique scalar maximizer controls every near-optimal sequence,
including the zero-gap case. -/
theorem activeMass_tendsto
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (O i).activeMass (x i)) l
      (𝓝 (SwitchScalar.optimalMass (familyTuranDensity F - p / q))) := by
  have hd := scalar_deficit_tendsto V F O p q hp hpq hq hz x hx hs
  have hv : Tendsto (fun i => SwitchScalar.value (familyTuranDensity F - p / q)
      ((O i).activeMass (x i))) l (𝓝 (SwitchScalar.gain (familyTuranDensity F - p / q))) := by
    simpa using hd.const_sub (SwitchScalar.gain (familyTuranDensity F - p / q))
  exact SwitchScalar.optimalMass_tendsto _ (sub_nonneg.mpr hz) _
    (fun i => ⟨(O i).activeMass_nonneg (x i) (hx i).1,
      (O i).activeMass_le_one (x i) (hx i)⟩) hv

theorem relaxation_tendsto
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (O i).relaxedScore p q (x i) - (O i).score p q (x i)) l (𝓝 0) := by
  apply squeeze_zero
    (fun i => ((O i).relaxation_bounds p q hp hpq (x i) (hx i)).1)
    (fun i => (O i).relaxation_deficit_le F p q hp hpq hq hz (x i) (hx i))
  simpa using hs.const_sub (SwitchScalar.phaseScore p q (familyTuranDensity F))

/-- At a positive gap, the inner projection itself becomes asymptotically
extremal; this is stronger than convergence of its active mass. -/
theorem innerDensity_tendsto (hgap : p / q < familyTuranDensity F)
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (O i).innerDensity (x i)) l (𝓝 (familyTuranDensity F)) := by
  let a := SwitchScalar.optimalMass (familyTuranDensity F - p / q)
  have ha : Tendsto (fun i => (O i).activeMass (x i)) l (𝓝 a) :=
    activeMass_tendsto V F O p q hp hpq hq hz x hx hs
  have ha0 : 0 < a := SwitchScalar.optimalMass_pos _ (sub_pos.mpr hgap)
  have ha1 : a < 1 := (SwitchScalar.optimalMass_lt_three_quarters _
    (sub_nonneg.mpr hz)).trans (by norm_num)
  let d : I → ℝ := fun i => (q / 6) * (O i).activeMass (x i) ^ 3 *
    (1 - (O i).activeMass (x i))
  have hd : Tendsto d l (𝓝 ((q / 6) * a ^ 3 * (1 - a))) :=
    (tendsto_const_nhds.mul (ha.pow 3)).mul (tendsto_const_nhds.sub ha)
  have hdpos : 0 < (q / 6) * a ^ 3 * (1 - a) := by positivity
  have hi : Tendsto (fun i => (q / 6) * (familyTuranDensity F - (O i).innerDensity (x i)) *
      (O i).activeMass (x i) ^ 3 * (1 - (O i).activeMass (x i))) l (𝓝 0) := by
    apply squeeze_zero
      (fun i => ((O i).phase_deficit_nonneg F p q hp hpq hq hz (x i) (hx i)).2.2)
      (fun i => (O i).inner_deficit_le F p q hp hpq hq hz (x i) (hx i))
    simpa using hs.const_sub (SwitchScalar.phaseScore p q (familyTuranDensity F))
  have hprod : Tendsto (fun i => d i * (familyTuranDensity F - (O i).innerDensity (x i)))
      l (𝓝 0) := by
    convert hi using 1
    funext i
    dsimp [d]
    ring
  have hdiv := hprod.div hd (ne_of_gt hdpos)
  have heq : (fun i => d i * (familyTuranDensity F - (O i).innerDensity (x i)) / d i) =ᶠ[l]
      (fun i => familyTuranDensity F - (O i).innerDensity (x i)) := by
    filter_upwards [hd.eventually_ne (ne_of_gt hdpos)] with i hi
    exact mul_div_cancel_left₀ _ hi
  have hzero : Tendsto (fun i => familyTuranDensity F - (O i).innerDensity (x i)) l (𝓝 0) := by
    simpa only [zero_div] using hdiv.congr' heq
  simpa using hzero.const_sub (familyTuranDensity F)

theorem activeMass_zero_tendsto (hzero : familyTuranDensity F = p / q)
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (O i).activeMass (x i)) l (𝓝 0) := by
  simpa [hzero, SwitchScalar.optimalMass] using
    activeMass_tendsto V F O p q hp hpq hq hz x hx hs

end LegalObject
end TuranUniversality.Structural
