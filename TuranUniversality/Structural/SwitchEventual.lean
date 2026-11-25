module

public import TuranUniversality.Structural.SwitchConvergence

@[expose] public section

/-! # Eventual probability weights in the switch limit

Normalized data weights are probability weights only once their total mass
is positive. This version retains that exact domain and discards no input
graphs or vertices when passing to the limiting assertion.
-/

open Filter Topology

namespace TuranUniversality.Structural.LegalObject

variable {I : Type*} {l : Filter I}
variable (V : I → Type*) [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
variable (F : Finset (FiniteGraph 3))
variable (O : ∀ i, LegalObject (homomorphicClosure F) (V i))
variable (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
variable (hz : p / q ≤ familyTuranDensity F)
variable (x : ∀ i, V i → ℝ) (hx : ∀ᶠ i in l, ProbabilityWeights (x i))

include hp hpq hq hz hx

theorem activeMass_tendsto_eventually
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (O i).activeMass (x i)) l
      (𝓝 (SwitchScalar.optimalMass (familyTuranDensity F - p / q))) := by
  have hscaled : Tendsto (fun i => (q / 6) *
      (SwitchScalar.gain (familyTuranDensity F - p / q) -
        SwitchScalar.value (familyTuranDensity F - p / q) ((O i).activeMass (x i))))
      l (𝓝 0) := by
    refine squeeze_zero'
      (g := fun i => SwitchScalar.phaseScore p q (familyTuranDensity F) - (O i).score p q (x i))
      ?_ ?_ ?_
    · filter_upwards [hx] with i hi
      exact ((O i).phase_deficit_nonneg F p q hp hpq hq hz (x i) hi).2.1
    · filter_upwards [hx] with i hi
      exact (O i).scalar_deficit_le F p q hp hpq hq hz (x i) hi
    · simpa using hs.const_sub (SwitchScalar.phaseScore p q (familyTuranDensity F))
  have hn : q / 6 ≠ 0 := by positivity
  have hd : Tendsto (fun i => SwitchScalar.gain (familyTuranDensity F - p / q) -
      SwitchScalar.value (familyTuranDensity F - p / q) ((O i).activeMass (x i))) l (𝓝 0) := by
    simpa only [mul_div_cancel_left₀ _ hn, zero_div] using hscaled.div_const (q / 6)
  have hv : Tendsto (fun i => SwitchScalar.value (familyTuranDensity F - p / q)
      ((O i).activeMass (x i))) l (𝓝 (SwitchScalar.gain (familyTuranDensity F - p / q))) := by
    simpa using hd.const_sub (SwitchScalar.gain (familyTuranDensity F - p / q))
  apply tendsto_of_unique_value_on_compact (s := Set.Icc (0 : ℝ) 1) isCompact_Icc
    (SwitchScalar.value (familyTuranDensity F - p / q))
    (by unfold SwitchScalar.value; fun_prop)
    (SwitchScalar.optimalMass (familyTuranDensity F - p / q))
    (SwitchScalar.gain (familyTuranDensity F - p / q))
    (fun a _ he => (SwitchScalar.value_eq_gain_iff _ a (sub_nonneg.mpr hz)).mp he)
    (fun i => (O i).activeMass (x i)) ?_ hv
  filter_upwards [hx] with i hi
  exact ⟨(O i).activeMass_nonneg (x i) hi.1, (O i).activeMass_le_one (x i) hi⟩

theorem innerDensity_tendsto_eventually (hgap : p / q < familyTuranDensity F)
    (hs : Tendsto (fun i => (O i).score p q (x i)) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (O i).innerDensity (x i)) l (𝓝 (familyTuranDensity F)) := by
  let a := SwitchScalar.optimalMass (familyTuranDensity F - p / q)
  have ha : Tendsto (fun i => (O i).activeMass (x i)) l (𝓝 a) :=
    activeMass_tendsto_eventually V F O p q hp hpq hq hz x hx hs
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
    refine squeeze_zero'
      (g := fun i => SwitchScalar.phaseScore p q (familyTuranDensity F) - (O i).score p q (x i))
      ?_ ?_ ?_
    · filter_upwards [hx] with i hi
      exact ((O i).phase_deficit_nonneg F p q hp hpq hq hz (x i) hi).2.2
    · filter_upwards [hx] with i hi
      exact (O i).inner_deficit_le F p q hp hpq hq hz (x i) hi
    · simpa using hs.const_sub (SwitchScalar.phaseScore p q (familyTuranDensity F))
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

end TuranUniversality.Structural.LegalObject
