module

public import TuranUniversality.Structural.RecordApproximationBasic

@[expose] public section

/-! # The sharp score is approached by actual complete legal objects

For every `n` an actual hom-free extremal graph on `n+3` vertices supplies
the active part, and `n+3` additional vertices supply the neutral part.
The weight square sum is at most `1/(n+3)`. This gives a sequence in either
phase approaching the exact score `S(z)`, including the zero-gap case.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.RecordApproximation

variable (F : Finset (FiniteGraph 3))
variable (hedges : ∀ A ∈ F, A.2.edges.Nonempty)

noncomputable def maxGraph (n : ℕ) : RGraph (Fin (n + 3)) 3 :=
  Classical.choose (exists_homFreeMax F hedges (n + 3))

theorem maxGraph_free (n : ℕ) : familyHomFree F (maxGraph F hedges n) :=
  (Classical.choose_spec (exists_homFreeMax F hedges (n + 3))).1

theorem maxGraph_edges (n : ℕ) :
    (maxGraph F hedges n).edges.card = homFreeMax F (n + 3) :=
  (Classical.choose_spec (exists_homFreeMax F hedges (n + 3))).2

theorem maxGraph_value (n : ℕ) :
    6 * (maxGraph F hedges n).edgePolynomial (fun _ => ((n + 3 : ℕ) : ℝ)⁻¹) =
      homFreeLower F (n + 3) := by
  rw [RGraph.edgePolynomial_uniform_three, maxGraph_edges]
  norm_num [homFreeLower, Nat.factorial]

include hedges in
theorem inner_deficit_bounds (n : ℕ) :
    0 ≤ familyTuranDensity F - homFreeLower F (n + 3) ∧
      familyTuranDensity F - homFreeLower F (n + 3) ≤
        3 * ((n + 3 : ℕ) : ℝ)⁻¹ := by
  have hb := homFreeMax_bounds F hedges (n + 3) (by omega) (by omega)
  have hw := homFreeMax_interval_width F (n + 3) (by omega) (by omega)
  constructor
  · linarith
  · calc
      familyTuranDensity F - homFreeLower F (n + 3) ≤
          homFreeUpper F (n + 3) - homFreeLower F (n + 3) := by linarith
      _ ≤ (3 : ℝ) * ((3 : ℝ) - 1) / (2 * ((n + 3 : ℕ) : ℝ)) := hw
      _ = 3 * ((n + 3 : ℕ) : ℝ)⁻¹ := by
        norm_num [div_eq_mul_inv, mul_inv_rev]
        ring

theorem inverse_order_tendsto :
    Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 3).mpr
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

include hedges in
theorem inner_deficit_tendsto :
    Tendsto (fun n => familyTuranDensity F - homFreeLower F (n + 3)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (inner_deficit_bounds F hedges n).1)
    (fun n => (inner_deficit_bounds F hedges n).2)
  simpa using inverse_order_tendsto.const_mul 3

theorem maxGraph_value_tendsto :
    Tendsto (fun n => 6 * (maxGraph F hedges n).edgePolynomial
      (fun _ => ((n + 3 : ℕ) : ℝ)⁻¹)) atTop (𝓝 (familyTuranDensity F)) := by
  have hc : Tendsto (fun _ : ℕ => familyTuranDensity F) atTop
      (𝓝 (familyTuranDensity F)) := tendsto_const_nhds
  have h := hc.sub (inner_deficit_tendsto F hedges)
  simpa only [sub_sub_cancel, sub_zero, maxGraph_value] using h

noncomputable def object (phase : Bool) (n : ℕ) :
    LegalObject (homomorphicClosure F) (Fin (n + 3) ⊕ Fin (n + 3)) :=
  ofGraph F (maxGraph F hedges n) (maxGraph_free F hedges n) phase

noncomputable def weights (p q : ℝ) (n : ℕ) : Fin (n + 3) ⊕ Fin (n + 3) → ℝ :=
  mixtureWeights (SwitchScalar.optimalMass (familyTuranDensity F - p / q))
    (fun _ => ((n + 3 : ℕ) : ℝ)⁻¹) (fun _ => ((n + 3 : ℕ) : ℝ)⁻¹)

theorem uniform_probability (n : ℕ) :
    ProbabilityWeights (fun _ : Fin (n + 3) => ((n + 3 : ℕ) : ℝ)⁻¹) := by
  simpa only [Fintype.card_fin] using (probabilityWeights_uniform (V := Fin (n + 3)))

theorem weights_probability (p q : ℝ) (hz : p / q ≤ familyTuranDensity F) (n : ℕ) :
    ProbabilityWeights (weights F p q n) := by
  apply mixture_probability
  · exact SwitchScalar.optimalMass_nonneg _ (sub_nonneg.mpr hz)
  · have h := SwitchScalar.optimalMass_lt_three_quarters _ (sub_nonneg.mpr hz)
    linarith
  · exact uniform_probability n
  · exact uniform_probability n

theorem weights_squares (p q : ℝ) (hz : p / q ≤ familyTuranDensity F) (n : ℕ) :
    ∑ v, (weights F p q n v) ^ 2 ≤ ((n + 3 : ℕ) : ℝ)⁻¹ := by
  apply uniform_mixture_squares
  · exact SwitchScalar.optimalMass_nonneg _ (sub_nonneg.mpr hz)
  · have h := SwitchScalar.optimalMass_lt_three_quarters _ (sub_nonneg.mpr hz)
    linarith

theorem object_activeMass (phase : Bool) (p q : ℝ) (n : ℕ) :
    (object F hedges phase n).activeMass (weights F p q n) =
      SwitchScalar.optimalMass (familyTuranDensity F - p / q) := by
  apply ofGraph_activeMass
  exact (uniform_probability n).2

theorem relaxed_deficit (phase : Bool) (p q : ℝ) (hq : q ≠ 0)
    (hz : p / q ≤ familyTuranDensity F) (n : ℕ) :
    SwitchScalar.phaseScore p q (familyTuranDensity F) -
      (object F hedges phase n).relaxedScore p q (weights F p q n) =
      (q / 6) * (familyTuranDensity F - homFreeLower F (n + 3)) *
        (SwitchScalar.optimalMass (familyTuranDensity F - p / q)) ^ 3 *
          (1 - SwitchScalar.optimalMass (familyTuranDensity F - p / q)) := by
  have hα := SwitchScalar.optimalMass_nonneg _ (sub_nonneg.mpr hz)
  have hα1 : SwitchScalar.optimalMass (familyTuranDensity F - p / q) ≤ 1 := by
    have h := SwitchScalar.optimalMass_lt_three_quarters _ (sub_nonneg.mpr hz)
    linarith
  have hformula := ofGraph_relaxedScore F (maxGraph F hedges n)
    (maxGraph_free F hedges n) phase p q _ hq hα hα1
    (fun _ : Fin (n + 3) => ((n + 3 : ℕ) : ℝ)⁻¹)
    (fun _ : Fin (n + 3) => ((n + 3 : ℕ) : ℝ)⁻¹)
    (uniform_probability n) (uniform_probability n)
  change SwitchScalar.phaseScore p q (familyTuranDensity F) -
    (ofGraph F (maxGraph F hedges n) (maxGraph_free F hedges n) phase).relaxedScore
      p q (mixtureWeights _ _ _) = _
  rw [hformula, maxGraph_value]
  rw [SwitchScalar.phaseScore,
    ← SwitchScalar.value_at_optimal _ (sub_nonneg.mpr hz)]
  unfold SwitchScalar.value
  ring

/-- A quantitative error bound for actual complete records in either phase.
The estimate is uniform over all finite forbidden families with edged members. -/
theorem score_deficit_bounds (phase : Bool) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F) (n : ℕ) :
    0 ≤ SwitchScalar.phaseScore p q (familyTuranDensity F) -
      (object F hedges phase n).score p q (weights F p q n) ∧
    SwitchScalar.phaseScore p q (familyTuranDensity F) -
      (object F hedges phase n).score p q (weights F p q n) ≤
        (163 * q / 4) * ((n + 3 : ℕ) : ℝ)⁻¹ := by
  let O := object F hedges phase n
  let x := weights F p q n
  let α := SwitchScalar.optimalMass (familyTuranDensity F - p / q)
  have hx := weights_probability F p q hz n
  have hα : 0 ≤ α := SwitchScalar.optimalMass_nonneg _ (sub_nonneg.mpr hz)
  have hα1 : α ≤ 1 := by
    have h := SwitchScalar.optimalMass_lt_three_quarters _ (sub_nonneg.mpr hz)
    dsimp only [α]
    linarith
  have hunit0 : 0 ≤ α ^ 3 * (1 - α) :=
    mul_nonneg (pow_nonneg hα _) (sub_nonneg.mpr hα1)
  have hunit1 : α ^ 3 * (1 - α) ≤ 1 := by
    calc
      _ ≤ 1 * (1 - α) := mul_le_mul_of_nonneg_right
        (pow_le_one₀ hα hα1) (sub_nonneg.mpr hα1)
      _ ≤ 1 := by linarith
  have hinner := inner_deficit_bounds F hedges n
  have hrelax := relaxed_deficit F hedges phase p q (ne_of_gt hq) hz n
  have hscale : (q / 6) * (familyTuranDensity F - homFreeLower F (n + 3)) *
      (α ^ 3 * (1 - α)) ≤ (q / 2) * ((n + 3 : ℕ) : ℝ)⁻¹ := by
    calc
      _ ≤ (q / 6) * (familyTuranDensity F - homFreeLower F (n + 3)) :=
        mul_le_of_le_one_right (mul_nonneg (by positivity) hinner.1) hunit1
      _ ≤ (q / 6) * (3 * ((n + 3 : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hinner.2 (by positivity)
      _ = _ := by ring
  have hcoll := (O.relaxation_squares_bound p q hp hpq x hx).2
  have hsquares := weights_squares F p q hz n
  have hmul := mul_le_mul_of_nonneg_left hsquares
    (show 0 ≤ (161 * q / 24) * 6 by positivity)
  constructor
  · exact sub_nonneg.mpr (O.score_le_phaseScore F p q hp hpq hq hz x hx)
  · dsimp only [O, x, α] at hcoll hscale
    nlinarith only [hrelax, hcoll, hmul, hscale]

/-- Both phases admit a genuine sequence of complete finite legal objects
whose actual scores converge to the quartic optimum. -/
theorem score_tendsto (phase : Bool) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F) :
    Tendsto (fun n => (object F hedges phase n).score p q (weights F p q n))
      atTop (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F))) := by
  have hzdef : Tendsto (fun n => SwitchScalar.phaseScore p q (familyTuranDensity F) -
      (object F hedges phase n).score p q (weights F p q n)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => (score_deficit_bounds F hedges phase p q hp hpq hq hz n).1)
      (fun n => (score_deficit_bounds F hedges phase p q hp hpq hq hz n).2)
    simpa using inverse_order_tendsto.const_mul (163 * q / 4)
  have hc : Tendsto (fun _ : ℕ => SwitchScalar.phaseScore p q (familyTuranDensity F))
      atTop (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F))) := tendsto_const_nhds
  have h := hc.sub hzdef
  simpa only [sub_sub_cancel, sub_zero] using h

end TuranUniversality.Structural.RecordApproximation
