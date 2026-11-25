module

public import TuranUniversality.Structural.PhaseApproximationBasic
public import TuranUniversality.Structural.ExtremalProfileSequences

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Realizing every inner profile by actual finite phase objects

Positive-order hom-free graphs supply the active side. An equally large
neutral side is added. The normalized inner profile is exactly the input
profile, and every data collision probability tends to zero with the order.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.PhaseApproximation

open PhaseRoles RecordApproximation

variable {b t : ℕ}

noncomputable def object (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase : Bool) :
    LegalObject (homomorphicClosure F) (Fin G.1 ⊕ Fin G.1) := by
  letI : Inhabited (Fin G.1) := ⟨⟨0, hpos⟩⟩
  exact ofGraph F G.2 hG phase

noncomputable def dataWeights (G : FiniteGraph 3) (α : ℝ) : Fin G.1 ⊕ Fin G.1 → ℝ :=
  mixtureWeights α (fun _ => (G.1 : ℝ)⁻¹) (fun _ => (G.1 : ℝ)⁻¹)

noncomputable def weights (b t : ℕ) (G : FiniteGraph 3) (α : ℝ) :=
  Compiled.optimalWeights b t (dataWeights G α)

theorem uniform_probability (G : FiniteGraph 3) (hpos : 0 < G.1) :
    ProbabilityWeights (fun _ : Fin G.1 => (G.1 : ℝ)⁻¹) := by
  letI : Nonempty (Fin G.1) := ⟨⟨0, hpos⟩⟩
  simpa only [Fintype.card_fin] using (probabilityWeights_uniform (V := Fin G.1))

theorem dataWeights_probability (G : FiniteGraph 3) (hpos : 0 < G.1)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) : ProbabilityWeights (dataWeights G α) :=
  mixture_probability α hα hα1 _ _ (uniform_probability G hpos) (uniform_probability G hpos)

theorem weights_probability (G : FiniteGraph 3) (hpos : 0 < G.1)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) : ProbabilityWeights (weights b t G α) :=
  Compiled.optimalWeights_probability b t _ (dataWeights_probability G hpos α hα hα1)

theorem object_other_phase (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase s : Bool) (hs : s ≠ phase) :
    ((object F G hpos hG phase).inner s).edges = ∅ := by
  letI : Inhabited (Fin G.1) := ⟨⟨0, hpos⟩⟩
  exact ofGraph_other_phase F G.2 hG phase s hs

theorem object_roleWeight (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase : Bool) (α : ℝ) :
    roleWeight (object F G hpos hG phase) (weights b t G α) = optimalRoleWeight b t α := by
  letI : Inhabited (Fin G.1) := ⟨⟨0, hpos⟩⟩
  exact ofGraph_roleWeight F G.2 hG phase α _ _
    (uniform_probability G hpos).2 (uniform_probability G hpos).2

theorem object_innerProfile (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase : Bool) (α : ℝ) (hα : α ≠ 0) :
    innerProfile (object F G hpos hG phase) phase (weights b t G α) = SetFamily.profile G := by
  letI : Inhabited (Fin G.1) := ⟨⟨0, hpos⟩⟩
  change innerProfile (ofGraph F G.2 hG phase) phase
    (Compiled.optimalWeights b t (mixtureWeights α _ _)) = _
  rw [ofGraph_innerProfile F G.2 hG phase α hα _ _
    (uniform_probability G hpos).2 (uniform_probability G hpos).2]
  exact SetFamily.weightedProfile_uniform G

theorem dataWeights_squares (G : FiniteGraph 3) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∑ v, dataWeights G α v ^ 2 ≤ (G.1 : ℝ)⁻¹ :=
  uniform_mixture_squares G.1 α hα hα1

theorem weights_data_squares (G : FiniteGraph 3) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∑ v : Fin G.1 ⊕ Fin G.1, weights b t G α (.inr (.inr v)) ^ 2 ≤
      (4 / (OuterWeights.arity b t : ℝ)) ^ 2 * (G.1 : ℝ)⁻¹ := by
  simp only [weights, Compiled.optimalWeights, Sum.elim_inr, mul_pow, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (dataWeights_squares G α hα hα1) (sq_nonneg _)

theorem dataWeights_squares_tendsto (G : ℕ → FiniteGraph 3)
    (hsize : Tendsto (fun n => (G n).1) atTop atTop)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    Tendsto (fun n => ∑ v, dataWeights (G n) α v ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun v _ => sq_nonneg _))
    (fun n => dataWeights_squares (G n) α hα hα1)
  exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsize)

theorem weights_data_squares_tendsto (G : ℕ → FiniteGraph 3)
    (hsize : Tendsto (fun n => (G n).1) atTop atTop)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    Tendsto (fun n => ∑ v : Fin (G n).1 ⊕ Fin (G n).1,
      weights b t (G n) α (.inr (.inr v)) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun v _ => sq_nonneg _))
    (fun n => weights_data_squares (G n) α hα hα1)
  have hi : Tendsto (fun n => ((G n).1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsize)
  simpa only [mul_zero] using hi.const_mul ((4 / (OuterWeights.arity b t : ℝ)) ^ 2)

theorem profile_tendsto (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (G : ℕ → FiniteGraph 3) (hpos : ∀ n, 0 < (G n).1)
    (hG : ∀ n, familyHomFree F (G n).2)
    (hsize : Tendsto (fun n => (G n).1) atTop atTop)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (W : SetFamily.Profile 3)
    (hW : Tendsto (fun n => SetFamily.profile (G n)) atTop (𝓝 W)) :
    Tendsto (fun n => SetFamily.weightedProfile
      (Compiled.graph t Ω (object F (G n) (hpos n) (hG n) phase).records)
      (weights b t (G n) α)) atTop (𝓝 (phaseMap Ω phase (optimalRoleWeight b t α) W)) := by
  have hr : 0 < (OuterWeights.arity b t : ℝ) := Nat.cast_pos.mpr (OuterWeights.arity_pos b t)
  apply phaseMap_tendsto Ω phase (fun n => object F (G n) (hpos n) (hG n) phase)
    (fun n => object_other_phase F (G n) (hpos n) (hG n) phase)
    (fun n => weights b t (G n) α)
    (fun n => weights_probability (G n) (hpos n) α hα.le hα1.le) atTop _ W
  · change 0 < (4 / (OuterWeights.arity b t : ℝ)) * α
    positivity
  · change 0 < (4 / (OuterWeights.arity b t : ℝ)) * (1 - α)
    exact mul_pos (div_pos (by norm_num) hr) (sub_pos.mpr hα1)
  · simpa only [object_roleWeight] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => optimalRoleWeight b t α) atTop (𝓝 _))
  · simpa only [object_innerProfile _ _ _ _ _ _ (ne_of_gt hα)] using hW
  · exact weights_data_squares_tendsto G hsize α hα.le hα1.le

theorem object_relaxedScore (F : Finset (FiniteGraph 3)) (G : FiniteGraph 3)
    (hpos : 0 < G.1) (hG : familyHomFree F G.2) (phase : Bool)
    (p q α : ℝ) (hq : q ≠ 0) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (object F G hpos hG phase).relaxedScore p q (dataWeights G α) =
      160 * q / 24 + (q / 6) *
        ((6 * G.2.edgePolynomial (fun _ => (G.1 : ℝ)⁻¹) - p / q) * α ^ 3 * (1 - α) - α ^ 4) := by
  letI : Inhabited (Fin G.1) := ⟨⟨0, hpos⟩⟩
  exact ofGraph_relaxedScore F G.2 hG phase p q α hq hα hα1 _ _
    (uniform_probability G hpos) (uniform_probability G hpos)

theorem score_tendsto (F : Finset (FiniteGraph 3)) (phase : Bool)
    (G : ℕ → FiniteGraph 3) (hpos : ∀ n, 0 < (G n).1)
    (hG : ∀ n, familyHomFree F (G n).2)
    (hsize : Tendsto (fun n => (G n).1) atTop atTop)
    (p q z : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ z)
    (hval : Tendsto (fun n => 6 * (G n).2.edgePolynomial
      (fun _ => ((G n).1 : ℝ)⁻¹)) atTop (𝓝 z)) :
    Tendsto (fun n => (object F (G n) (hpos n) (hG n) phase).score p q
      (dataWeights (G n) (SwitchScalar.optimalMass (z - p / q)))) atTop
        (𝓝 (SwitchScalar.phaseScore p q z)) := by
  let α := SwitchScalar.optimalMass (z - p / q)
  have ha : 0 ≤ α := SwitchScalar.optimalMass_nonneg _ (sub_nonneg.mpr hz)
  have ha1 : α ≤ 1 := le_of_lt ((SwitchScalar.optimalMass_lt_three_quarters _
    (sub_nonneg.mpr hz)).trans (by norm_num))
  let O n := object F (G n) (hpos n) (hG n) phase
  let f : ℝ → ℝ := fun d => 160 * q / 24 + (q / 6) *
    ((d - p / q) * α ^ 3 * (1 - α) - α ^ 4)
  have hf : Continuous f := by fun_prop
  have hfz : f z = SwitchScalar.phaseScore p q z := by
    change 160 * q / 24 + (q / 6) * SwitchScalar.value (z - p / q) α = _
    rw [SwitchScalar.value_at_optimal _ (sub_nonneg.mpr hz)]
    rfl
  have hrel : Tendsto (fun n => (O n).relaxedScore p q (dataWeights (G n) α)) atTop
      (𝓝 (SwitchScalar.phaseScore p q z)) := by
    have h := (hf.tendsto z).comp hval
    rw [hfz] at h
    simpa only [O, object_relaxedScore _ _ _ _ _ _ _ _ (ne_of_gt hq) ha ha1,
      Function.comp_def, f] using h
  have hloss : Tendsto (fun n => (O n).relaxedScore p q (dataWeights (G n) α) -
      (O n).score p q (dataWeights (G n) α)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => ((O n).relaxation_squares_bound p q hp hpq _
        (dataWeights_probability (G n) (hpos n) α ha ha1)).1)
      (fun n => ((O n).relaxation_squares_bound p q hp hpq _
        (dataWeights_probability (G n) (hpos n) α ha ha1)).2)
    simpa only [mul_zero] using (dataWeights_squares_tendsto G hsize α ha ha1).const_mul
      ((161 * q / 24) * 6)
  have h := hrel.sub hloss
  simpa only [sub_sub_cancel, sub_zero] using h

theorem polynomial_tendsto (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (G : ℕ → FiniteGraph 3) (hpos : ∀ n, 0 < (G n).1)
    (hG : ∀ n, familyHomFree F (G n).2)
    (hsize : Tendsto (fun n => (G n).1) atTop atTop)
    (p q z : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ z)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hval : Tendsto (fun n => 6 * (G n).2.edgePolynomial
      (fun _ => ((G n).1 : ℝ)⁻¹)) atTop (𝓝 z)) :
    Tendsto (fun n => (Compiled.graph t Ω (object F (G n) (hpos n) (hG n) phase).records).edgePolynomial (weights b t (G n) (SwitchScalar.optimalMass (z - p / q)))) atTop
        (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q z)) := by
  have ha := SwitchScalar.optimalMass_nonneg _ (sub_nonneg.mpr hz)
  have ha1 : SwitchScalar.optimalMass (z - p / q) ≤ 1 := le_of_lt
    ((SwitchScalar.optimalMass_lt_three_quarters _ (sub_nonneg.mpr hz)).trans (by norm_num))
  have h := (score_tendsto F phase G hpos hG hsize p q z hp hpq hq hz hval).const_mul
    (OuterWeights.chi b t)
  apply h.congr'
  exact Eventually.of_forall (fun n =>
    (Compiled.optimalWeights_value Ω _ p q hΩ _
      (dataWeights_probability (G n) (hpos n) _ ha ha1)).symm)

end TuranUniversality.Structural.PhaseApproximation
