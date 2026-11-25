module

public import TuranUniversality.Structural.RecordScores
public import TuranUniversality.Structural.RecordCollisions

@[expose] public section

/-! # Complete legal scores and the three actual phase deficits

Complete records are all four-element subsets of the actual finite carrier.
The relaxed score is an expectation on all ordered samples, so its difference
from the finite score is precisely a collision loss, not an assumed error.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.LegalObject

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {B : Finset (FiniteGraph 3)}

def records (O : LegalObject B V) : RecordSystem V where
  recorded := ⟨Finset.univ.powersetCard 4, by
    intro X hX
    exact (Finset.mem_powersetCard.mp hX).2⟩
  label := O.label

@[simp] theorem mem_records (O : LegalObject B V) (X : Finset V) :
    X ∈ O.records.recorded.edges ↔ X.card = 4 := by
  simp [records]

theorem records_successful (O : LegalObject B V) (f : Fin 4 → V) :
    O.records.Successful f ↔ Function.Injective f := by
  constructor
  · exact RecordSystem.Successful.injective
  · intro hf
    change Finset.univ.image f ∈ O.records.recorded.edges
    rw [mem_records]
    simp [Finset.card_image_of_injective _ hf]

/-- Restrict the active set and both inner edge sets, retaining the ambient
carrier only so local-record comparisons are literally on the same vertices. -/
def restrict (O : LegalObject B V) (S : Finset V) : LegalObject B V where
  active := O.active ∩ S
  inner a := ⟨(O.inner a).edges.filter (· ⊆ S), by
    intro e he
    exact (O.inner a).uniform e (Finset.mem_filter.mp he).1⟩
  supported := by
    intro a e he v hv
    obtain ⟨he, hS⟩ := Finset.mem_filter.mp he
    exact Finset.mem_inter.mpr ⟨O.supported a e he hv, hS hv⟩
  onePhase := by
    rcases O.onePhase with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  free := by
    intro a F hF f hf he
    apply O.free a F hF f (fun v => (Finset.mem_inter.mp (hf v)).1)
    exact ⟨he.1, fun e heF => (Finset.mem_filter.mp (he.2 e heF)).1⟩

theorem restrict_labels (O : LegalObject B V) (S X : Finset V) (hXS : X ⊆ S)
    (l : Label) : (O.restrict S).Labels X l ↔ O.Labels X l := by
  have hi : X ∩ (O.active ∩ S) = X ∩ O.active := by
    ext v
    simp only [Finset.mem_inter]
    aesop
  have hs : X ∩ O.active ⊆ S := Finset.inter_subset_left.trans hXS
  simp only [Labels, restrict, hi, Finset.mem_filter, hs, and_true]

theorem records_locallyLegal (O : LegalObject B V) : O.records.LocallyLegal B := by
  intro S _
  refine ⟨O.restrict S, Finset.inter_subset_right, ?_⟩
  intro X hX hXS
  apply (O.restrict_labels S X hXS (O.label X)).mpr
  exact O.labels_label X (by have := (O.mem_records X).mp hX; omega)

def score (O : LegalObject B V) (p q : ℝ) (x : V → ℝ) : ℝ :=
  O.records.score p q x

def activeMass (O : LegalObject B V) (x : V → ℝ) : ℝ := ∑ v ∈ O.active, x v

noncomputable def relaxedScore (O : LegalObject B V) (p q : ℝ) (x : V → ℝ) : ℝ :=
  (160 * q + weightedMean x (O.extendedCorrection p q)) / 24

noncomputable def innerDensity (O : LegalObject B V) (x : V → ℝ) : ℝ :=
  6 * O.projection.edgePolynomial x / O.activeMass x ^ 3

theorem activeMass_nonneg (O : LegalObject B V) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    0 ≤ O.activeMass x := Finset.sum_nonneg (fun v _ => hx v)

theorem activeMass_le_one (O : LegalObject B V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    O.activeMass x ≤ 1 := by
  calc
    O.activeMass x ≤ ∑ v, x v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ => hx.1 v)
    _ = 1 := hx.2

theorem projection_eq_zero_of_mass (O : LegalObject B V) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hm : O.activeMass x = 0) :
    O.projection.edgePolynomial x = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hc : e.card = 3 := O.projection.uniform e he
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
  have hva := O.projection_supported e he hv
  have hxv : x v = 0 := by
    have hle : x v ≤ O.activeMass x := Finset.single_le_sum (fun v _ => hx v) hva
    rw [hm] at hle
    exact le_antisymm hle (hx v)
  exact Finset.prod_eq_zero hv hxv

theorem innerDensity_mul_mass (O : LegalObject B V) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    O.innerDensity x * O.activeMass x ^ 3 = 6 * O.projection.edgePolynomial x := by
  by_cases hm : O.activeMass x = 0
  · simp [innerDensity, hm, O.projection_eq_zero_of_mass x hx hm]
  · exact div_mul_cancel₀ _ (pow_ne_zero _ hm)

theorem innerDensity_nonneg (O : LegalObject B V) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    0 ≤ O.innerDensity x := by
  unfold innerDensity
  exact div_nonneg (mul_nonneg (by norm_num) (O.projection.edgePolynomial_nonneg hx))
    (pow_nonneg (O.activeMass_nonneg x hx) _)

theorem innerDensity_le (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    O.innerDensity x ≤ familyTuranDensity F := by
  by_cases hm : O.activeMass x = 0
  · simp only [innerDensity, hm, zero_pow (by decide : 3 ≠ 0), div_zero]
    exact familyTuranDensity_nonneg F
  · have hp : 0 < O.activeMass x := lt_of_le_of_ne (O.activeMass_nonneg x hx) (Ne.symm hm)
    apply (div_le_iff₀ (pow_pos hp 3)).mpr
    exact O.projection_normalizedPolynomial_le F x hx

theorem extendedPayoff_bounds (O : LegalObject B V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (f : Fin 4 → V) :
    156 * q ≤ 160 * q + O.extendedCorrection p q f ∧
      160 * q + O.extendedCorrection p q f ≤ 161 * q := by
  have hl := (O.extendedCorrection_bounds p q hp hpq f).1
  have hq : 0 ≤ q := hp.trans hpq
  have h1 := mul_nonneg hp (truth_nonneg (activeCount O.active f = 3))
  have h2 := mul_nonneg (show 0 ≤ 4 * q by positivity)
    (truth_nonneg (activeCount O.active f = 4))
  have h3 := mul_le_mul_of_nonneg_left (O.reward_le_one f) hq
  constructor
  · linarith
  · unfold extendedCorrection
    nlinarith

theorem score_mean (O : LegalObject B V) (p q : ℝ) (x : V → ℝ) :
    weightedMean x (fun f : Fin 4 → V =>
      truth (Function.Injective f) * (160 * q + O.extendedCorrection p q f)) =
        24 * O.score p q x := by
  have he := edge_value_mean O.records.recorded x (fun X => Label.payoff p q (O.label X))
  norm_num only [Nat.factorial] at he
  calc
    _ = weightedMean x (fun f : Fin 4 → V =>
        truth (O.records.Successful f) * Label.payoff p q (O.label (Finset.univ.image f))) := by
      apply weightedMean_congr
      intro f
      by_cases hf : Function.Injective f
      · have hs := (O.records_successful f).mpr hf
        have hd : ¬ O.records.Disagreement O f := by
          change ¬ (¬ O.records.Successful f ∨ O.label _ ≠ O.label _)
          exact not_or.mpr ⟨not_not.mpr hs, not_not.mpr rfl⟩
        have hc := O.corrections_agree p q f hd
        have ht : truth (O.records.Successful f) = 1 := by simp [truth, hs]
        simp only [RecordSystem.observedCorrection, ht, one_mul] at hc
        simp only [hf, hs, truth_true, one_mul]
        rw [← hc]
        rfl
      · have hs : ¬ O.records.Successful f := fun h => hf ((O.records_successful f).mp h)
        simp [truth, hf, hs]
    _ = _ := he

theorem relaxation_identity (O : LegalObject B V) (p q : ℝ)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    24 * (O.relaxedScore p q x - O.score p q x) =
      weightedMean x (fun f : Fin 4 → V =>
        truth (¬ Function.Injective f) * (160 * q + O.extendedCorrection p q f)) := by
  calc
    _ = weightedMean x (fun f : Fin 4 → V => 160 * q + O.extendedCorrection p q f) -
        weightedMean x (fun f : Fin 4 → V =>
          truth (Function.Injective f) * (160 * q + O.extendedCorrection p q f)) := by
      rw [weightedMean_add, weightedMean_const x hx.2, O.score_mean]
      unfold relaxedScore
      ring
    _ = _ := by
      rw [← weightedMean_sub]
      apply weightedMean_congr
      intro f
      by_cases hf : Function.Injective f <;> simp [truth, hf]

theorem relaxation_bounds (O : LegalObject B V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (x : V → ℝ) (hx : ProbabilityWeights x) :
    0 ≤ O.relaxedScore p q x - O.score p q x ∧
      O.relaxedScore p q x - O.score p q x ≤
        (161 * q / 24) * sampleProbability x (fun f : Fin 4 → V => ¬ Function.Injective f) := by
  have hq : 0 ≤ q := hp.trans hpq
  have hlow : 0 ≤ weightedMean x (fun f : Fin 4 → V =>
      truth (¬ Function.Injective f) * (160 * q + O.extendedCorrection p q f)) := by
    apply Finset.sum_nonneg
    intro f _
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => hx.1 _)
      (mul_nonneg (truth_nonneg _) (by have := (O.extendedPayoff_bounds p q hp hpq f).1; linarith))
  have hup := weightedMean_mono x hx.1 (fun f : Fin 4 → V =>
    mul_le_mul_of_nonneg_left (O.extendedPayoff_bounds p q hp hpq f).2
      (truth_nonneg (¬ Function.Injective f)))
  have hscale : weightedMean x (fun f : Fin 4 → V => truth (¬ Function.Injective f) * (161 * q)) =
      (161 * q) * sampleProbability x (fun f : Fin 4 → V => ¬ Function.Injective f) := by
    simp_rw [mul_comm (truth _) (161 * q)]
    exact weightedMean_scale x _ _
  rw [hscale, ← O.relaxation_identity p q x hx] at hup
  rw [← O.relaxation_identity p q x hx] at hlow
  constructor <;> nlinarith

/-- The exact collision coefficient from the paper's `colourupper` inequality. -/
theorem relaxation_squares_bound (O : LegalObject B V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (x : V → ℝ) (hx : ProbabilityWeights x) :
    0 ≤ O.relaxedScore p q x - O.score p q x ∧
      O.relaxedScore p q x - O.score p q x ≤ (161 * q / 24) * 6 * ∑ v, (x v) ^ 2 := by
  have h := O.relaxation_bounds p q hp hpq x hx
  have hc := mul_le_mul_of_nonneg_left (collision_probability_le x hx)
    (show 0 ≤ 161 * q / 24 by have hq := hp.trans hpq; positivity)
  exact ⟨h.1, h.2.trans (by nlinarith only [hc])⟩

theorem relaxedScore_formula (O : LegalObject B V) (p q : ℝ) (hq : q ≠ 0)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    O.relaxedScore p q x = 160 * q / 24 + (q / 6) *
      ((O.innerDensity x - p / q) * O.activeMass x ^ 3 * (1 - O.activeMass x) -
        O.activeMass x ^ 4) := by
  have hi := O.innerDensity_mul_mass x hx.1
  have hiq := congrArg (fun a : ℝ => q * (1 - O.activeMass x) * a) hi
  rw [relaxedScore, O.extendedCorrection_mean p q x hx]
  change (160 * q + (-4 * p * O.activeMass x ^ 3 * (1 - O.activeMass x) -
    4 * q * O.activeMass x ^ 4 + 24 * q * (1 - O.activeMass x) * O.projection.edgePolynomial x)) /
      24 = _
  field_simp [hq]
  nlinarith only [hiq]

/-- The three summands in the source phase-deficit identity, without replacing
the actual finite score by its relaxed expectation. -/
theorem phase_deficit (O : LegalObject B V) (p q z : ℝ) (hq : q ≠ 0)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    SwitchScalar.phaseScore p q z - O.score p q x =
      (O.relaxedScore p q x - O.score p q x) +
      (q / 6) * (SwitchScalar.gain (z - p / q) -
        SwitchScalar.value (z - p / q) (O.activeMass x)) +
      (q / 6) * (z - O.innerDensity x) * O.activeMass x ^ 3 * (1 - O.activeMass x) := by
  rw [O.relaxedScore_formula p q hq x hx]
  unfold SwitchScalar.phaseScore SwitchScalar.value
  ring

theorem score_le_phaseScore (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    O.score p q x ≤ SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  have hl := (O.relaxation_bounds p q hp hpq x hx).1
  have hu := O.extendedCorrection_upper F p q hq hz x hx
  unfold relaxedScore at hl
  linarith

theorem phase_deficit_nonneg (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    0 ≤ O.relaxedScore p q x - O.score p q x ∧
    0 ≤ (q / 6) * (SwitchScalar.gain (familyTuranDensity F - p / q) -
      SwitchScalar.value (familyTuranDensity F - p / q) (O.activeMass x)) ∧
    0 ≤ (q / 6) * (familyTuranDensity F - O.innerDensity x) *
      O.activeMass x ^ 3 * (1 - O.activeMass x) := by
  refine ⟨(O.relaxation_bounds p q hp hpq x hx).1, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr
      (SwitchScalar.value_le_gain _ _ (sub_nonneg.mpr hz)))
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (sub_nonneg.mpr (O.innerDensity_le F x hx.1)))
      (pow_nonneg (O.activeMass_nonneg x hx.1) 3))
      (sub_nonneg.mpr (O.activeMass_le_one x hx))

theorem scalar_deficit_le (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    (q / 6) * (SwitchScalar.gain (familyTuranDensity F - p / q) -
      SwitchScalar.value (familyTuranDensity F - p / q) (O.activeMass x)) ≤
        SwitchScalar.phaseScore p q (familyTuranDensity F) - O.score p q x := by
  have he := O.phase_deficit p q (familyTuranDensity F) (ne_of_gt hq) x hx
  have hn := O.phase_deficit_nonneg F p q hp hpq hq hz x hx
  linarith

theorem inner_deficit_le (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    (q / 6) * (familyTuranDensity F - O.innerDensity x) *
      O.activeMass x ^ 3 * (1 - O.activeMass x) ≤
        SwitchScalar.phaseScore p q (familyTuranDensity F) - O.score p q x := by
  have he := O.phase_deficit p q (familyTuranDensity F) (ne_of_gt hq) x hx
  have hn := O.phase_deficit_nonneg F p q hp hpq hq hz x hx
  linarith

theorem relaxation_deficit_le (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    O.relaxedScore p q x - O.score p q x ≤
      SwitchScalar.phaseScore p q (familyTuranDensity F) - O.score p q x := by
  have he := O.phase_deficit p q (familyTuranDensity F) (ne_of_gt hq) x hx
  have hn := O.phase_deficit_nonneg F p q hp hpq hq hz x hx
  linarith

end TuranUniversality.Structural.LegalObject
