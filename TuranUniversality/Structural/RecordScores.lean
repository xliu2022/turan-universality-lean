module

public import TuranUniversality.Structural.RecordReward
public import TuranUniversality.Structural.RecordPayoff
public import TuranUniversality.Structural.SwitchScalar
public import TuranUniversality.Structural.InnerWeights

@[expose] public section

/-! # The actual score loss in Lemma 7.1

The observed and reconstructed corrections are compared on the same ordered
sample space.  Repeated samples retain their active-position penalties, while
their inner-edge reward is zero.  This supplies the full erasure penalty,
including the collision probability.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Arbitrary real edge values can be averaged through ordered edge samples. -/
theorem edge_value_mean {r : ℕ} (G : RGraph V r) (x : V → ℝ) (c : Finset V → ℝ) :
    weightedMean x (fun f : Fin r → V =>
      truth (Finset.univ.image f ∈ G.edges) * c (Finset.univ.image f)) =
      (r.factorial : ℝ) * ∑ e ∈ G.edges, c e * ∏ v ∈ e, x v := by
  classical
  have hp (f : Fin r → V) : truth (Finset.univ.image f ∈ G.edges) * c (Finset.univ.image f) =
      if (RGraph.oneEdge r).IsHom G f then c (Finset.univ.image f) else 0 := by
    by_cases h : (RGraph.oneEdge r).IsHom G f
    · simp [truth, h, (G.oneEdge_isHom f).mp h]
    · have he : Finset.univ.image f ∉ G.edges := fun he => h ((G.oneEdge_isHom f).mpr he)
      simp [truth, h, he]
  simp_rw [hp]
  unfold weightedMean
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_subtype _
    (p := fun f : Fin r → V => (RGraph.oneEdge r).IsHom G f)
    (by intro f; simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  calc
    (∑ f : {f : Fin r → V // (RGraph.oneEdge r).IsHom G f},
        productWeight x f.val * c (Finset.univ.image f.val)) =
        ∑ p : RGraph.EdgeOrdering G, c p.1.val * ∏ v ∈ p.1.val, x v := by
      symm
      apply Fintype.sum_equiv (Equiv.ofBijective G.orderedEdgeMap G.orderedEdgeMap_bijective)
      intro p
      change c p.1.val * (∏ v ∈ p.1.val, x v) =
        productWeight x (G.orderingFunction p) * c (Finset.univ.image (G.orderingFunction p))
      rw [G.orderingFunction_weight p x, G.orderingFunction_image p]
      ring
    _ = _ := by
      rw [Fintype.sum_sigma]
      have hc (e : G.edges) : Fintype.card (Fin r ≃ e.val) = r.factorial := by
        have he : Fintype.card (Fin r) = Fintype.card e.val := by simp [G.uniform _ e.property]
        rw [Fintype.card_equiv (Fintype.equivOfCardEq he), Fintype.card_fin]
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort G.edges (fun e : Finset V => c e * ∏ v ∈ e, x v)

namespace RecordSystem

def score (R : RecordSystem V) (p q : ℝ) (x : V → ℝ) : ℝ :=
  ∑ X ∈ R.recorded.edges, Label.payoff p q (R.label X) * ∏ v ∈ X, x v

noncomputable def observedCorrection (R : RecordSystem V) (p q : ℝ) (f : Fin 4 → V) : ℝ :=
  truth (R.Successful f) * Label.correction p q (R.label (Finset.univ.image f))

theorem observedCorrection_bounds (R : RecordSystem V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (f : Fin 4 → V) :
    -4 * q ≤ R.observedCorrection p q f ∧ R.observedCorrection p q f ≤ 4 * q := by
  classical
  by_cases h : R.Successful f
  · simpa [observedCorrection, truth, h] using Label.correction_bounds p q hp hpq
      (R.label (Finset.univ.image f))
  · simp only [observedCorrection, h, truth_false, zero_mul]
    constructor <;> linarith

/-- The missing background is exactly `160q * ε`. -/
theorem score_identity (R : RecordSystem V) (p q : ℝ) (x : V → ℝ) :
    24 * R.score p q x =
      160 * q * (1 - R.erasure x) + weightedMean x (R.observedCorrection p q) := by
  have hm := edge_value_mean R.recorded x (fun X => Label.correction p q (R.label X))
  have hsplit : R.score p q x = 160 * q * R.recorded.edgePolynomial x +
      ∑ X ∈ R.recorded.edges, Label.correction p q (R.label X) * ∏ v ∈ X, x v := by
    simp only [score, Label.payoff, add_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, RGraph.edgePolynomial]
  change weightedMean x (R.observedCorrection p q) = _ at hm
  norm_num at hm
  rw [hsplit, hm, erasure]
  ring

end RecordSystem

namespace LegalObject

variable {B : Finset (FiniteGraph 3)}

/-- The correction on all ordered samples, with multiplicity in the counts. -/
noncomputable def extendedCorrection (O : LegalObject B V) (p q : ℝ) (f : Fin 4 → V) : ℝ :=
  -p * truth (activeCount O.active f = 3) -
    4 * q * truth (activeCount O.active f = 4) + q * O.reward f

theorem extendedCorrection_bounds (O : LegalObject B V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (f : Fin 4 → V) :
    -4 * q ≤ O.extendedCorrection p q f ∧ O.extendedCorrection p q f ≤ 4 * q := by
  have hq : 0 ≤ q := hp.trans hpq
  have hr0 := O.reward_nonneg f
  have hr1 := O.reward_le_one f
  have hqr0 := mul_nonneg hq hr0
  have hqr1 := mul_le_mul_of_nonneg_left hr1 hq
  by_cases hc3 : activeCount O.active f = 3
  · have hc4 : activeCount O.active f ≠ 4 := by omega
    simp only [extendedCorrection, hc3, show (3 : ℕ) ≠ 4 by decide,
      truth_true, truth_false, mul_one, mul_zero, sub_zero]
    constructor <;> nlinarith
  · have hr := O.reward_eq_zero_of_count_ne f hc3
    by_cases hc4 : activeCount O.active f = 4
    · simp [extendedCorrection, truth, hc3, hc4, hr]
      linarith
    · simp [extendedCorrection, truth, hc3, hc4, hr]
      linarith

theorem extendedCorrection_mean (O : LegalObject B V) (p q : ℝ)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    weightedMean x (O.extendedCorrection p q) =
      -4 * p * (∑ v ∈ O.active, x v) ^ 3 * (1 - ∑ v ∈ O.active, x v) -
        4 * q * (∑ v ∈ O.active, x v) ^ 4 +
          24 * q * (1 - ∑ v ∈ O.active, x v) * O.projection.edgePolynomial x := by
  unfold extendedCorrection
  rw [weightedMean_add, weightedMean_sub, weightedMean_scale, weightedMean_scale,
    weightedMean_scale]
  change -p * countProbability x O.active 4 3 - 4 * q * countProbability x O.active 4 4 +
    q * weightedMean x O.reward = _
  rw [countProbability_four_three x hx, countProbability_four_four x hx, O.reward_mean x hx]
  ring

theorem corrections_agree {R : RecordSystem V} (O : LegalObject B V) (p q : ℝ)
    (f : Fin 4 → V) (h : ¬ R.Disagreement O f) :
    R.observedCorrection p q f = O.extendedCorrection p q f := by
  classical
  have h' : R.Successful f ∧ O.label (Finset.univ.image f) = R.label (Finset.univ.image f) := by
    simpa only [RecordSystem.Disagreement, not_or, not_not] using h
  have hg := h'.1
  have hl := h'.2
  have hcard := R.recorded.uniform _ hg
  have hlabel : O.Labels (Finset.univ.image f) (R.label (Finset.univ.image f)) := by
    rw [← hl]
    exact O.labels_label _ (by omega)
  have hc := (activeCount_injective O.active f hg.injective).trans hlabel.1
  rw [RecordSystem.observedCorrection, show truth (R.Successful f) = 1 by simp [truth, hg], one_mul]
  rw [extendedCorrection, hc, O.reward_eq_label f hg.injective hlabel]
  exact Label.correction_formula p q _

theorem correction_difference_le {R : RecordSystem V} (O : LegalObject B V) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (f : Fin 4 → V) :
    R.observedCorrection p q f - O.extendedCorrection p q f ≤
      8 * q * truth (R.Disagreement O f) := by
  classical
  by_cases h : R.Disagreement O f
  · have ho := R.observedCorrection_bounds p q hp hpq f
    have hc := O.extendedCorrection_bounds p q hp hpq f
    rw [show truth (R.Disagreement O f) = 1 by simp [truth, h], mul_one]
    linarith
  · rw [O.corrections_agree p q f h]
    simp [truth, h]

theorem mean_correction_difference_le {R : RecordSystem V} (O : LegalObject B V)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (x : V → ℝ) (hx : ProbabilityWeights x) :
    weightedMean x (R.observedCorrection p q) - weightedMean x (O.extendedCorrection p q) ≤
      8 * q * sampleProbability x (R.Disagreement O) := by
  have h := weightedMean_mono x hx.1 (O.correction_difference_le (R := R) p q hp hpq)
  rw [weightedMean_sub, weightedMean_scale] at h
  exact h

/-- The reconstructed relaxed score is bounded using the actual ordinary
finite-family density, through the homomorphic closure and real weight bound. -/
theorem extendedCorrection_upper (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (p q : ℝ) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F) (x : V → ℝ) (hx : ProbabilityWeights x) :
    160 * q + weightedMean x (O.extendedCorrection p q) ≤
      24 * SwitchScalar.phaseScore p q (familyTuranDensity F) := by
  let α := ∑ v ∈ O.active, x v
  have ha0 : 0 ≤ α := Finset.sum_nonneg (fun v _ => hx.1 v)
  have ha1 : α ≤ 1 := by
    calc
      α ≤ ∑ v : V, x v := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun v _ _ => hx.1 v)
      _ = 1 := hx.2
  have hi := O.projection_normalizedPolynomial_le F x hx.1
  have hr := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ 4 * q * (1 - α) by positivity)
  have hscalar := SwitchScalar.relaxed_le_phaseScore p q (familyTuranDensity F) α hq.le hz
  calc
    160 * q + weightedMean x (O.extendedCorrection p q) =
        160 * q - 4 * p * α ^ 3 * (1 - α) - 4 * q * α ^ 4 +
          24 * q * (1 - α) * O.projection.edgePolynomial x := by
      rw [O.extendedCorrection_mean p q x hx]
      dsimp only [α]
      ring
    _ ≤ 160 * q - 4 * p * α ^ 3 * (1 - α) - 4 * q * α ^ 4 +
        4 * q * familyTuranDensity F * α ^ 3 * (1 - α) := by
      dsimp only [α] at hr ⊢
      nlinarith only [hr]
    _ = 24 * (160 * q / 24 + (q / 6) * SwitchScalar.value (familyTuranDensity F - p / q) α) := by
      unfold SwitchScalar.value
      field_simp [ne_of_gt hq]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscalar (by norm_num)

end LegalObject

namespace RecordSystem

/-- The proof gives the slightly stronger loss `3L/(4·4!) = 5q`. -/
theorem score_le_strong_penalty (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) {R : RecordSystem V}
    (hlocal : R.LocallyLegal (homomorphicClosure F)) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    R.score p q x ≤ SwitchScalar.phaseScore p q (familyTuranDensity F) - 5 * q * R.erasure x := by
  obtain ⟨S, O, _, _, _, hdis⟩ := repair hlocal (homomorphicClosure_has_edges F hedges) x hx
  have hcor := O.mean_correction_difference_le (R := R) p q hp hpq x hx
  have hmul := mul_le_mul_of_nonneg_left hdis (show 0 ≤ 8 * q by positivity)
  have hupper := O.extendedCorrection_upper F p q hq hz x hx
  have hid := R.score_identity p q x
  nlinarith

/-- Lemma 7.1(iii), with exactly the paper's stated `L/(2·4!)` penalty. -/
theorem score_le_penalty (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) {R : RecordSystem V}
    (hlocal : R.LocallyLegal (homomorphicClosure F)) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    R.score p q x ≤ SwitchScalar.phaseScore p q (familyTuranDensity F) -
      (160 * q / 48) * R.erasure x := by
  have h := score_le_strong_penalty F hedges hlocal p q hp hpq hq hz x hx
  have he := R.erasure_nonneg x hx
  nlinarith [mul_nonneg hq.le he]

/-- All three conclusions of Lemma 7.1 for the actual homomorphically closed
inner family, including the common retained realization. -/
theorem record_repair (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) {R : RecordSystem V}
    (hlocal : R.LocallyLegal (homomorphicClosure F)) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    ∃ S : Finset V, ∃ O : LegalObject (homomorphicClosure F) V,
      1 - R.erasure x ≤ ∑ v ∈ S, x v ∧ O.active ⊆ S ∧ O.Realizes R S ∧
        sampleProbability x (R.Disagreement O) ≤ 5 * R.erasure x ∧
          R.score p q x ≤ SwitchScalar.phaseScore p q (familyTuranDensity F) -
            (160 * q / 48) * R.erasure x := by
  obtain ⟨S, O, hm, ha, hr, hd⟩ := repair hlocal (homomorphicClosure_has_edges F hedges) x hx
  exact ⟨S, O, hm, ha, hr, hd, score_le_penalty F hedges hlocal p q hp hpq hq hz x hx⟩

end RecordSystem
end TuranUniversality.Structural
