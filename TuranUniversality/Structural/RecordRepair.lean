module

public import TuranUniversality.Structural.RecordSampling

@[expose] public section

/-! # Mass and disagreement in record repair

Parts (i) and (ii) of Lemma 7.1, with arbitrary real probability weights.
The output is a genuine legal object on the original carrier; every vertex
outside the retained set is neutral.  Missing records and all repetitions
are included in the disagreement event.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem probabilityWeights_nonempty (x : V → ℝ) (hx : ProbabilityWeights x) : Nonempty V := by
  classical
  by_contra hn
  letI : IsEmpty V := not_nonempty_iff.mp hn
  have h := hx.2
  simp at h

theorem weightedMean_add {n : ℕ} (x : V → ℝ) (F G : (Fin n → V) → ℝ) :
    weightedMean x (fun f => F f + G f) = weightedMean x F + weightedMean x G := by
  simp [weightedMean, mul_add, Finset.sum_add_distrib]

namespace RecordSystem

theorem exists_large_sampleNeighborhood (R : RecordSystem V) (x : V → ℝ)
    (hx : ProbabilityWeights x) :
    ∃ f : Fin 3 → V, 1 - R.erasure x ≤ ∑ v ∈ R.sampleNeighborhood f, x v := by
  classical
  letI : Nonempty V := probabilityWeights_nonempty x hx
  obtain ⟨f, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3 → V))
    (fun f => ∑ v ∈ R.sampleNeighborhood f, x v) Finset.univ_nonempty
  have hm := weightedMean_mono x hx.1 (fun g => hmax g (Finset.mem_univ g))
  rw [R.mean_neighborhood_mass x, weightedMean_const x hx.2] at hm
  exact ⟨f, hm⟩

/-- Lemma 7.1(i): available records on a set of mass at least `1-ε` can be
realized, with all omitted vertices neutral in the output object. -/
theorem repair_mass {R : RecordSystem V} {B : Finset (FiniteGraph 3)}
    (hlocal : R.LocallyLegal B) (hedges : ∀ F ∈ B, F.2.edges.Nonempty)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    ∃ S : Finset V, ∃ O : LegalObject B V,
      1 - R.erasure x ≤ ∑ v ∈ S, x v ∧ O.active ⊆ S ∧ O.Realizes R S := by
  classical
  obtain ⟨f, hmass⟩ := R.exists_large_sampleNeighborhood x hx
  by_cases hf : Function.Injective f
  · have hA : (Finset.univ.image f).card = 3 := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    obtain ⟨O, hO, hreal⟩ := commonLink hlocal hedges (Finset.univ.image f) hA
    refine ⟨R.neighborhood (Finset.univ.image f), O, ?_, hO, hreal⟩
    simpa only [sampleNeighborhood, ite_eq_left hf] using hmass
  · refine ⟨∅, LegalObject.empty B hedges ∅, ?_, Finset.Subset.refl _, ?_⟩
    · simpa only [sampleNeighborhood, ite_eq_right hf] using hmass
    · intro X hX hXempty
      have hcard := R.recorded.uniform X hX
      have hzero := Finset.subset_empty.mp hXempty
      simp [hzero] at hcard

def Disagreement {B : Finset (FiniteGraph 3)} (R : RecordSystem V)
    (O : LegalObject B V) (f : Fin 4 → V) : Prop :=
  ¬ R.Successful f ∨ O.label (Finset.univ.image f) ≠ R.label (Finset.univ.image f)

/-- Pointwise union bound: a disagreement requires erasure or a vertex outside
the set on which all available records have been preserved. -/
theorem disagreement_indicator_le {R : RecordSystem V} {B : Finset (FiniteGraph 3)}
    (O : LegalObject B V) (S : Finset V) (hreal : O.Realizes R S) (f : Fin 4 → V) :
    truth (R.Disagreement O f) ≤ truth (¬ R.Successful f) + ∑ i, truth (f i ∉ S) := by
  classical
  have hnonneg : (0 : ℝ) ≤ ∑ i : Fin 4, truth (f i ∉ S) :=
    Finset.sum_nonneg (fun i _ => truth_nonneg _)
  by_cases hg : R.Successful f
  · by_cases hl : O.label (Finset.univ.image f) = R.label (Finset.univ.image f)
    · simpa [Disagreement, hg, hl, truth] using hnonneg
    · have hex : ∃ i, f i ∉ S := by
        by_contra! hn
        have hsub : Finset.univ.image f ⊆ S := by
          intro v hv
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
          exact hn i
        have hcard := R.recorded.uniform _ hg
        have hlabels := hreal _ hg hsub
        exact hl ((O.labels_iff _ (by omega) _).mp hlabels)
      obtain ⟨i, hi⟩ := hex
      have hs : (1 : ℝ) ≤ ∑ j : Fin 4, truth (f j ∉ S) := by
        simpa [hi, truth] using Finset.single_le_sum
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
            truth_nonneg (f j ∉ S))
          (Finset.mem_univ i)
      simpa [Disagreement, hg, hl, truth] using hs
  · simpa only [Disagreement, hg, not_false_eq_true, true_or, truth_true] using
      (show (1 : ℝ) ≤ 1 + ∑ i : Fin 4, truth (f i ∉ S) by linarith)

theorem disagreement_probability_le {R : RecordSystem V} {B : Finset (FiniteGraph 3)}
    (O : LegalObject B V) (S : Finset V) (hreal : O.Realizes R S)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    sampleProbability x (R.Disagreement O) ≤
      R.erasure x + 4 * (1 - ∑ v ∈ S, x v) := by
  classical
  have hm := weightedMean_mono x hx.1 (disagreement_indicator_le O S hreal)
  have hi (i : Fin 4) : weightedMean x (fun f : Fin 4 → V =>
      truth (f i ∉ S)) = 1 - ∑ v ∈ S, x v := by
    change sampleProbability x (fun f : Fin 4 → V => ¬ f i ∈ S) = _
    rw [sampleProbability_compl x hx, coordinate_probability x hx i S]
  rw [weightedMean_add, weightedMean_sum] at hm
  simp_rw [hi] at hm
  change sampleProbability x (R.Disagreement O) ≤
    sampleProbability x (fun f => ¬ R.Successful f) +
      ∑ _i : Fin 4, (1 - ∑ v ∈ S, x v) at hm
  simpa only [R.erasure_probability x hx, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hm

/-- Lemma 7.1(i)-(ii), including all repetitions and missing records in the
disagreement probability and retaining the original real weights. -/
theorem repair {R : RecordSystem V} {B : Finset (FiniteGraph 3)}
    (hlocal : R.LocallyLegal B) (hedges : ∀ F ∈ B, F.2.edges.Nonempty)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    ∃ S : Finset V, ∃ O : LegalObject B V,
      1 - R.erasure x ≤ ∑ v ∈ S, x v ∧ O.active ⊆ S ∧ O.Realizes R S ∧
        sampleProbability x (R.Disagreement O) ≤ 5 * R.erasure x := by
  obtain ⟨S, O, hmass, hactive, hreal⟩ := repair_mass hlocal hedges x hx
  refine ⟨S, O, hmass, hactive, hreal, ?_⟩
  have h := disagreement_probability_le O S hreal x hx
  linarith

end RecordSystem
end TuranUniversality.Structural
