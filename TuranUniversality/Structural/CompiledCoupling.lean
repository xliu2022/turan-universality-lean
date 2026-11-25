module

public import TuranUniversality.Structural.CompiledRepair
public import TuranUniversality.Structural.WeightedProfiles
public import TuranUniversality.Density.WeightedHomConvergence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual compiled edge mismatch is controlled by record disagreement

The mismatch graph is contained in an actual expansion of the bad data
four-sets. All seven support pools are included in this expansion. Its
polynomial is bounded by the disagreement probability, and hence every
ordinary homomorphism coordinate is preserved when repair error vanishes.
-/

open scoped BigOperators symmDiff
open Filter Topology

namespace TuranUniversality.Structural.Compiled

open Density

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}
variable {B : Finset (FiniteGraph 3)}

noncomputable def badRecords (R : RecordSystem V) (O : LegalObject B V) : RecordSystem V := by
  classical
  exact {
    recorded := {
      edges := (Finset.univ.powersetCard 4).filter (fun X =>
        X ∉ R.recorded.edges ∨ O.label X ≠ R.label X)
      uniform := fun X hX => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hX).1).2 }
    label := fun _ => .inl ⟨0, by decide⟩ }

@[simp] theorem mem_badRecords (R : RecordSystem V) (O : LegalObject B V) (X : Finset V) :
    X ∈ (badRecords R O).recorded.edges ↔
      X.card = 4 ∧ (X ∉ R.recorded.edges ∨ O.label X ≠ R.label X) := by
  classical
  simp [badRecords]

def allPools (Ω : Label → Finset (Cube.Word b)) : Finset (Cube.Word b) := Finset.univ.biUnion Ω

theorem poolGraph_subset_allPools (Ω : Label → Finset (Cube.Word b)) (a : Label) :
    (Support.poolGraph (Ω a)).edges ⊆ (Support.poolGraph (allPools Ω)).edges := by
  intro Z hZ
  obtain ⟨w, hw, hZ⟩ := Finset.mem_biUnion.mp hZ
  exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hw⟩, hZ⟩

theorem mismatch_subset_badExpansion (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (O : LegalObject B V) :
    ((graph t Ω R).edgeSymmDifference (graph t Ω O.records)).edges ⊆
      (graph t (fun _ => allPools Ω) (badRecords R O)).edges := by
  intro e he
  rcases Finset.mem_symmDiff.mp he with he | he
  · obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω R e).mp he.1
    have hc := R.recorded.uniform X hX
    have hbad : O.label X ≠ R.label X := by
      intro hl
      apply he.2
      apply (mem_graph Ω O.records _).mpr
      refine ⟨X, (O.mem_records X).mpr hc, Z, ?_, rfl⟩
      change Z ∈ (Support.poolGraph (Ω (O.label X))).edges
      rwa [hl]
    exact (mem_graph _ _ _).mpr ⟨X, (mem_badRecords R O X).mpr ⟨hc, Or.inr hbad⟩,
      Z, poolGraph_subset_allPools Ω _ hZ, rfl⟩
  · obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω O.records e).mp he.1
    have hc := O.records.recorded.uniform X hX
    have hbad : X ∉ R.recorded.edges ∨ O.label X ≠ R.label X := by
      by_cases hr : X ∈ R.recorded.edges
      · right
        intro hl
        apply he.2
        apply (mem_graph Ω R _).mpr
        refine ⟨X, hr, Z, ?_, rfl⟩
        change Z ∈ (Support.poolGraph (Ω (O.label X))).edges at hZ
        rwa [← hl]
      · exact Or.inl hr
    exact (mem_graph _ _ _).mpr ⟨X, (mem_badRecords R O X).mpr ⟨hc, hbad⟩,
      Z, poolGraph_subset_allPools Ω _ hZ, rfl⟩

theorem badRecord_polynomial_le (R : RecordSystem V) (O : LegalObject B V)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    (badRecords R O).recorded.edgePolynomial x ≤ sampleProbability x (R.Disagreement O) / 24 := by
  have hpoint (f : Fin 4 → V) :
      (RGraph.oneEdge 4).homIndicator (badRecords R O).recorded f ≤ truth (R.Disagreement O f) := by
    by_cases hf : (RGraph.oneEdge 4).IsHom (badRecords R O).recorded f
    · have hm := (mem_badRecords R O _).mp
        (((badRecords R O).recorded.oneEdge_isHom f).mp hf)
      have hd : R.Disagreement O f := by
        exact hm.2
      rw [RGraph.homIndicator_of_hom _ _ hf]
      simp [truth, hd]
    · rw [RGraph.homIndicator_of_not_hom _ _ hf]
      exact truth_nonneg _
  have h := weightedMean_mono x hx hpoint
  rw [RGraph.weightedMean_oneEdge] at h
  norm_num only [Nat.factorial] at h
  change 24 * (badRecords R O).recorded.edgePolynomial x ≤ sampleProbability x (R.Disagreement O) at h
  linarith

theorem constantPool_polynomial_le (Θ : Finset (Cube.Word b)) (R : RecordSystem V)
    (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) (hT : 0 < dataMass x) :
    (graph t (fun _ => Θ) R).edgePolynomial x ≤
      factor x * (Θ.card : ℝ) * R.recorded.edgePolynomial (normalizedData x) := by
  have h := polynomial_le (fun _ => Θ) R x hx
  change (graph t (fun _ => Θ) R).edgePolynomial x ≤
    (∏ i, suspensionWeight x i) * ((1 / 25 : ℝ) ^ b * ∏ i, blockMass x i ^ 3) *
      ∑ X ∈ R.recorded.edges, (Θ.card : ℝ) * ∏ v ∈ X, dataWeight x v at h
  rw [← Finset.mul_sum] at h
  change (graph t (fun _ => Θ) R).edgePolynomial x ≤
    (∏ i, suspensionWeight x i) * ((1 / 25 : ℝ) ^ b * ∏ i, blockMass x i ^ 3) *
      ((Θ.card : ℝ) * R.recorded.edgePolynomial (dataWeight x)) at h
  have he : dataWeight x = fun v => dataMass x * normalizedData x v := by
    funext v
    simp [normalizedData, ne_of_gt hT, mul_div_cancel₀]
  rw [he, RGraph.edgePolynomial_scale] at h
  convert h using 1 <;> unfold factor OuterWeights.massFactor <;> ring

theorem mismatch_polynomial_le (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (O : LegalObject B V) (x : Vertex b t V → ℝ)
    (hx : ProbabilityWeights x) (hT : 0 < dataMass x) :
    ((graph t Ω R).edgeSymmDifference (graph t Ω O.records)).edgePolynomial x ≤
      (OuterWeights.chi b t * (allPools Ω).card / 24) *
        sampleProbability (normalizedData x) (R.Disagreement O) := by
  have hn := normalizedData_probability x hx.1 hT
  have hb := (badRecords R O).recorded.edgePolynomial_nonneg hn.1
  have hc : 0 ≤ OuterWeights.chi b t * ((allPools Ω).card : ℝ) :=
    mul_nonneg (OuterWeights.chi_pos b t).le (Nat.cast_nonneg _)
  calc
    _ ≤ (graph t (fun _ => allPools Ω) (badRecords R O)).edgePolynomial x :=
      RGraph.edgePolynomial_mono _ _ (mismatch_subset_badExpansion Ω R O) hx.1
    _ ≤ factor x * ((allPools Ω).card : ℝ) *
        (badRecords R O).recorded.edgePolynomial (normalizedData x) :=
      constantPool_polynomial_le _ _ x hx.1 hT
    _ ≤ OuterWeights.chi b t * ((allPools Ω).card : ℝ) *
        (badRecords R O).recorded.edgePolynomial (normalizedData x) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (factor_le x hx) (Nat.cast_nonneg _)) hb
    _ ≤ OuterWeights.chi b t * ((allPools Ω).card : ℝ) *
        (sampleProbability (normalizedData x) (R.Disagreement O) / 24) :=
      mul_le_mul_of_nonneg_left (badRecord_polynomial_le R O _ hn.1) hc
    _ = _ := by ring

theorem mismatch_tendsto {I : Type*} {X : I → Type*}
    [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)] (l : Filter I)
    (Ω : Label → Finset (Cube.Word b)) (R : ∀ i, RecordSystem (X i))
    (O : ∀ i, LegalObject B (X i)) (x : ∀ i, Vertex b t (X i) → ℝ)
    (hx : ∀ i, ProbabilityWeights (x i))
    (hT : ∀ᶠ i in l, 0 < dataMass (x i))
    (hd : Tendsto (fun i => sampleProbability (normalizedData (x i)) ((R i).Disagreement (O i)))
      l (𝓝 0)) :
    Tendsto (fun i => ((graph t Ω (R i)).edgeSymmDifference
      (graph t Ω (O i).records)).edgePolynomial (x i)) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i => RGraph.edgePolynomial_nonneg _ (hx i).1)
    (hT.mono fun i hi => mismatch_polynomial_le Ω (R i) (O i) (x i) (hx i) hi)
  simpa only [mul_zero] using hd.const_mul (OuterWeights.chi b t * (allPools Ω).card / 24)

theorem profile_repair_tendsto {I : Type*} {X : I → Type*}
    [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)] (l : Filter I)
    (Ω : Label → Finset (Cube.Word b)) (R : ∀ i, RecordSystem (X i))
    (O : ∀ i, LegalObject B (X i)) (x : ∀ i, Vertex b t (X i) → ℝ)
    (hx : ∀ i, ProbabilityWeights (x i))
    (hT : ∀ᶠ i in l, 0 < dataMass (x i))
    (hd : Tendsto (fun i => sampleProbability (normalizedData (x i)) ((R i).Disagreement (O i)))
      l (𝓝 0)) (W : SetFamily.Profile (t + (3 * b + 4)))
    (hW : Tendsto (fun i => SetFamily.weightedProfile (graph t Ω (R i)) (x i)) l (𝓝 W)) :
    Tendsto (fun i => SetFamily.weightedProfile (graph t Ω (O i).records) (x i)) l (𝓝 W) := by
  have hm := mismatch_tendsto l Ω R O x hx hT hd
  apply tendsto_pi_nhds.mpr
  intro A
  have hdiff := A.2.weightedHomDensity_sub_tendsto_zero_of_mismatch
    (fun i => graph t Ω (R i)) (fun i => graph t Ω (O i).records) x hx l hm
  have h := ((tendsto_pi_nhds.mp hW) A).sub hdiff
  simpa only [SetFamily.weightedProfile, sub_sub_cancel, sub_zero] using h

end TuranUniversality.Structural.Compiled
