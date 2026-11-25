module

public import TuranUniversality.Structural.PhaseMixtureWeights
public import TuranUniversality.Structural.WeightedExpectations
public import TuranUniversality.Structural.ExtremalProfiles
public import TuranUniversality.Density.WeightedInducedPatterns

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The finite polynomial defining the phase map

Each coordinate is a finite sum over actual root/type assignments and
actual induced inner graphs. Compatibility is checked in a genuine finite
compiled graph. Inclusion-exclusion gives a finite linear combination of
inner homomorphism coordinates. The finite-model error is bounded by the
actual collision probabilities of the active and neutral samples.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.PhaseRoles

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

noncomputable def coordinate (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (H : RGraph U (t + (3 * b + 4))) (z : Role b t → ℝ) (W : RGraph U 3 → ℝ) : ℝ :=
  weightedMean z (fun θ => ∑ K : RGraph U 3,
    truth (Compatible Ω phase H θ K) * K.inducedPolynomial W)

theorem continuous_coordinate (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (H : RGraph U (t + (3 * b + 4))) :
    Continuous (fun p : (Role b t → ℝ) × (RGraph U 3 → ℝ) => coordinate Ω phase H p.1 p.2) := by
  unfold coordinate weightedMean productWeight RGraph.inducedPolynomial
  fun_prop

theorem coordinate_sample_formula (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (H : RGraph U (t + (3 * b + 4))) (O : LegalObject B V)
    (z : Role b t → ℝ) (a : O.active → ℝ) :
    coordinate Ω phase H z
        (fun K => K.weightedHomDensity ((O.inner phase).pullback (Function.Embedding.subtype _)) a) =
      weightedMean z (fun θ => weightedMean a (fun f =>
        truth (Compatible Ω phase H θ ((O.inner phase).inverseImage (fun u => (f u).val))))) := by
  unfold coordinate
  apply weightedMean_congr
  intro θ
  rw [← RGraph.weightedMean_inverseImage_polynomial]
  apply weightedMean_congr
  intro f
  rw [inverseImage_pullback]
  rfl

theorem coordinate_mixture_error (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (H : RGraph U (t + (3 * b + 4))) (O : LegalObject B V)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (z : Role b t → ℝ) (a : O.active → ℝ) (w : Neutral O → ℝ)
    (hz : ProbabilityWeights z) (ha : ProbabilityWeights a) (hw : ProbabilityWeights w) :
    |H.weightedHomDensity (Compiled.graph t Ω O.records) (mixtureWeight O z a w) -
      coordinate Ω phase H z
        (fun K => K.weightedHomDensity ((O.inner phase).pullback (Function.Embedding.subtype _)) a)| ≤
      (Fintype.card U : ℝ) ^ 2 * ((∑ v, (a v) ^ 2) + ∑ v, (w v) ^ 2) := by
  let P := Role b t × (O.active × Neutral O)
  let μ : P → ℝ := fun p => z p.1 * (a p.2.1 * w p.2.2)
  let A : (U → P) → ℝ := fun f =>
    H.homIndicator (Compiled.graph t Ω O.records) (sampleVertex O ∘ f)
  let C : (U → P) → ℝ := fun f =>
    truth (Compatible Ω phase H (fun u => (f u).1)
      ((O.inner phase).inverseImage (fun u => ((f u).2.1).val)))
  have hμ : ProbabilityWeights μ := probabilityWeights_product z _ hz
    (probabilityWeights_product a w ha hw)
  have hA : H.weightedHomDensity (Compiled.graph t Ω O.records) (mixtureWeight O z a w) =
      weightedMean μ A := (weightedMean_pushforward (sampleVertex O) μ _).symm
  have hC : coordinate Ω phase H z
      (fun K => K.weightedHomDensity ((O.inner phase).pullback (Function.Embedding.subtype _)) a) =
      weightedMean μ C := by
    rw [coordinate_sample_formula]
    unfold μ C
    rw [weightedMean_product_three z a w]
    simp only [weightedMean_const w hw.2]
  have he (f : U → P) : |A f - C f| ≤
      truth (¬ Function.Injective (fun u => (f u).2.1)) +
        truth (¬ Function.Injective (fun u => (f u).2.2)) := by
    have h := sampled_indicator_error O (fun u => (f u).1) phase hphase
      (fun u => (f u).2.1) (fun u => (f u).2.2) Ω H
    have hf : sampleVertex O ∘ f = sampleMap O (fun u => (f u).1)
        (fun u => (f u).2.1) (fun u => (f u).2.2) := by
      funext u
      exact sampleVertex_eq O (fun u => (f u).1) (fun u => (f u).2.1)
        (fun u => (f u).2.2) u
    simpa only [A, C, hf] using h
  rw [hA, hC]
  apply (weightedMean_abs_sub_le μ hμ.1 A C).trans
  calc
    _ ≤ weightedMean μ (fun f : U → P =>
        truth (¬ Function.Injective (fun u => (f u).2.1)) +
          truth (¬ Function.Injective (fun u => (f u).2.2))) := weightedMean_mono μ hμ.1 he
    _ = weightedMean a (fun f : U → O.active => truth (¬ Function.Injective f)) +
        weightedMean w (fun f : U → Neutral O => truth (¬ Function.Injective f)) := by
      unfold μ
      rw [weightedMean_product_three z a w]
      simp only [Density.weightedMean_add, weightedMean_const w hw.2,
        weightedMean_const a ha.2, weightedMean_const z hz.2]
    _ ≤ (Fintype.card U : ℝ) ^ 2 * ∑ v, (a v) ^ 2 +
        (Fintype.card U : ℝ) ^ 2 * ∑ v, (w v) ^ 2 :=
      add_le_add (weightedMean_collision_le a ha) (weightedMean_collision_le w hw)
    _ = _ := by ring

/-- The coordinate expansion applies to the actual original weighting. -/
theorem coordinate_error (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (H : RGraph U (t + (3 * b + 4))) (O : LegalObject B V)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (x : Compiled.Vertex b t V → ℝ) (hx : ProbabilityWeights x)
    (hA : 0 < roleWeight O x (.inr false)) (hW : 0 < roleWeight O x (.inr true)) :
    |H.weightedHomDensity (Compiled.graph t Ω O.records) x -
      coordinate Ω phase H (roleWeight O x)
        (fun K => K.weightedHomDensity ((O.inner phase).pullback (Function.Embedding.subtype _))
          (activeWeight O x))| ≤
      (Fintype.card U : ℝ) ^ 2 *
        ((∑ v, (activeWeight O x v) ^ 2) + ∑ v, (neutralWeight O x v) ^ 2) := by
  simpa only [mixtureWeight_eq O x hx.1 hA hW] using coordinate_mixture_error Ω phase H O hphase
    (roleWeight O x) (activeWeight O x) (neutralWeight O x)
    (roleWeight_probability O x hx) (activeWeight_probability O x hx.1 hA)
    (neutralWeight_probability O x hx.1 hW)

noncomputable def phaseMap (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (z : Role b t → ℝ) (W : SetFamily.Profile 3) : SetFamily.Profile (t + (3 * b + 4)) :=
  fun H => coordinate Ω phase H.2 z (fun K => W ⟨H.1, K⟩)

theorem continuous_phaseMap (Ω : Label → Finset (Cube.Word b)) (phase : Bool) :
    Continuous (fun p : (Role b t → ℝ) × SetFamily.Profile 3 => phaseMap Ω phase p.1 p.2) := by
  apply continuous_pi
  intro H
  unfold phaseMap coordinate weightedMean productWeight RGraph.inducedPolynomial
  fun_prop

end TuranUniversality.Structural.PhaseRoles
