module

public import TuranUniversality.Structural.PhaseSamples
public import TuranUniversality.Structural.SamplingProducts

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact root/active/neutral mixture sampling -/

open scoped BigOperators

namespace TuranUniversality.Structural.PhaseRoles

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

def sampleVertex (O : LegalObject B V) : Role b t × (O.active × Neutral O) →
    Compiled.Vertex b t V
  | (.inl j, _) => rootVertex j
  | (.inr false, a, _) => .inr (.inr a.val)
  | (.inr true, _, w) => .inr (.inr w.val)

theorem sampleVertex_eq (O : LegalObject B V) (θ : U → Role b t)
    (a : U → O.active) (w : U → Neutral O) (u : U) :
    sampleVertex O (θ u, (a u, w u)) = sampleMap O θ a w u := by
  unfold sampleMap
  simp only [Function.comp_apply, place]
  split
  · rename_i j h
    cases j <;> simp [sampleVertex, h, rootVertex, Compiled.mapData]
  · rename_i c h
    cases c <;> simp [sampleVertex, h, Compiled.mapData, dataMap]

noncomputable def mixtureWeight (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ) : Compiled.Vertex b t V → ℝ :=
  pushforwardWeight (sampleVertex O) (fun p => z p.1 * (a p.2.1 * w p.2.2))

theorem mixtureWeight_probability (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ)
    (hz : ProbabilityWeights z) (ha : ProbabilityWeights a) (hw : ProbabilityWeights w) :
    ProbabilityWeights (mixtureWeight O z a w) :=
  pushforwardWeight_probability _ _
    (probabilityWeights_product z _ hz (probabilityWeights_product a w ha hw))

theorem weightedHomDensity_mixture (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    H.weightedHomDensity (Compiled.graph t Ω O.records) (mixtureWeight O z a w) =
      weightedMean z (fun θ => weightedMean a (fun f => weightedMean w
        (fun g => H.homIndicator (Compiled.graph t Ω O.records) (sampleMap O θ f g)))) := by
  unfold RGraph.weightedHomDensity mixtureWeight
  rw [← weightedMean_pushforward, weightedMean_product_three z a w]
  apply weightedMean_congr
  intro θ
  apply weightedMean_congr
  intro f
  apply weightedMean_congr
  intro g
  congr 1
  funext u
  exact sampleVertex_eq O θ f g u

theorem inverseImage_pullback (G : RGraph V 3) {W : Type*} [Fintype W] [DecidableEq W]
    (i : W ↪ V) (f : U → W) :
    (G.pullback i).inverseImage f = G.inverseImage (i ∘ f) := by
  apply RGraph.ext
  ext e
  rw [RGraph.mem_inverseImage, RGraph.mem_inverseImage, RGraph.mem_pullback]
  have him : (e.image f).map i = e.image (i ∘ f) := by
    simp only [Finset.map_eq_image, Finset.image_image]
  rw [him]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨he, hG⟩
    refine ⟨he, ?_, hG⟩
    have hc := G.uniform _ hG
    rw [← him, Finset.card_map] at hc
    exact hc

end TuranUniversality.Structural.PhaseRoles
