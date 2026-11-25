module

public import TuranUniversality.Density.EditDistance
public import TuranUniversality.Density.WeightedHomPushforward

@[expose] public section

/-! # Exact edge-edit pullback under an arbitrary vertex map -/

namespace TuranUniversality.RGraph

open Density

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable [Fintype V] [Fintype W] {r : ℕ}

theorem edgeSymmDifference_inverseImage (G H : RGraph W r) (f : V → W) :
    (G.inverseImage f).edgeSymmDifference (H.inverseImage f) =
      (G.edgeSymmDifference H).inverseImage f := by
  ext e
  simp only [edgeSymmDifference, Finset.mem_symmDiff, mem_inverseImage]
  tauto

theorem normalizedEditDistance_inverseImage (G H : RGraph W r) (f : V → W) :
    (G.inverseImage f).normalizedEditDistance (H.inverseImage f) =
      (G.edgeSymmDifference H).edgePolynomial
        (pushforwardWeight f (fun _ : V => (Fintype.card V : ℝ)⁻¹)) := by
  rw [normalizedEditDistance_eq_polynomial, edgeSymmDifference_inverseImage,
    edgePolynomial_inverseImage]

end TuranUniversality.RGraph
