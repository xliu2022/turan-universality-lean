module

public import TuranUniversality.Uniformity.DensityScaling
public import TuranUniversality.Uniformity.Thresholds

@[expose] public section

/-! # The mathematical finite families and fixed optimal templates

The three-uniform branch is exactly the singleton from Theorem 1.1. Higher
uniformities use the concrete bounded suspension basis and its full extension
family. The fixed template is independent of the machine input.
-/

open Filter Topology

namespace TuranUniversality.Uniformity

open TuranUniversality.Computation TuranUniversality.Effective

noncomputable section

set_option maxRecDepth 8000

attribute [local irreducible] forbiddenCompiler tau3

private theorem decoded_nonempty (g : GraphCode) (h : (decodeGraph g).edges.Nonempty) :
    (decodeGraphCode g).2.edges.Nonempty := h

private theorem singleton_code_density (g : GraphCode) :
    familyTuranDensity {decodeGraphCode g} = turanDensity (decodeGraph g) :=
  familyTuranDensity_singleton (decodeGraphCode g)

private theorem lifted_code_density (g : GraphCode) (r : ℕ) (hr : 3 ≤ r)
    (h : (decodeGraph g).edges.Nonempty) :
    familyTuranDensity (family (decodeGraphCode g) r) =
      (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) * turanDensity (decodeGraph g) :=
  family_density_eq (decodeGraphCode g) r hr (decoded_nonempty g h)

/-- The actual finite forbidden family. The higher-uniformity branch is
defined at all other natural numbers, while the theorem concerns `r ≥ 3`. -/
def numericalFamily (r : ℕ) (w : BinaryWord) : Finset (FiniteGraph r) :=
  if h : r = 3 then
    h.symm ▸ ({decodeGraphCode (forbiddenCompiler w)} : Finset (FiniteGraph 3))
  else family (decodeGraphCode (forbiddenCompiler w)) r

@[simp] theorem numericalFamily_three (w : BinaryWord) :
    numericalFamily 3 w = {decodeGraphCode (forbiddenCompiler w)} := by
  simp [numericalFamily]

theorem numericalFamily_of_ne_three (r : ℕ) (w : BinaryWord) (h : r ≠ 3) :
    numericalFamily r w = family (decodeGraphCode (forbiddenCompiler w)) r := by
  simp [numericalFamily, h]

theorem numericalFamily_has_edges (r : ℕ) (w : BinaryWord)
    {A : FiniteGraph r} (hA : A ∈ numericalFamily r w) : A.2.edges.Nonempty := by
  by_cases hr : r = 3
  · subst r
    rw [numericalFamily_three] at hA
    obtain rfl := Finset.mem_singleton.mp hA
    exact decoded_nonempty (forbiddenCompiler w) (forbiddenCompiler_has_edges w)
  · rw [numericalFamily_of_ne_three r w hr] at hA
    exact family_has_edges _ _ hA

theorem numericalFamily_density_limit (r : ℕ) (w : BinaryWord) :
    Tendsto (familyExtremalDensity (numericalFamily r w)) atTop
      (𝓝 (familyTuranDensity (numericalFamily r w))) :=
  familyExtremalDensity_tendsto _ (fun _ h => numericalFamily_has_edges r w h)

/-- The exact ordinary-density formula, retaining the original singleton at 3. -/
theorem numericalFamily_density_scaling (r : ℕ) (hr : 3 ≤ r) (w : BinaryWord) :
    familyTuranDensity (numericalFamily r w) =
      (densityScale r : ℝ) * turanDensity (decodeGraph (forbiddenCompiler w)) := by
  by_cases h3 : r = 3
  · subst r
    rw [numericalFamily_three, singleton_code_density, densityScale_three]
    simp only [Rat.cast_one, one_mul]
  · rw [numericalFamily_of_ne_three r w h3, densityScale_cast]
    exact lifted_code_density (forbiddenCompiler w) r hr (forbiddenCompiler_has_edges w)

theorem numericalFamily_density_scaling_formula (r : ℕ) (hr : 3 ≤ r) (w : BinaryWord) :
    familyTuranDensity (numericalFamily r w) =
      (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) *
        turanDensity (decodeGraph (forbiddenCompiler w)) := by
  rw [numericalFamily_density_scaling r hr w, densityScale_cast]

theorem numericalFamily_density_eq_iff (r : ℕ) (hr : 3 ≤ r) (w : BinaryWord) :
    familyTuranDensity (numericalFamily r w) = (thresholdR r : ℝ) ↔ ¬ WordHalts w := by
  have hc : (densityScale r : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast densityScale_pos (show 0 < r by omega)
  rw [numericalFamily_density_scaling r hr w]
  have ht : (thresholdR r : ℝ) = (densityScale r : ℝ) * (tau3 : ℝ) := by
    simp only [thresholdR, Rat.cast_mul]
  rw [ht, mul_right_inj' hc]
  exact forbiddenCompiler_density_eq_iff w

theorem numericalFamily_density_strict_iff (r : ℕ) (hr : 3 ≤ r) (w : BinaryWord) :
    (thresholdR r : ℝ) < familyTuranDensity (numericalFamily r w) ↔ WordHalts w := by
  have hc : (0 : ℝ) < densityScale r := by
    exact_mod_cast densityScale_pos (show 0 < r by omega)
  rw [numericalFamily_density_scaling r hr w]
  have ht : (thresholdR r : ℝ) = (densityScale r : ℝ) * (tau3 : ℝ) := by
    simp only [thresholdR, Rat.cast_mul]
  rw [ht, mul_lt_mul_iff_right₀ hc]
  exact forbiddenCompiler_density_strict_iff w

end
end TuranUniversality.Uniformity
