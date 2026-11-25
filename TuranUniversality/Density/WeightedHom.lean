module

public import TuranUniversality.Density.WeightedSampling

@[expose] public section

/-! # Actual homomorphism densities with arbitrary real vertex weights

The definition is the independent vertex-sampling sum with the ordinary
homomorphism indicator. Probability normalization is imposed only in the
lemmas that need it. Thus the same definition supports exact polynomial
factorizations and homogeneity before normalization.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density Selector

universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable [Fintype U] [Fintype V] {r : ℕ}

noncomputable def weightedHomDensity (F : RGraph U r) (G : RGraph V r) (x : V → ℝ) : ℝ :=
  weightedMean x (F.homIndicator G)

theorem weightedHomDensity_eq_sum_homs (F : RGraph U r) (G : RGraph V r) (x : V → ℝ) :
    F.weightedHomDensity G x = ∑ f : {f : U → V // F.IsHom G f}, productWeight x f.val := by
  classical
  unfold weightedHomDensity weightedMean homIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_subtype _
    (p := fun f : U → V => F.IsHom G f)
    (by intro f; simp only [Finset.mem_filter, Finset.mem_univ, true_and])]

theorem weightedHomDensity_nonneg (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) : 0 ≤ F.weightedHomDensity G x := by
  rw [weightedHomDensity_eq_sum_homs]
  exact Finset.sum_nonneg (fun f _ => Finset.prod_nonneg fun u _ => hx (f.val u))

theorem weightedHomDensity_le_one (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (hx : ProbabilityWeights x) : F.weightedHomDensity G x ≤ 1 := by
  calc
    _ ≤ weightedMean x (fun _ : U → V => (1 : ℝ)) :=
      weightedMean_mono x hx.1 (F.homIndicator_le_one G)
    _ = 1 := weightedMean_const x hx.2 1

theorem weightedHomDensity_scale (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (c : ℝ) :
    F.weightedHomDensity G (fun v => c * x v) =
      c ^ Fintype.card U * F.weightedHomDensity G x := by
  unfold weightedHomDensity weightedMean productWeight
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem weightedHomDensity_oneEdge (G : RGraph V r) (x : V → ℝ) :
    (oneEdge r).weightedHomDensity G x = (r.factorial : ℝ) * G.edgePolynomial x :=
  weightedMean_oneEdge G x

theorem weightedHomDensity_uniform (F : RGraph U r) (G : RGraph V r) :
    F.weightedHomDensity G (fun _ => (Fintype.card V : ℝ)⁻¹) = F.homDensity G := by
  rw [homDensity, mean_eq_sum_div_card]
  unfold weightedHomDensity weightedMean productWeight
  simp [Finset.prod_const, Fintype.card_fun, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem weightedHomDensity_eq_zero_of_homFree (F : RGraph U r) (G : RGraph V r)
    (h : F.HomFree G) (x : V → ℝ) : F.weightedHomDensity G x = 0 := by
  unfold weightedHomDensity weightedMean
  apply Finset.sum_eq_zero
  intro f _
  rw [homIndicator_of_not_hom F G (fun hf => h ⟨f, hf⟩), mul_zero]

end TuranUniversality.RGraph
