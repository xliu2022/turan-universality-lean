module

public import TuranUniversality.Structural.Pentagon
public import TuranUniversality.Structural.CompactOptimization
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! # The simultaneous quantitative pentagon defect

The same permutation-invariant defect controls both code graphs.  Its
weighted Cauchy--Schwarz estimate is the exact finite inequality used in the
root-weight convergence claim.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.Pentagon

def defect (x : Fin 5 → ℝ) : ℝ := ∑ i, x i * (5 * x i - mass x) ^ 2

noncomputable def variance (x : Fin 5 → ℝ) : ℝ := ∑ i, (x i - mass x / 5) ^ 2

noncomputable def normalizedDefect (x : Fin 5 → ℝ) : ℝ := defect x / mass x ^ 3

theorem defect_nonneg {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ defect x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (sq_nonneg _))

theorem defect_doublePerm (x : Fin 5 → ℝ) : defect (x ∘ doublePerm) = defect x := by
  unfold defect
  rw [mass_doublePerm]
  exact doublePerm.sum_comp (fun i => x i * (5 * x i - mass x) ^ 2)

theorem P0_defect_le {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    defect x ≤ 400 * (mass x ^ 3 / 25 - P0.edgePolynomial x) := by
  rw [squares_identity]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hx i)
  have h1 := sq_nonneg (x (i + 1) + x (i - 1) - x (i + 2) - x (i - 2))
  have h2 := sq_nonneg (x (i + 1) - x (i - 1) - x (i + 2) + x (i - 2))
  linarith

theorem defect_le (phase : Bool) {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    defect x ≤ 400 * (mass x ^ 3 / 25 - (graph phase).edgePolynomial x) := by
  cases phase
  · exact P0_defect_le hx
  · change defect x ≤ 400 * (mass x ^ 3 / 25 - P1.edgePolynomial x)
    rw [P1_polynomial_doublePerm, ← mass_doublePerm x, ← defect_doublePerm x]
    exact P0_defect_le (fun i => hx (doublePerm i))

theorem polynomial_le_defect (phase : Bool) {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (graph phase).edgePolynomial x ≤ mass x ^ 3 / 25 - defect x / 400 := by
  linarith [defect_le phase hx]

theorem weighted_deviation_identity (x : Fin 5 → ℝ) :
    (∑ i, x i * (5 * x i - mass x)) = 5 * variance x := by
  simp only [variance, mass, Fin.sum_univ_succ]
  ring

/-- Weighted Cauchy--Schwarz, before normalizing the total block mass. -/
theorem variance_sq_le {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    25 * variance x ^ 2 ≤ mass x * defect x := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i : Fin 5 => x i * (5 * x i - mass x))
    (f := x) (g := fun i => x i * (5 * x i - mass x) ^ 2)
    (fun i _ => hx i) (fun i _ => mul_nonneg (hx i) (sq_nonneg _))
    (fun i _ => by ring_nf; rfl)
  rw [weighted_deviation_identity] at h
  change (5 * variance x) ^ 2 ≤ mass x * defect x at h
  nlinarith only [h]

theorem defect_eq_zero_iff {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    defect x = 0 ↔ ∀ i, x i = mass x / 5 := by
  constructor
  · intro hd
    have hv := variance_sq_le hx
    rw [hd, mul_zero] at hv
    have hv0 : variance x = 0 := by nlinarith [sq_nonneg (variance x)]
    have hs (i : Fin 5) : (x i - mass x / 5) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - mass x / 5))).mp
        hv0 i (Finset.mem_univ i)
    intro i
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hs i))
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    have hi : 5 * x i - mass x = 0 := by rw [h i]; ring
    simp [hi]

theorem normalizedDefect_nonneg {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ normalizedDefect x := by
  apply div_nonneg (defect_nonneg hx)
  exact pow_nonneg (Finset.sum_nonneg fun i _ => hx i) 3

theorem polynomial_le_normalizedDefect (phase : Bool) {x : Fin 5 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : 0 < mass x) :
    (graph phase).edgePolynomial x ≤ (mass x ^ 3 / 25) * (1 - normalizedDefect x / 16) := by
  have he : (mass x ^ 3 / 25) * (1 - normalizedDefect x / 16) =
      mass x ^ 3 / 25 - defect x / 400 := by
    unfold normalizedDefect
    field_simp [ne_of_gt hs]
    <;> ring
  rw [he]
  exact polynomial_le_defect phase hx

theorem normalizedDefect_le_sixteen {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    normalizedDefect x ≤ 16 := by
  by_cases hm : mass x = 0
  · simp [normalizedDefect, hm]
  · have hs : 0 < mass x := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => hx i) (Ne.symm hm)
    have hd := defect_le false hx
    have hp := (graph false).edgePolynomial_nonneg hx
    apply (div_le_iff₀ (pow_pos hs 3)).mpr
    linarith

theorem normalized_factor_nonneg {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ 1 - normalizedDefect x / 16 := by linarith [normalizedDefect_le_sixteen hx]

theorem mass_scale (x : Fin 5 → ℝ) (c : ℝ) : mass (fun i => c * x i) = c * mass x := by
  simp only [mass, Finset.mul_sum]

theorem defect_scale (x : Fin 5 → ℝ) (c : ℝ) :
    defect (fun i => c * x i) = c ^ 3 * defect x := by
  rw [defect, mass_scale]
  unfold defect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def normalizedWeights (x : Fin 5 → ℝ) : Fin 5 → ℝ :=
  if mass x = 0 then fun _ => 1 / 5 else fun i => x i / mass x

theorem normalizedWeights_probability {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ProbabilityWeights (normalizedWeights x) := by
  by_cases hm : mass x = 0
  · simp [normalizedWeights, hm, ProbabilityWeights]
  · have hs : 0 ≤ mass x := Finset.sum_nonneg fun i _ => hx i
    refine ⟨?_, ?_⟩
    · intro i
      simp only [normalizedWeights, hm, ite_false]
      exact div_nonneg (hx i) hs
    · simp only [normalizedWeights, hm, ite_false, ← Finset.sum_div]
      exact div_self hm

theorem defect_normalizedWeights {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    defect (normalizedWeights x) = normalizedDefect x := by
  by_cases hm : mass x = 0
  · simp only [normalizedWeights, hm, ite_true, normalizedDefect,
      zero_pow (by decide : 3 ≠ 0), div_zero]
    norm_num [defect, mass]
  · have he : normalizedWeights x = fun i => (mass x)⁻¹ * x i := by
      ext i
      simp [normalizedWeights, hm, div_eq_mul_inv, mul_comm]
    rw [he, defect_scale]
    simp only [normalizedDefect, div_eq_mul_inv, inv_pow]
    ring

theorem mass_mul_normalizedWeights {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) (i : Fin 5) :
    mass x * normalizedWeights x i = x i := by
  by_cases hm : mass x = 0
  · have hle : x i ≤ mass x := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
    have hi : x i = 0 := le_antisymm (by simpa [hm] using hle) (hx i)
    simp [hm, hi]
  · simp [normalizedWeights, hm, mul_div_cancel₀]

theorem probability_defect_tendsto {I : Type*} {l : Filter I}
    (x : I → Fin 5 → ℝ) (hx : ∀ n, ProbabilityWeights (x n))
    (hd : Tendsto (fun n => defect (x n)) l (𝓝 0)) :
    Tendsto x l (𝓝 (fun _ : Fin 5 => (1 / 5 : ℝ))) := by
  apply tendsto_of_unique_value_on_compact (isCompact_stdSimplex ℝ (Fin 5))
    defect (by unfold defect mass; fun_prop) (fun _ => (1 / 5 : ℝ)) 0 ?_ x
    (Eventually.of_forall hx) hd
  intro y hy he
  have h := (defect_eq_zero_iff hy.1).mp he
  funext i
  simpa only [mass, hy.2] using h i

theorem weights_tendsto_of_normalizedDefect {I : Type*} {l : Filter I}
    (x : I → Fin 5 → ℝ) (hx : ∀ n i, 0 ≤ x n i) (s : ℝ)
    (hs : Tendsto (fun n => mass (x n)) l (𝓝 s))
    (hd : Tendsto (fun n => normalizedDefect (x n)) l (𝓝 0)) :
    Tendsto x l (𝓝 (fun _ : Fin 5 => s / 5)) := by
  have hp : Tendsto (fun n => normalizedWeights (x n)) l (𝓝 (fun _ : Fin 5 => (1 / 5 : ℝ))) :=
    probability_defect_tendsto _ (fun n => normalizedWeights_probability (hx n))
      (by simpa only [defect_normalizedWeights (hx _)] using hd)
  apply tendsto_pi_nhds.mpr
  intro i
  have h := hs.mul (tendsto_pi_nhds.mp hp i)
  simpa only [mass_mul_normalizedWeights (hx _), mul_one_div] using h

end TuranUniversality.Structural.Pentagon
