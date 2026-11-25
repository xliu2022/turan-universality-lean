module

public import TuranUniversality.Structural.OuterWeights

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Outer weight and erasure convergence from the actual defect inequality -/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.OuterWeights

theorem massVector_tendsto {I : Type*} {l : Filter I} {b t : ℕ}
    (y : I → Fin t → ℝ) (s : I → Fin b → ℝ) (T : I → ℝ)
    (hy : ∀ n j, 0 ≤ y n j) (hs : ∀ n i, 0 ≤ s n i) (hT : ∀ n, 0 ≤ T n)
    (htotal : ∀ n, (∑ j, y n j) + (∑ i, s n i) + T n = 1)
    (hK : Tendsto (fun n => massFactor (y n) (s n) (T n)) l (𝓝 (chi b t))) :
    Tendsto (fun n => massVector (y n) (s n) (T n)) l
      (𝓝 (fun _ : Slot b t => (arity b t : ℝ)⁻¹)) := by
  have hp : Tendsto (fun n => ∏ j, massVector (y n) (s n) (T n) j) l
      (𝓝 (((arity b t : ℝ)⁻¹) ^ arity b t)) := by
    have hd := hK.div_const (scale b)
    simpa only [massFactor_product, chi,
      mul_div_cancel_left₀ _ (ne_of_gt (scale_pos b))] using hd
  simpa only [slot_card] using probability_product_tendsto
    (fun n => massVector (y n) (s n) (T n))
    (fun n => massVector_probability (y n) (s n) (T n) (hy n) (hs n) (hT n) (htotal n))
    (by simpa only [slot_card] using hp)

/-- The exact mass limits asserted for the suspension roots, root blocks,
and all data vertices together. -/
theorem mass_limits {I : Type*} {l : Filter I} {b t : ℕ}
    (y : I → Fin t → ℝ) (s : I → Fin b → ℝ) (T : I → ℝ)
    (hy : ∀ n j, 0 ≤ y n j) (hs : ∀ n i, 0 ≤ s n i) (hT : ∀ n, 0 ≤ T n)
    (htotal : ∀ n, (∑ j, y n j) + (∑ i, s n i) + T n = 1)
    (hK : Tendsto (fun n => massFactor (y n) (s n) (T n)) l (𝓝 (chi b t))) :
    (∀ j, Tendsto (fun n => y n j) l (𝓝 (1 / (arity b t : ℝ)))) ∧
    (∀ i, Tendsto (fun n => s n i) l (𝓝 (3 / (arity b t : ℝ)))) ∧
      Tendsto T l (𝓝 (4 / (arity b t : ℝ))) := by
  have hv := massVector_tendsto y s T hy hs hT htotal hK
  have hc := tendsto_pi_nhds.mp hv
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa only [massVector, Sum.elim_inl, one_div] using hc (.inl j)
  · intro i
    have h := (hc (.inr (.inl ⟨i, 0⟩))).const_mul 3
    have he : (fun n => s n i) =
        (fun n => 3 * massVector (y n) (s n) (T n) (.inr (.inl ⟨i, 0⟩))) := by
      funext n
      dsimp [massVector]
      ring
    rw [he]
    simpa only [div_eq_mul_inv] using h
  · have h := (hc (.inr (.inr 0))).const_mul 4
    have he : T = (fun n => 4 * massVector (y n) (s n) (T n) (.inr (.inr 0))) := by
      funext n
      dsimp [massVector]
      ring
    rw [he]
    simpa only [div_eq_mul_inv] using h

/-- The two nonnegative losses in `defectglobal` separately vanish. -/
theorem factor_erasure_tendsto {I : Type*} {l : Filter I}
    (χ S a : ℝ) (hχ : 0 < χ) (hS : 0 < S) (ha : 0 < a)
    (K ε v : I → ℝ) (hK0 : ∀ i, 0 ≤ K i) (hKχ : ∀ i, K i ≤ χ)
    (hε : ∀ i, 0 ≤ ε i) (hv : ∀ i, v i ≤ K i * (S - a * ε i))
    (hlim : Tendsto v l (𝓝 (χ * S))) :
    Tendsto K l (𝓝 χ) ∧ Tendsto ε l (𝓝 0) := by
  have hvK (i : I) : v i ≤ K i * S := by
    have hp := mul_nonneg (hK0 i) (mul_nonneg ha.le (hε i))
    nlinarith [hv i]
  have hK : Tendsto K l (𝓝 χ) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun i => v i / S) (h := fun _ => χ)
    · simpa only [mul_div_cancel_right₀ _ (ne_of_gt hS)] using hlim.div_const S
    · exact tendsto_const_nhds
    · intro i
      exact (div_le_iff₀ hS).mpr (hvK i)
    · exact hKχ
  have hweighted : Tendsto (fun i => (a * K i) * ε i) l (𝓝 0) := by
    refine squeeze_zero (g := fun i => χ * S - v i)
      (fun i => mul_nonneg (mul_nonneg ha.le (hK0 i)) (hε i))
      (fun i => ?_) ?_
    · have hKS : K i * S ≤ χ * S := mul_le_mul_of_nonneg_right (hKχ i) hS.le
      nlinarith [hv i]
    · simpa using hlim.const_sub (χ * S)
  have hden := hK.const_mul a
  have hden0 : a * χ ≠ 0 := ne_of_gt (mul_pos ha hχ)
  have hdiv := hweighted.div hden hden0
  have heq : (fun i => (a * K i) * ε i / (a * K i)) =ᶠ[l] ε := by
    filter_upwards [hden.eventually_ne hden0] with i hi
    exact mul_div_cancel_left₀ _ hi
  refine ⟨hK, ?_⟩
  simpa only [zero_div] using hdiv.congr' heq

/-- Once the outer factor converges to its positive optimum, the actual
record scores must converge to their own optimum. -/
theorem score_tendsto {I : Type*} {l : Filter I} (χ S : ℝ) (hχ : 0 < χ)
    (K v ψ : I → ℝ) (hK : Tendsto K l (𝓝 χ))
    (hv : Tendsto v l (𝓝 (χ * S)))
    (hbound : ∀ i, v i ≤ K i * ψ i) (hψ : ∀ i, ψ i ≤ S) :
    Tendsto ψ l (𝓝 S) := by
  have hfloor : Tendsto (fun i => v i / K i) l (𝓝 S) := by
    have hh := hv.div hK (ne_of_gt hχ)
    change Tendsto (fun i => v i / K i) l (𝓝 ((χ * S) / χ)) at hh
    simpa only [mul_div_cancel_left₀ _ (ne_of_gt hχ)] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfloor tendsto_const_nhds
  · filter_upwards [hK.eventually (lt_mem_nhds hχ)] with i hi
    exact (div_le_iff₀ hi).mpr (by simpa only [mul_comm] using hbound i)
  · exact Eventually.of_forall hψ

end TuranUniversality.Structural.OuterWeights
