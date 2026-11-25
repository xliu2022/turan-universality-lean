module

public import TuranUniversality.Structural.BlockDefects
public import TuranUniversality.Structural.OuterConvergence
public import TuranUniversality.Structural.RecordCollisions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Near-optimal actual compiled graphs have the prescribed root limits

Both the carrier and the record system may vary. The hypotheses contain
only actual local legality, probability weights and convergence of the edge
polynomial; all factor, erasure and individual-root conclusions are proved.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.Compiled

variable {I : Type*} {l : Filter I} {b t : ℕ}
variable (V : I → Type*) [∀ n, DecidableEq (V n)] [∀ n, Fintype (V n)]
variable (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
variable (Ω : Label → Finset (Cube.Word b)) (R : ∀ n, RecordSystem (V n))
variable (hlocal : ∀ n, (R n).LocallyLegal (homomorphicClosure F))
variable (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
variable (hz : p / q ≤ familyTuranDensity F)
variable (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
variable (x : ∀ n, Vertex b t (V n) → ℝ) (hx : ∀ n, ProbabilityWeights (x n))
variable (hlim : Tendsto (fun n => (graph t Ω (R n)).edgePolynomial (x n)) l
  (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))))

include hedges hlocal hp hpq hq hz hΩ hx hlim

theorem near_optimal_factor_erasure :
    Tendsto (fun n => factor (x n)) l (𝓝 (OuterWeights.chi b t)) ∧
      Tendsto (fun n => (R n).erasure (normalizedData (x n))) l (𝓝 0) := by
  exact OuterWeights.factor_erasure_tendsto (OuterWeights.chi b t)
    (SwitchScalar.phaseScore p q (familyTuranDensity F)) (160 * q / 48)
    (OuterWeights.chi_pos b t) (SwitchScalar.phaseScore_pos p q _ hq hz) (by positivity)
    (fun n => factor (x n)) (fun n => (R n).erasure (normalizedData (x n)))
    (fun n => (graph t Ω (R n)).edgePolynomial (x n))
    (fun n => factor_nonneg (x n) (hx n).1) (fun n => factor_le (x n) (hx n))
    (fun n => normalized_erasure_nonneg (R n) (x n) (hx n).1)
    (fun n => defect_global_all F hedges Ω (R n) (hlocal n) p q hp hpq hq hz hΩ (x n) (hx n))
    hlim

theorem near_optimal_mass_limits :
    (∀ j, Tendsto (fun n => suspensionWeight (x n) j) l (𝓝 (1 / (OuterWeights.arity b t : ℝ)))) ∧
    (∀ i, Tendsto (fun n => blockMass (x n) i) l (𝓝 (3 / (OuterWeights.arity b t : ℝ)))) ∧
      Tendsto (fun n => dataMass (x n)) l (𝓝 (4 / (OuterWeights.arity b t : ℝ))) := by
  have hK := (near_optimal_factor_erasure V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).1
  exact OuterWeights.mass_limits (fun n => suspensionWeight (x n))
    (fun n => blockMass (x n)) (fun n => dataMass (x n)) (fun n j => (hx n).1 _)
    (fun n i => blockMass_nonneg (x n) (hx n).1 i)
    (fun n => dataMass_nonneg (x n) (hx n).1) (fun n => mass_sum (x n) (hx n)) hK

theorem near_optimal_blockDefect (i : Fin b) :
    Tendsto (fun n => Pentagon.normalizedDefect (fun j => rootWeight (x n) ⟨i, j⟩))
      l (𝓝 0) := by
  let Λ := OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)
  have hΛ : 0 < Λ := mul_pos (OuterWeights.chi_pos b t)
    (SwitchScalar.phaseScore_pos p q _ hq hz)
  have hbound (n : I) : Pentagon.normalizedDefect (fun j => rootWeight (x n) ⟨i, j⟩) ≤
      16 * (Λ - (graph t Ω (R n)).edgePolynomial (x n)) / Λ := by
    apply (le_div_iff₀ hΛ).mpr
    have h := polynomial_le_defect_upper F hedges Ω (R n) (hlocal n)
      p q hp hpq hq hz hΩ (x n) (hx n) i
    change (graph t Ω (R n)).edgePolynomial (x n) ≤
      (1 - Pentagon.normalizedDefect (fun j => rootWeight (x n) ⟨i, j⟩) / 16) * Λ at h
    nlinarith only [h]
  apply squeeze_zero
    (fun n => Pentagon.normalizedDefect_nonneg (fun j => (hx n).1 _)) hbound
  simpa [Λ] using ((hlim.const_sub Λ).const_mul 16).div_const Λ

/-- The root coordinates, including all five vertices of every block,
have exactly the limits stated in the structural classification. -/
theorem near_optimal_root_limits :
    (∀ j, Tendsto (fun n => suspensionWeight (x n) j) l (𝓝 (1 / (OuterWeights.arity b t : ℝ)))) ∧
    (∀ i j, Tendsto (fun n => rootWeight (x n) ⟨i, j⟩) l
      (𝓝 (3 / (5 * (OuterWeights.arity b t : ℝ))))) ∧
      Tendsto (fun n => dataMass (x n)) l (𝓝 (4 / (OuterWeights.arity b t : ℝ))) := by
  have hm := near_optimal_mass_limits V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim
  refine ⟨hm.1, ?_, hm.2.2⟩
  intro i j
  have hd := near_optimal_blockDefect V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim i
  have hw := Pentagon.weights_tendsto_of_normalizedDefect
    (fun n j => rootWeight (x n) ⟨i, j⟩) (fun n j => (hx n).1 _)
    (3 / (OuterWeights.arity b t : ℝ)) (hm.2.1 i) hd
  have he : (3 / (OuterWeights.arity b t : ℝ)) / 5 =
      3 / (5 * (OuterWeights.arity b t : ℝ)) := by ring
  simpa only [he] using tendsto_pi_nhds.mp hw j

theorem near_optimal_score :
    Tendsto (fun n => (R n).score p q (normalizedData (x n))) l
      (𝓝 (SwitchScalar.phaseScore p q (familyTuranDensity F))) := by
  exact OuterWeights.score_tendsto (OuterWeights.chi b t)
    (SwitchScalar.phaseScore p q (familyTuranDensity F)) (OuterWeights.chi_pos b t)
    (fun n => factor (x n)) (fun n => (graph t Ω (R n)).edgePolynomial (x n))
    (fun n => (R n).score p q (normalizedData (x n)))
    (near_optimal_factor_erasure V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).1 hlim
    (fun n => polynomial_le_factor_score_all Ω (R n) p q hΩ (x n) (hx n).1)
    (fun n => normalized_score_le F hedges (R n) (hlocal n) p q hp hpq hq hz (x n) (hx n).1)

theorem eventually_positive_dataMass : ∀ᶠ n in l, 0 < dataMass (x n) := by
  have hT := (near_optimal_mass_limits V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).2.2
  have hpos : 0 < 4 / (OuterWeights.arity b t : ℝ) :=
    div_pos (by norm_num) (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  exact hT.eventually (lt_mem_nhds hpos)

theorem normalized_squares_tendsto :
    Tendsto (fun n => ∑ v : V n, (normalizedData (x n) v) ^ 2) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  · filter_upwards [eventually_positive_dataMass V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim]
      with n hn
    exact (R n).squares_le_erasure _ (normalizedData_probability (x n) (hx n).1 hn)
  · exact (near_optimal_factor_erasure V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).2

theorem data_squares_tendsto :
    Tendsto (fun n => ∑ v : V n, (dataWeight (x n) v) ^ 2) l (𝓝 0) := by
  have hT := (near_optimal_mass_limits V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim).2.2
  have hN := normalized_squares_tendsto V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim
  have hprod : Tendsto (fun n => dataMass (x n) ^ 2 *
      (∑ v : V n, (normalizedData (x n) v) ^ 2)) l (𝓝 0) := by
    simpa using (hT.pow 2).mul hN
  apply hprod.congr'
  filter_upwards [eventually_positive_dataMass V F hedges Ω R hlocal p q hp hpq hq hz hΩ x hx hlim]
    with n hn
  simp only [normalizedData, div_pow, ← Finset.sum_div]
  field_simp [ne_of_gt hn]

end TuranUniversality.Structural.Compiled
