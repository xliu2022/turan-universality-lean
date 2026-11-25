module

public import TuranUniversality.Structural.RecordMoments

@[expose] public section

/-! # Collisions in genuine independent four-samples

The exact pair-collision probability is the sum of squared vertex weights.
The six unordered pairs give the collision upper bound, while any erased
record system contains the first-pair collision event.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem pair_collision_probability (x : V → ℝ) (hx : ProbabilityWeights x)
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    sampleProbability x (fun f : Fin n → V => f i = f j) = ∑ v, (x v) ^ 2 := by
  classical
  let a : Fin 2 → Fin n := ![i, j]
  have ha : Function.Injective a := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all [a, eq_comm]
  have h := weightedMean_restrict_injective x hx.2 a ha
    (fun f : Fin 2 → V => truth (f 0 = f 1))
  calc
    sampleProbability x (fun f : Fin n → V => f i = f j) =
        weightedMean x (fun f : Fin 2 → V => truth (f 0 = f 1)) := by
      simpa only [sampleProbability, Function.comp_apply, a, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] using h
    _ = _ := by
      rw [weightedMean_succ]
      change weightedMean x (fun f : Fin 1 → V => ∑ v, x v * truth (v = f 0)) = _
      simp only [truth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [weightedMean_one]
      simp only [sq]

theorem collision_indicator_le (f : Fin 4 → V) :
    truth (¬ Function.Injective f) ≤
      truth (f 0 = f 1) + truth (f 0 = f 2) + truth (f 0 = f 3) +
        truth (f 1 = f 2) + truth (f 1 = f 3) + truth (f 2 = f 3) := by
  classical
  have h01 := truth_nonneg (f 0 = f 1)
  have h02 := truth_nonneg (f 0 = f 2)
  have h03 := truth_nonneg (f 0 = f 3)
  have h12 := truth_nonneg (f 1 = f 2)
  have h13 := truth_nonneg (f 1 = f 3)
  have h23 := truth_nonneg (f 2 = f 3)
  have ht := truth_le_one (¬ Function.Injective f)
  by_cases hi : Function.Injective f
  · simp only [hi, not_true_eq_false, truth_false]
    positivity
  · have hc : f 0 = f 1 ∨ f 0 = f 2 ∨ f 0 = f 3 ∨
        f 1 = f 2 ∨ f 1 = f 3 ∨ f 2 = f 3 := by
      by_contra hn
      push Not at hn
      apply hi
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    rcases hc with h | h | h | h | h | h
    all_goals
      have he : truth _ = 1 :=
        (congrArg truth (propext (iff_true_intro h))).trans truth_true
      linarith

/-- The sharp union-bound coefficient for four positions is six. -/
theorem collision_probability_le (x : V → ℝ) (hx : ProbabilityWeights x) :
    sampleProbability x (fun f : Fin 4 → V => ¬ Function.Injective f) ≤
      6 * ∑ v, (x v) ^ 2 := by
  have h := weightedMean_mono x hx.1 (fun f : Fin 4 → V => collision_indicator_le f)
  simp only [weightedMean_add] at h
  change sampleProbability x (fun f : Fin 4 → V => ¬ Function.Injective f) ≤
    sampleProbability x (fun f : Fin 4 → V => f 0 = f 1) +
      sampleProbability x (fun f : Fin 4 → V => f 0 = f 2) +
      sampleProbability x (fun f : Fin 4 → V => f 0 = f 3) +
      sampleProbability x (fun f : Fin 4 → V => f 1 = f 2) +
      sampleProbability x (fun f : Fin 4 → V => f 1 = f 3) +
      sampleProbability x (fun f : Fin 4 → V => f 2 = f 3) at h
  rw [pair_collision_probability x hx 0 1 (by decide),
    pair_collision_probability x hx 0 2 (by decide),
    pair_collision_probability x hx 0 3 (by decide),
    pair_collision_probability x hx 1 2 (by decide),
    pair_collision_probability x hx 1 3 (by decide),
    pair_collision_probability x hx 2 3 (by decide)] at h
  linarith

namespace RecordSystem

theorem squares_le_erasure (R : RecordSystem V) (x : V → ℝ)
    (hx : ProbabilityWeights x) : (∑ v, (x v) ^ 2) ≤ R.erasure x := by
  rw [← pair_collision_probability x hx (0 : Fin 4) 1 (by decide),
    ← R.erasure_probability x hx]
  apply weightedMean_mono x hx.1
  intro f
  by_cases h : f 0 = f 1
  · have hn : ¬ R.Successful f := fun hs => (by decide : (0 : Fin 4) ≠ 1) (hs.injective h)
    simp [truth, h, hn]
  · simp only [h, truth_false]
    exact truth_nonneg _

end RecordSystem
end TuranUniversality.Structural
