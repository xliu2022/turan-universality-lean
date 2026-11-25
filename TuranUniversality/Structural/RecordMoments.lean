module

public import TuranUniversality.Structural.RecordRepair
public import TuranUniversality.Structural.RecordProjection

@[expose] public section

/-! # Exact finite moments for the four-sample score

Active positions are counted with multiplicity, including repeated samples.
All expectations below are finite sums with the actual real product weights.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem truth_and (p q : Prop) : truth (p ∧ q) = truth p * truth q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [truth, hp, hq]

theorem truth_le_one (p : Prop) : truth p ≤ 1 := by
  unfold truth
  split <;> norm_num

theorem weightedMean_scale {n : ℕ} (x : V → ℝ) (c : ℝ) (F : (Fin n → V) → ℝ) :
    weightedMean x (fun f => c * F f) = c * weightedMean x F := by
  simp only [weightedMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem weightedMean_sub {n : ℕ} (x : V → ℝ) (F G : (Fin n → V) → ℝ) :
    weightedMean x (fun f => F f - G f) = weightedMean x F - weightedMean x G := by
  simp [weightedMean, mul_sub, Finset.sum_sub_distrib]

theorem sum_neutral_weights (x : V → ℝ) (hx : ProbabilityWeights x) (A : Finset V) :
    (∑ v, x v * truth (v ∉ A)) = 1 - ∑ v ∈ A, x v := by
  classical
  have h : (∑ v, x v * truth (v ∈ A)) + (∑ v, x v * truth (v ∉ A)) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ v, x v := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ A <;> simp [truth, hv]
      _ = 1 := hx.2
  have ha : (∑ v, x v * truth (v ∈ A)) = ∑ v ∈ A, x v := by simp [truth]
  rw [ha] at h
  linarith

theorem sum_weighted_choice (x : V → ℝ) (hx : ProbabilityWeights x) (A : Finset V)
    (a b : ℝ) :
    (∑ v, x v * if v ∈ A then a else b) =
      (∑ v ∈ A, x v) * a + (1 - ∑ v ∈ A, x v) * b := by
  classical
  have hp (v : V) : x v * (if v ∈ A then a else b) =
      (x v * truth (v ∈ A)) * a + (x v * truth (v ∉ A)) * b := by
    by_cases h : v ∈ A <;> simp [truth, h]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_neutral_weights x hx A]
  simp [truth]

/-- Product-weight Fubini at any one coordinate. -/
theorem weightedMean_insertNth {n : ℕ} (x : V → ℝ) (i : Fin (n + 1))
    (F : (Fin (n + 1) → V) → ℝ) :
    weightedMean x F =
      weightedMean x (fun f : Fin n → V => ∑ v, x v * F (i.insertNth v f)) := by
  classical
  let e := Fin.insertNthEquiv (fun _ : Fin (n + 1) => V) i
  have hp (v : V) (f : Fin n → V) :
      productWeight x (i.insertNth v f) = x v * productWeight x f := by
    unfold productWeight
    rw [Fin.prod_univ_succAbove _ i]
    simp
  calc
    weightedMean x F = ∑ p : V × (Fin n → V),
        productWeight x (i.insertNth p.1 p.2) * F (i.insertNth p.1 p.2) :=
      (e.sum_comp (fun f => productWeight x f * F f)).symm
    _ = ∑ f : Fin n → V, ∑ v : V,
        (x v * productWeight x f) * F (i.insertNth v f) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [hp]
    _ = _ := by
      unfold weightedMean
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro v _
      ring

def activeCount {n : ℕ} (A : Finset V) (f : Fin n → V) : ℕ :=
  ∑ i, if f i ∈ A then 1 else 0

theorem activeCount_eq_card {n : ℕ} (A : Finset V) (f : Fin n → V) :
    activeCount A f = ((Finset.univ : Finset (Fin n)).filter (fun i => f i ∈ A)).card := by
  classical
  simp only [activeCount, Finset.sum_boole, Nat.cast_id]

@[simp] theorem activeCount_cons {n : ℕ} (A : Finset V) (v : V) (f : Fin n → V) :
    activeCount A (Fin.cons v f) = (if v ∈ A then 1 else 0) + activeCount A f := by
  simp only [activeCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

noncomputable def countProbability (x : V → ℝ) (A : Finset V) (n k : ℕ) : ℝ :=
  sampleProbability x (fun f : Fin n → V => activeCount A f = k)

theorem countProbability_zero (x : V → ℝ) (hx : ProbabilityWeights x)
    (A : Finset V) (k : ℕ) : countProbability x A 0 k = truth (0 = k) := by
  unfold countProbability sampleProbability
  have hp (f : Fin 0 → V) : activeCount A f = 0 := by simp [activeCount]
  simp_rw [hp]
  exact weightedMean_const x hx.2 _

theorem countProbability_succ_zero (x : V → ℝ) (hx : ProbabilityWeights x)
    (A : Finset V) (n : ℕ) :
    countProbability x A (n + 1) 0 = (1 - ∑ v ∈ A, x v) * countProbability x A n 0 := by
  classical
  unfold countProbability sampleProbability
  rw [weightedMean_succ]
  have hp (f : Fin n → V) :
      (∑ v, x v * truth (activeCount A (Fin.cons v f) = 0)) =
        (1 - ∑ v ∈ A, x v) * truth (activeCount A f = 0) := by
    calc
      _ = ∑ v, x v * if v ∈ A then 0 else truth (activeCount A f = 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v ∈ A <;> simp [h, activeCount_cons, truth]
      _ = _ := by rw [sum_weighted_choice x hx A]; ring
  simp_rw [hp]
  exact weightedMean_scale x _ _

theorem countProbability_succ_succ (x : V → ℝ) (hx : ProbabilityWeights x)
    (A : Finset V) (n k : ℕ) :
    countProbability x A (n + 1) (k + 1) =
      (∑ v ∈ A, x v) * countProbability x A n k +
        (1 - ∑ v ∈ A, x v) * countProbability x A n (k + 1) := by
  classical
  unfold countProbability sampleProbability
  rw [weightedMean_succ]
  have hp (f : Fin n → V) :
      (∑ v, x v * truth (activeCount A (Fin.cons v f) = k + 1)) =
        (∑ v ∈ A, x v) * truth (activeCount A f = k) +
          (1 - ∑ v ∈ A, x v) * truth (activeCount A f = k + 1) := by
    calc
      _ = ∑ v, x v * if v ∈ A then truth (activeCount A f = k)
            else truth (activeCount A f = k + 1) := by
        apply Finset.sum_congr rfl
        intro v _
        have hiff : 1 + activeCount A f = k + 1 ↔ activeCount A f = k := by omega
        by_cases h : v ∈ A <;> simp [h, activeCount_cons, truth, hiff]
      _ = _ := sum_weighted_choice x hx A _ _
  simp_rw [hp]
  rw [weightedMean_add, weightedMean_scale, weightedMean_scale]

theorem countProbability_four_three (x : V → ℝ) (hx : ProbabilityWeights x) (A : Finset V) :
    countProbability x A 4 3 = 4 * (∑ v ∈ A, x v) ^ 3 * (1 - ∑ v ∈ A, x v) := by
  norm_num [countProbability_succ_succ x hx A, countProbability_succ_zero x hx A,
    countProbability_zero x hx A, truth]
  ring

theorem countProbability_four_four (x : V → ℝ) (hx : ProbabilityWeights x) (A : Finset V) :
    countProbability x A 4 4 = (∑ v ∈ A, x v) ^ 4 := by
  norm_num [countProbability_succ_succ x hx A, countProbability_succ_zero x hx A,
    countProbability_zero x hx A, truth]
  ring

/-- The finite count identity used to locate the unique neutral position. -/
theorem activeCount_three_iff (A : Finset V) (f : Fin 4 → V) :
    activeCount A f = 3 ↔ ∃ i, f i ∉ A ∧ ∀ j, j ≠ i → f j ∈ A := by
  classical
  have hb : ∀ b : Fin 4 → Bool,
      (∑ i, if b i = true then (1 : ℕ) else 0) = 3 ↔
        ∃ i, b i ≠ true ∧ ∀ j, j ≠ i → b j = true := by decide
  simpa only [activeCount, ne_eq, decide_eq_true_eq] using hb (fun i => decide (f i ∈ A))

end TuranUniversality.Structural
