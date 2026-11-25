module

public import TuranUniversality.Hypergraph.PartitionRounding
public import TuranUniversality.Hypergraph.Polynomial
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Integer class sizes with exact total order

Formalization author: Xizhi Liu.
Maintainer: Xizhi Liu.

Taking floors and allocating the remaining vertices to one fixed class gives
integer class sizes summing to the prescribed graph order. Every coordinate
has an error bounded independently of that order, so the normalized sizes
converge to the prescribed probability weights.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.PartitionRounding

universe u v
variable {A : Type u} [Fintype A] [DecidableEq A]

theorem exists_counts (x : A → ℝ) (hx : ProbabilityWeights x) (n : ℕ) :
    ∃ d : A → ℕ, (∑ a, d a = n) ∧
      ∀ a, |(d a : ℝ) - n * x a| ≤ Fintype.card A := by
  classical
  have hne : Nonempty A := by
    by_contra h
    haveI : IsEmpty A := not_nonempty_iff.mp h
    simpa using hx.2
  let a₀ : A := Classical.choice hne
  let f (a : A) : ℕ := ⌊(n : ℝ) * x a⌋₊
  have hf a : (f a : ℝ) ≤ n * x a := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hx.1 a))
  have hflt a : (n : ℝ) * x a < f a + 1 := Nat.lt_floor_add_one _
  have htotal : ∑ a, ((n : ℝ) * x a) = n := by
    rw [← Finset.mul_sum, hx.2, mul_one]
  have hsum : ∑ a, f a ≤ n := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hf a)
    rw [htotal, ← Nat.cast_sum] at h
    exact_mod_cast h
  let R := n - ∑ a, f a
  have hR : (R : ℝ) ≤ Fintype.card A := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => (hflt a).le)
    rw [htotal, Finset.sum_add_distrib] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    dsimp [R]
    rw [Nat.cast_sub hsum, Nat.cast_sum]
    linarith
  have hcard : (1 : ℝ) ≤ Fintype.card A := by
    haveI := hne
    exact_mod_cast Fintype.card_pos_iff.mpr hne
  let d (a : A) := f a + if a = a₀ then R else 0
  refine ⟨d, ?_, fun a => ?_⟩
  · simp only [d, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Nat.add_sub_of_le hsum
  · by_cases ha : a = a₀
    · simp only [d, ha, ite_true, Nat.cast_add]
      apply abs_le.mpr
      constructor
      · have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
        linarith [hflt a₀]
      · linarith [hf a₀]
    · simp only [d, if_neg ha, add_zero]
      exact (Nat.abs_floor_sub_le (mul_nonneg (Nat.cast_nonneg n) (hx.1 a))).trans hcard

theorem exists_counts_normalized (x : A → ℝ) (hx : ProbabilityWeights x)
    (n : ℕ) (hn : 0 < n) :
    ∃ d : A → ℕ, (∑ a, d a = n) ∧
      ∀ a, |(d a : ℝ) / n - x a| ≤ (Fintype.card A : ℝ) / n := by
  obtain ⟨d, hd, he⟩ := exists_counts x hx n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨d, hd, fun a => ?_⟩
  calc
    _ = |((d a : ℝ) - n * x a) / n| := by
      congr 1
      field_simp
    _ = |(d a : ℝ) - n * x a| / n := by rw [abs_div, abs_of_pos hn']
    _ ≤ (Fintype.card A : ℝ) / n := div_le_div_of_nonneg_right (he a) hn'.le

/-- Exact class totals along any diverging sequence of graph orders. -/
theorem exists_counts_tendsto (x : A → ℝ) (hx : ProbabilityWeights x)
    {I : Type v} (n : I → ℕ) (l : Filter I) (hsize : Tendsto n l atTop) :
    ∃ d : I → A → ℕ, (∀ i, ∑ a, d i a = n i) ∧
      ∀ a, Tendsto (fun i => (d i a : ℝ) / n i) l (𝓝 (x a)) := by
  classical
  have hd i : ∃ d : A → ℕ, (∑ a, d a = n i) ∧
      (0 < n i → ∀ a, |(d a : ℝ) / n i - x a| ≤ (Fintype.card A : ℝ) / n i) := by
    by_cases hn : 0 < n i
    · obtain ⟨d, hd, he⟩ := exists_counts_normalized x hx (n i) hn
      exact ⟨d, hd, fun _ => he⟩
    · obtain ⟨d, hd, _⟩ := exists_counts x hx (n i)
      exact ⟨d, hd, fun h => False.elim (hn h)⟩
  choose d hd he using hd
  refine ⟨d, hd, fun a => ?_⟩
  have hden : Tendsto (fun i => ((n i : ℝ))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsize)
  have hsmall : Tendsto (fun i => (Fintype.card A : ℝ) / n i) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hden.const_mul (Fintype.card A : ℝ)
  have herr : Tendsto (fun i => (d i a : ℝ) / n i - x a) l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hsmall
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with i hi
    exact he i (by omega) a
  simpa only [sub_add_cancel, zero_add] using herr.add_const (x a)

/-- Balanced rounding: every class has its floor or ceiling size and the
total remains exactly the prescribed order. This also handles zero weights
and order zero. -/
theorem exists_floor_ceil_counts (x : A → ℝ) (hx : ProbabilityWeights x) (n : ℕ) :
    ∃ d : A → ℕ, (∑ a, d a = n) ∧
      ∀ a, d a = ⌊(n : ℝ) * x a⌋₊ ∨ d a = ⌈(n : ℝ) * x a⌉₊ := by
  classical
  let f (a : A) : ℕ := ⌊(n : ℝ) * x a⌋₊
  let g (a : A) : ℕ := ⌈(n : ℝ) * x a⌉₊
  let T : Finset A := Finset.univ.filter (fun a => f a < g a)
  have htotal : ∑ a, ((n : ℝ) * x a) = n := by
    rw [← Finset.mul_sum, hx.2, mul_one]
  have hfloor : ∑ a, f a ≤ n := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hx.1 a)))
    rw [htotal, ← Nat.cast_sum] at h
    exact_mod_cast h
  have hceil : n ≤ ∑ a, g a := by
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
      Nat.le_ceil ((n : ℝ) * x a))
    rw [htotal, ← Nat.cast_sum] at h
    exact_mod_cast h
  have hstep a : g a = f a + if a ∈ T then 1 else 0 := by
    have h1 := Nat.floor_le_ceil ((n : ℝ) * x a)
    have h2 := Nat.ceil_le_floor_add_one ((n : ℝ) * x a)
    change f a ≤ g a at h1
    change g a ≤ f a + 1 at h2
    by_cases ha : a ∈ T
    · have hlt : f a < g a := (Finset.mem_filter.mp ha).2
      simp only [if_pos ha]
      omega
    · have hn : ¬ f a < g a := by simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      simp only [if_neg ha, add_zero]
      omega
  have hsum : ∑ a, g a = (∑ a, f a) + T.card := by
    simp_rw [hstep]
    rw [Finset.sum_add_distrib]
    simp
  have hleft : n - ∑ a, f a ≤ T.card := by omega
  obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq hleft
  let d (a : A) := f a + if a ∈ S then 1 else 0
  refine ⟨d, ?_, fun a => ?_⟩
  · simp only [d, Finset.sum_add_distrib]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hS]
    exact Nat.add_sub_of_le hfloor
  · by_cases ha : a ∈ S
    · right
      change f a + (if a ∈ S then 1 else 0) = g a
      rw [hstep, if_pos ha, if_pos (hST ha)]
    · left
      simp only [d, if_neg ha, add_zero, f]

theorem floor_ceil_count_error (x : ℝ) (hx : 0 ≤ x) (n d : ℕ)
    (hd : d = ⌊(n : ℝ) * x⌋₊ ∨ d = ⌈(n : ℝ) * x⌉₊) :
    |(d : ℝ) - n * x| ≤ 1 := by
  rcases hd with rfl | rfl
  · exact Nat.abs_floor_sub_le (mul_nonneg (Nat.cast_nonneg n) hx)
  · exact Nat.abs_ceil_sub_le (mul_nonneg (Nat.cast_nonneg n) hx)

end TuranUniversality.PartitionRounding
