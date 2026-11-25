module

public import TuranUniversality.Hypergraph.FiniteProfiles
public import TuranUniversality.Hypergraph.PartitionCounts

@[expose] public section

/-! # Exact class-size rounding without changing a finite-profile limit

The target integer counts depend only on the fixed profile and the total
order. Adjusting a presentation with convergent proportions changes `o(n)`
vertices and therefore `o(n^r)` actual edges.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.FiniteRolePattern

open PartitionRounding

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def roundedCounts (z : A → ℝ) (hz : ProbabilityWeights z) (n : ℕ) : A → ℕ :=
  Classical.choose (exists_floor_ceil_counts z hz n)

theorem roundedCounts_sum (z : A → ℝ) (hz : ProbabilityWeights z) (n : ℕ) :
    ∑ a, roundedCounts z hz n a = n := (Classical.choose_spec (exists_floor_ceil_counts z hz n)).1

theorem roundedCounts_floor_ceil (z : A → ℝ) (hz : ProbabilityWeights z) (n : ℕ) (a : A) :
    roundedCounts z hz n a = ⌊(n : ℝ) * z a⌋₊ ∨
      roundedCounts z hz n a = ⌈(n : ℝ) * z a⌉₊ :=
  (Classical.choose_spec (exists_floor_ceil_counts z hz n)).2 a

theorem roundedCounts_error_one (z : A → ℝ) (hz : ProbabilityWeights z) (n : ℕ) (a : A) :
    |(roundedCounts z hz n a : ℝ) - n * z a| ≤ 1 :=
  floor_ceil_count_error (z a) (hz.1 a) n _ (roundedCounts_floor_ceil z hz n a)

theorem roundedCounts_error (z : A → ℝ) (hz : ProbabilityWeights z) (n : ℕ) (a : A) :
    |(roundedCounts z hz n a : ℝ) - n * z a| ≤ Fintype.card A := by
  apply (roundedCounts_error_one z hz n a).trans
  exact_mod_cast (show 1 ≤ Fintype.card A from Nat.succ_le_of_lt
    (Fintype.card_pos_iff.mpr ⟨a⟩))

theorem roundedCounts_tendsto (z : A → ℝ) (hz : ProbabilityWeights z)
    {I : Type*} (n : I → ℕ) (l : Filter I) (hsize : Tendsto n l atTop) (a : A) :
    Tendsto (fun i => (roundedCounts z hz (n i) a : ℝ) / n i) l (𝓝 (z a)) := by
  have hsmall : Tendsto (fun i => (Fintype.card A : ℝ) / n i) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hsize)).const_mul
        (Fintype.card A : ℝ)
  have herr : Tendsto (fun i => (roundedCounts z hz (n i) a : ℝ) / n i - z a) l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hsmall
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with i hi
    have hn : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
    calc
      _ = |((roundedCounts z hz (n i) a : ℝ) - n i * z a) / n i| := by
        congr 1
        field_simp
      _ = |(roundedCounts z hz (n i) a : ℝ) - n i * z a| / n i := by
        rw [abs_div, abs_of_pos hn]
      _ ≤ _ := div_le_div_of_nonneg_right (roundedCounts_error z hz (n i) a) hn.le
  simpa only [sub_add_cancel, zero_add] using herr.add_const (z a)

theorem round_presentations {r : ℕ} (P : FiniteRolePattern A r) (hr : 1 ≤ r)
    {I : Type*} {V : I → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (ρ : ∀ i, V i → A) (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (z : A → ℝ) (hz : ProbabilityWeights z)
    (hρ : ∀ a, Tendsto (fun i => (fiberSize (ρ i) a : ℝ) / Fintype.card (V i)) l (𝓝 (z a))) :
    ∃ σ : ∀ i, V i → A,
      (∀ i a, fiberSize (σ i) a = roundedCounts z hz (Fintype.card (V i)) a) ∧
      Tendsto (fun i => ((Finset.univ.filter (fun v : V i => σ i v ≠ ρ i v)).card : ℝ) /
        Fintype.card (V i)) l (𝓝 0) ∧
      Tendsto (fun i => (P.graph (ρ i)).normalizedEditDistance (P.graph (σ i))) l (𝓝 0) := by
  classical
  have hex i := exists_reassignment_normalized (ρ i)
    (roundedCounts z hz (Fintype.card (V i))) (roundedCounts_sum z hz _)
    (Fintype.card (V i) : ℝ) (by exact_mod_cast hn i)
  choose σ hσ hm using hex
  have hsum : Tendsto (fun i => ∑ a,
      |(fiberSize (ρ i) a : ℝ) / Fintype.card (V i) -
        (roundedCounts z hz (Fintype.card (V i)) a : ℝ) / Fintype.card (V i)|) l (𝓝 0) := by
    convert tendsto_finset_sum Finset.univ (fun a _ =>
      ((hρ a).sub (roundedCounts_tendsto z hz _ l hsize a)).abs) using 1 <;> simp
  have hmove : Tendsto (fun i =>
      ((Finset.univ.filter (fun v : V i => σ i v ≠ ρ i v)).card : ℝ) /
        Fintype.card (V i)) l (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) hm hsum
  refine ⟨σ, hσ, hmove, ?_⟩
  apply squeeze_zero (fun i => (P.graph (ρ i)).normalizedEditDistance_nonneg _) _
    (show Tendsto (fun i => 2 * (((Finset.univ.filter
      (fun v : V i => σ i v ≠ ρ i v)).card : ℝ) / Fintype.card (V i))) l (𝓝 0) from
        by simpa using hmove.const_mul 2)
  intro i
  simpa only [ne_comm, mul_div_assoc] using P.edit_le_moved hr (hn i) (ρ i) (σ i)

end TuranUniversality.FiniteRolePattern
