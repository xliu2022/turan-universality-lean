module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Exact finite class-size rounding

Formalization author: Xizhi Liu.
Maintainer: Xizhi Liu.

A partition can be changed to any prescribed integer class sizes with the
same total size. The number of reassigned vertices is bounded by the total
surplus of the original classes. This is a finite statement, including empty
classes and an empty vertex carrier.
-/

open scoped BigOperators

namespace TuranUniversality.PartitionRounding

universe u v
variable {V : Type u} {A : Type v} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A]

def fiberSize (ρ : V → A) (a : A) : ℕ :=
  (Finset.univ.filter fun v => ρ v = a).card

theorem sum_fiberSize (ρ : V → A) : ∑ a, fiberSize ρ a = Fintype.card V := by
  simpa [fiberSize] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V) Finset.univ ρ

theorem exists_fiberSize (d : A → ℕ) (hd : ∑ a, d a = Fintype.card V) :
    ∃ σ : V → A, ∀ a, fiberSize σ a = d a := by
  classical
  let e : V ≃ Σ a, Fin (d a) := Fintype.equivOfCardEq (by simpa using hd.symm)
  refine ⟨fun v => (e v).1, fun a => ?_⟩
  rw [fiberSize, ← Fintype.card_subtype]
  calc
    _ = Fintype.card {s : (Σ a, Fin (d a)) // s.1 = a} :=
      Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
    _ = Fintype.card (Fin (d a)) := Fintype.card_congr (Equiv.sigmaSubtype a)
    _ = d a := Fintype.card_fin _

/-- Keep as many vertices as possible in each original class and reassign
only the surplus. The target class sizes are exact natural numbers. -/
theorem exists_reassignment (ρ : V → A) (d : A → ℕ)
    (hd : ∑ a, d a = Fintype.card V) :
    ∃ σ : V → A, (∀ a, fiberSize σ a = d a) ∧
      (Finset.univ.filter fun v => σ v ≠ ρ v).card ≤
        ∑ a, (fiberSize ρ a - d a) := by
  classical
  let m (a : A) := min (fiberSize ρ a) (d a)
  have hsub a : ∃ S ⊆ (Finset.univ.filter fun v => ρ v = a), S.card = m a :=
    Finset.exists_subset_card_eq (min_le_left _ _)
  choose S hS hScard using hsub
  let K := Finset.univ.biUnion S
  have hSK a : S a ⊆ K := Finset.subset_biUnion_of_mem S (Finset.mem_univ a)
  have hrole a v (hv : v ∈ S a) : ρ v = a := (Finset.mem_filter.mp (hS a hv)).2
  have hKfiber a : K.filter (fun v => ρ v = a) = S a := by
    ext v
    constructor
    · intro hv
      obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hv).1
      have hab : b = a := (hrole b v hb).symm.trans (Finset.mem_filter.mp hv).2
      simpa only [hab] using hb
    · intro hv
      exact Finset.mem_filter.mpr ⟨hSK a hv, hrole a v hv⟩
  have hKcard : K.card = ∑ a, m a := by
    calc
      _ = ∑ a, (K.filter fun v => ρ v = a).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = ∑ a, m a := by simp_rw [hKfiber, hScard]
  let W := {v : V // v ∉ K}
  have hWcard : Fintype.card W = Fintype.card V - K.card := by
    simpa [W, Fintype.card_subtype] using
      Fintype.card_subtype_compl (fun v : V => v ∈ K)
  have hrem : ∑ a, (d a - m a) = Fintype.card W := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => min_le_right _ _),
      hd, hWcard, hKcard]
  obtain ⟨γ, hγ⟩ := exists_fiberSize (V := W) (fun a => d a - m a) hrem
  let σ (v : V) : A := if hv : v ∈ K then ρ v else γ ⟨v, hv⟩
  have hσ (a : A) : fiberSize σ a = d a := by
    let T := (Finset.univ.filter fun w : W => γ w = a).image Subtype.val
    have hT v : v ∈ T ↔ ∃ hv : v ∉ K, γ ⟨v, hv⟩ = a := by
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw⟩
      · rintro ⟨hv, hγv⟩
        exact ⟨⟨v, hv⟩, hγv, rfl⟩
    have hdis : Disjoint (S a) T := by
      rw [Finset.disjoint_left]
      intro v hv ht
      exact (hT v |>.mp ht).choose (hSK a hv)
    have heq : (Finset.univ.filter fun v => σ v = a) = S a ∪ T := by
      rw [← hKfiber a]
      ext v
      by_cases hv : v ∈ K
      · have hnT : v ∉ T := by
          intro ht
          exact (hT v |>.mp ht).choose hv
        simp [σ, hv, hnT]
      · simp [σ, hv, hT]
    calc
      _ = (S a ∪ T).card := congrArg Finset.card heq
      _ = (S a).card + T.card := Finset.card_union_of_disjoint hdis
      _ = m a + fiberSize γ a := by
        rw [hScard, Finset.card_image_of_injective _ Subtype.val_injective]
        rfl
      _ = d a := by rw [hγ]; exact Nat.add_sub_of_le (min_le_right _ _)
  refine ⟨σ, hσ, ?_⟩
  have hmoved : (Finset.univ.filter fun v => σ v ≠ ρ v) ⊆ Finset.univ \ K := by
    intro v hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, ?_⟩
    intro hK
    exact (Finset.mem_filter.mp hv).2 (by simp [σ, hK])
  calc
    _ ≤ (Finset.univ \ K).card := Finset.card_le_card hmoved
    _ = Fintype.card V - ∑ a, m a := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hKcard]
    _ = ∑ a, (fiberSize ρ a - m a) := by
      rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => min_le_left _ _), sum_fiberSize]
    _ = ∑ a, (fiberSize ρ a - d a) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp [m]
      omega

/-- The corresponding real-valued error bound, convenient for limits. -/
theorem exists_reassignment_real (ρ : V → A) (d : A → ℕ)
    (hd : ∑ a, d a = Fintype.card V) :
    ∃ σ : V → A, (∀ a, fiberSize σ a = d a) ∧
      ((Finset.univ.filter fun v => σ v ≠ ρ v).card : ℝ) ≤
        ∑ a, |(fiberSize ρ a : ℝ) - d a| := by
  classical
  obtain ⟨σ, hσ, hmove⟩ := exists_reassignment ρ d hd
  refine ⟨σ, hσ, (Nat.cast_le.mpr hmove).trans ?_⟩
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : d a ≤ fiberSize ρ a
  · rw [Nat.cast_sub h]
    exact le_abs_self _
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero]
    exact abs_nonneg _

theorem exists_reassignment_normalized (ρ : V → A) (d : A → ℕ)
    (hd : ∑ a, d a = Fintype.card V) (N : ℝ) (hN : 0 < N) :
    ∃ σ : V → A, (∀ a, fiberSize σ a = d a) ∧
      ((Finset.univ.filter fun v => σ v ≠ ρ v).card : ℝ) / N ≤
        ∑ a, |(fiberSize ρ a : ℝ) / N - (d a : ℝ) / N| := by
  obtain ⟨σ, hσ, hmove⟩ := exists_reassignment_real ρ d hd
  refine ⟨σ, hσ, ?_⟩
  calc
    _ ≤ (∑ a, |(fiberSize ρ a : ℝ) - d a|) / N :=
      div_le_div_of_nonneg_right hmove hN.le
    _ = ∑ a, |(fiberSize ρ a : ℝ) / N - (d a : ℝ) / N| := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [← sub_div, abs_div, abs_of_pos hN]

end TuranUniversality.PartitionRounding
