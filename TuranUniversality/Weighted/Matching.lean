module

public import TuranUniversality.Weighted.Symmetric

/-! # Partial matchings, their defect, and the one-root link identity -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v
variable {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]

structure PartialMatching (U : Finset A) (V : Finset B) where
  pairs : Finset (A × B)
  left_mem : ∀ p ∈ pairs, p.1 ∈ U
  right_mem : ∀ p ∈ pairs, p.2 ∈ V
  left_injective : Set.InjOn Prod.fst (pairs : Set (A × B))
  right_injective : Set.InjOn Prod.snd (pairs : Set (A × B))

namespace PartialMatching

variable {U : Finset A} {V : Finset B}

def leftMatched (D : PartialMatching U V) : Finset A := D.pairs.image Prod.fst

def rightMatched (D : PartialMatching U V) : Finset B := D.pairs.image Prod.snd

def weight (D : PartialMatching U V) (x : A → ℝ) (y : B → ℝ) : ℝ :=
  ∑ p ∈ D.pairs, x p.1 * y p.2

/-- Squared differences on present pairs, plus squared weights at missing
incidences. Every indexed relation uses this definition separately. -/
def defect (D : PartialMatching U V) (x : A → ℝ) (y : B → ℝ) : ℝ :=
  (∑ p ∈ D.pairs, (x p.1 - y p.2) ^ 2) +
    (∑ a ∈ U \ D.leftMatched, (x a) ^ 2) + (∑ b ∈ V \ D.rightMatched, (y b) ^ 2)

omit [DecidableEq B] in
theorem leftMatched_subset (D : PartialMatching U V) : D.leftMatched ⊆ U := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact D.left_mem p hp

omit [DecidableEq A] in
theorem rightMatched_subset (D : PartialMatching U V) : D.rightMatched ⊆ V := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
  exact D.right_mem p hp

omit [DecidableEq B] in
theorem sum_leftMatched (D : PartialMatching U V) (f : A → ℝ) :
    (∑ a ∈ D.leftMatched, f a) = ∑ p ∈ D.pairs, f p.1 := by
  unfold leftMatched
  exact Finset.sum_image D.left_injective

omit [DecidableEq A] in
theorem sum_rightMatched (D : PartialMatching U V) (f : B → ℝ) :
    (∑ b ∈ D.rightMatched, f b) = ∑ p ∈ D.pairs, f p.2 := by
  unfold rightMatched
  exact Finset.sum_image D.right_injective

theorem defect_identity (D : PartialMatching U V) (x : A → ℝ) (y : B → ℝ) :
    D.defect x y = (∑ a ∈ U, (x a) ^ 2) + (∑ b ∈ V, (y b) ^ 2) - 2 * D.weight x y := by
  have hl := Finset.sum_sdiff D.leftMatched_subset (f := fun a => (x a) ^ 2)
  have hr := Finset.sum_sdiff D.rightMatched_subset (f := fun b => (y b) ^ 2)
  rw [D.sum_leftMatched] at hl
  rw [D.sum_rightMatched] at hr
  have hp : (∑ p ∈ D.pairs, (x p.1 - y p.2) ^ 2) =
      (∑ p ∈ D.pairs, (x p.1) ^ 2) + (∑ p ∈ D.pairs, (y p.2) ^ 2) - 2 * D.weight x y := by
    unfold weight
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  unfold defect
  rw [hp]
  linarith

theorem defect_nonneg (D : PartialMatching U V) (x : A → ℝ) (y : B → ℝ) : 0 ≤ D.defect x y := by
  unfold defect
  exact add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [DecidableEq A] [DecidableEq B] in
theorem weight_mono (D E : PartialMatching U V) (x : A → ℝ) (y : B → ℝ)
    (hx : ∀ a ∈ U, 0 ≤ x a) (hy : ∀ b ∈ V, 0 ≤ y b) (h : D.pairs ⊆ E.pairs) :
    D.weight x y ≤ E.weight x y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro p hp hnot
  exact mul_nonneg (hx p.1 (E.left_mem p hp)) (hy p.2 (E.right_mem p hp))

/-- Deleting matching pairs increases the defect. -/
theorem defect_antitone (D E : PartialMatching U V) (x : A → ℝ) (y : B → ℝ)
    (hx : ∀ a ∈ U, 0 ≤ x a) (hy : ∀ b ∈ V, 0 ≤ y b) (h : D.pairs ⊆ E.pairs) :
    E.defect x y ≤ D.defect x y := by
  rw [D.defect_identity, E.defect_identity]
  have hw := D.weight_mono E x y hx hy h
  linarith

/-- Adding the two permitted within-type cliques and replacing the complete
cross pair by the matching yields the manuscript's exact correction term. -/
theorem completed_link_identity (D : PartialMatching U V) (x : A → ℝ) (y : B → ℝ)
    (otherCross : ℝ) :
    elementary U x 2 + elementary V y 2 + D.weight x y + otherCross =
      (otherCross + (∑ a ∈ U, x a) * (∑ b ∈ V, y b)) +
        ((∑ a ∈ U, x a) - (∑ b ∈ V, y b)) ^ 2 / 2 - D.defect x y / 2 := by
  have hU := elementary_second_identity U x
  have hV := elementary_second_identity V y
  have hD := D.defect_identity x y
  nlinarith

end PartialMatching

end TuranUniversality.Weighted
