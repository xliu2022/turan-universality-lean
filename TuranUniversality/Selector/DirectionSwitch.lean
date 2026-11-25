/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.FunctionSlice
public import TuranUniversality.Selector.GuardSelection

/-! # Selecting a direction with bounded coordinate exclusions -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

theorem density_mono {X : Type*} [Fintype X] {A B : Finset X} (h : A ⊆ B) :
    density A ≤ density B := by
  apply mean_mono
  intro x
  by_cases hx : x ∈ A
  · simp [indicator, hx, h hx]
  · simp only [indicator, ite_eq_right hx]
    split <;> norm_num

/-- Bad-line families are indexed by a direction and a root. The two
intersection hypotheses express that equal root images cannot occur at
vertices differing in every coordinate. -/
theorem select_direction {I V R : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype R] [DecidableEq R]
    (q : ℝ) (hroots : (Fintype.card R : ℝ) ≤ q)
    (hn : 1048576 ≤ Fintype.card V)
    (Z : I → R → Finset (I → V))
    (hself : ∀ j r, ∀ x ∈ Z j r, ∀ y ∈ Z j r, ∃ i, i ≠ j ∧ x i = y i)
    (hcross : ∀ j k, j ≠ k → ∀ r, ∀ x ∈ Z j r, ∀ y ∈ Z k r,
      ∃ i, i ≠ j ∧ i ≠ k ∧ x i = y i) :
    ∃ j : I, ∃ Marked : I → Finset V,
      (∀ i, ((Marked i).card : ℝ) ≤ q / 2) ∧
        (∑ i, ((Marked i).card : ℝ)) ≤ q ∧
          ∀ r, density ((Z j r).filter fun w => ∀ i, w i ∉ Marked i) ≤
            1 / (64 * (Fintype.card V : ℝ)) := by
  classical
  let θ : ℝ := 1 / (64 * (Fintype.card V : ℝ))
  have hex (j : I) (r : R) : ∃ (k : I) (b : V), θ < density (Z j r) →
      k ≠ j ∧ density ((Z j r).filter fun w => w k ≠ b) ≤ θ ∧ density (Z k r) ≤ θ := by
    by_cases hlarge : θ < density (Z j r)
    · have hF : ∀ x ∈ Z j r, ∀ y ∈ Z j r, ∃ i, x i = y i := by
        intro x hx y hy
        obtain ⟨i, _, hi⟩ := hself j r x hx y hy
        exact ⟨i, hi⟩
      obtain hsmall | ⟨k, b, hout, hcontrol⟩ := spectral_slice_functions hn (Z j r) hF
      · exact False.elim ((not_lt_of_ge hsmall) hlarge)
      have hkj : k ≠ j := by
        intro heq
        subst k
        have hsmall := hcontrol (Z j r) (fun x hx _ y hy => hself j r x hx y hy)
        exact (not_lt_of_ge hsmall) hlarge
      refine ⟨k, b, fun _ => ⟨hkj, hout, ?_⟩⟩
      apply hcontrol
      intro x hx _ y hy
      obtain ⟨i, _, hik, hi⟩ := hcross j k (Ne.symm hkj) r x hx y hy
      exact ⟨i, hik, hi⟩
    · exact ⟨j, Classical.choice inferInstance, fun h => False.elim (hlarge h)⟩
  choose coord value hchoice using hex
  let large : I → Finset R := fun j => Finset.univ.filter fun r => θ < density (Z j r)
  let assigned : I → I → Finset R := fun j k => (large j).filter fun r => coord j r = k
  have hsum (j : I) : ∑ k, (assigned j k).card = (large j).card :=
    sum_fiber_card (coord j) (large j)
  have hsub (j k : I) : (assigned j k).card ≤ (large j).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hlargecard (j : I) : ((large j).card : ℝ) ≤ q := by
    have hc : ((large j).card : ℝ) ≤ Fintype.card R := by
      exact_mod_cast (Finset.card_le_univ (large j))
    exact hc.trans hroots
  have hdir : ∃ j, ∀ k, ((assigned j k).card : ℝ) ≤ q / 2 := by
    let j₀ : I := Classical.choice inferInstance
    by_cases hcap : ∀ k, ((assigned j₀ k).card : ℝ) ≤ q / 2
    · exact ⟨j₀, hcap⟩
    · push Not at hcap
      obtain ⟨k, hk⟩ := hcap
      have hdis : Disjoint (large k) (assigned j₀ k) := by
        apply Finset.disjoint_left.mpr
        intro r hr hrold
        have hrnew : θ < density (Z k r) := (Finset.mem_filter.mp hr).2
        have hold := Finset.mem_filter.mp hrold
        have hsmall := (hchoice j₀ r ((Finset.mem_filter.mp hold.1).2)).2.2
        rw [hold.2] at hsmall
        exact (not_lt_of_ge hsmall) hrnew
      have htotal : (large k).card + (assigned j₀ k).card ≤ Fintype.card R := by
        rw [← Finset.card_union_of_disjoint hdis]
        exact Finset.card_le_univ _
      have htotalR : ((large k).card : ℝ) + (assigned j₀ k).card ≤ q := by
        have hc : ((large k).card : ℝ) + (assigned j₀ k).card ≤ Fintype.card R := by
          exact_mod_cast htotal
        exact hc.trans hroots
      refine ⟨k, ?_⟩
      intro i
      have hcard : ((assigned k i).card : ℝ) ≤ (large k).card := by exact_mod_cast hsub k i
      linarith
  obtain ⟨j, hj⟩ := hdir
  let Marked : I → Finset V := fun k => (assigned j k).image (value j)
  have hmarked (k : I) : (Marked k).card ≤ (assigned j k).card := Finset.card_image_le
  refine ⟨j, Marked, ?_, ?_, ?_⟩
  · intro k
    have hc : ((Marked k).card : ℝ) ≤ (assigned j k).card := by exact_mod_cast hmarked k
    exact hc.trans (hj k)
  · calc
      ∑ k, ((Marked k).card : ℝ) ≤ ∑ k, ((assigned j k).card : ℝ) :=
        Finset.sum_le_sum (fun k _ => by exact_mod_cast hmarked k)
      _ = (large j).card := by exact_mod_cast hsum j
      _ ≤ q := hlargecard j
  · intro r
    by_cases hr : θ < density (Z j r)
    · have hsmall := (hchoice j r hr).2.1
      have hsubsets : ((Z j r).filter fun w => ∀ i, w i ∉ Marked i) ⊆
          ((Z j r).filter fun w => w (coord j r) ≠ value j r) := by
        intro w hw
        obtain ⟨hwZ, hwM⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_filter.mpr ⟨hwZ, ?_⟩
        intro heq
        apply hwM (coord j r)
        apply Finset.mem_image.mpr
        refine ⟨r, ?_, heq.symm⟩
        simp [assigned, large, hr]
      exact (density_mono hsubsets).trans hsmall
    · exact (density_mono (Finset.filter_subset _ _)).trans (le_of_not_gt hr)

end TuranUniversality.Selector
