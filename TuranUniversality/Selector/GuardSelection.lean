/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.GuardBlocks
public import TuranUniversality.Selector.GuardDensity

/-! # Selecting good rows from a marked guard product -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

theorem density_biUnion_le {R V : Type*} [Fintype R] [Fintype V]
    [DecidableEq V] (A : R → Finset V) :
    density (Finset.univ.biUnion A) ≤ ∑ r, density (A r) := by
  classical
  simp only [density]
  rw [← mean_sum]
  apply mean_mono
  intro v
  by_cases hv : v ∈ Finset.univ.biUnion A
  · obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hv
    calc
      indicator (Finset.univ.biUnion A) v = indicator (A r) v := by simp [indicator, hv, hr]
      _ ≤ ∑ r, indicator (A r) v := Finset.single_le_sum (f := fun r => indicator (A r) v)
        (fun i _ => by simp only [indicator]; split <;> positivity) (Finset.mem_univ r)
  · simp only [indicator, ite_eq_right hv]
    exact Finset.sum_nonneg (fun i _ => by split <;> positivity)

/-- The finite form of guard sampling used by compatible profiles. Each
coordinate has the same guard, with a bounded set of marked vertices.
The selected rows avoid the marks and the bad set, and their entries in
each coordinate are distinct vertices of one constituent clique. -/
theorem choose_good_guard_rows {I V B : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V]
    [DecidableEq V] [Fintype B] [DecidableEq B]
    (q : ℝ) (hq : 0 < q) (hn : 19 * q / 20 < Fintype.card V)
    (h t : ℕ) (hh : 0 < h) (ht : 8 * h ≤ t)
    (block : V → B) (hblock : ∀ b, (blockFiber block b).card = t)
    (Marked : I → Finset V)
    (hcap : ∀ i, (Marked i).card ≤ q / 2)
    (hbudget : ∑ i, ((Marked i).card : ℝ) ≤ q)
    (Bad : Finset (I → V))
    (hBad : density Bad ≤ q / (64 * Fintype.card V)) :
    ∃ w : Fin h → I → V,
      (∀ a, w a ∉ Bad) ∧
        (∀ a i, w a i ∉ Marked i) ∧
          (∀ i, Function.Injective (fun a => w a i)) ∧
            ∀ i a b, block (w a i) = block (w b i) := by
  classical
  let Y : I → Type _ := fun i => ↥(retainedVertices block (Marked i) (2 * h))
  have hsize (i : I) : (Fintype.card V : ℝ) - 4 * (Marked i).card / 3 ≤
      Fintype.card (Y i) := by
    have hret := retained_card_bound block (Marked i) (2 * h) t (by omega) hblock
    have hR : 3 * (Fintype.card V : ℝ) ≤
        3 * (retainedVertices block (Marked i) (2 * h)).card + 4 * (Marked i).card := by
      exact_mod_cast hret
    simpa only [Y, Fintype.card_coe] using (by linarith :
      (Fintype.card V : ℝ) - 4 * (Marked i).card / 3 ≤
        (retainedVertices block (Marked i) (2 * h)).card)
  have hpos (i : I) : 0 < Fintype.card (Y i) := by
    have hi := hsize i
    have hc := hcap i
    have : (0 : ℝ) < Fintype.card (Y i) := by linarith
    exact_mod_cast this
  let (i : I) : Nonempty (Y i) := Fintype.card_pos_iff.mp (hpos i)
  let e : ((i : I) → Y i) ↪ (I → V) :=
    ⟨fun y i => (y i).val, fun _ _ he => funext (fun i => Subtype.ext (congrFun he i))⟩
  let BadY : Finset ((i : I) → Y i) := Finset.univ.filter fun y => e y ∈ Bad
  have hratio : (Fintype.card (I → V) : ℝ) / Fintype.card ((i : I) → Y i) < 12 := by
    have hbound := guard_product_density_bound q (Fintype.card V) hq hn
      (fun i => ((Marked i).card : ℝ)) (fun i => (Fintype.card (Y i) : ℝ))
      (fun _ => by positivity) hcap hbudget hsize
    simpa only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib] using hbound
  have hBadY : density BadY < (1 / 2 : ℝ) := by
    have hrestrict := density_preimage_le e Bad
    change density BadY ≤ _ at hrestrict
    have hnpos : (0 : ℝ) < Fintype.card V := by positivity
    have hnumeric : 12 * (q / (64 * Fintype.card V)) < (1 / 2 : ℝ) := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      linarith
    apply lt_of_le_of_lt hrestrict
    apply lt_of_le_of_lt _ hnumeric
    exact mul_le_mul (le_of_lt hratio) hBad (density_nonneg Bad) (by norm_num)
  obtain ⟨w, hw, hinj, hsame⟩ := choose_good_block_rows h hh
    (fun i (y : Y i) => block y.val)
    (fun i b hb => retained_block_size block (Marked i) (2 * h) b hb) BadY hBadY
  refine ⟨fun a => e (w a), ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact hw a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
  · intro a i
    exact ((mem_retainedVertices block (Marked i) (2 * h) (w a i).val).mp
      (w a i).property).1
  · intro i a b hab
    exact hinj i (Subtype.ext hab)
  · exact hsame

end TuranUniversality.Selector
