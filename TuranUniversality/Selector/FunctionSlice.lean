/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.SpectralSlice
public import Mathlib.Data.Fintype.EquivFin

/-! # Coordinate slices on arbitrary finite products -/

@[expose] public section

namespace TuranUniversality.Selector

variable {V I : Type*}

theorem wordsEquivFunction_insertWord {d : ℕ} (j : Fin (d + 1))
    (b : V) (w : Words V d) :
    wordsEquivFunction V (d + 1) (insertWord j b w) =
      Fin.insertNth j b (wordsEquivFunction V d w) := by
  induction d with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rw [insertWord_zero, Fin.insertNth_zero']
      rfl
  | succ d ih =>
      refine Fin.cases ?_ ?_ j
      · rw [insertWord_zero, Fin.insertNth_zero']
        rfl
      · intro k
        rw [insertWord_succ]
        change Fin.cons w.1 (wordsEquivFunction V (d + 1) (insertWord k b w.2)) =
          Fin.insertNth (α := fun _ : Fin (d + 2) => V) k.succ b
            (Fin.cons w.1 (wordsEquivFunction V d w.2))
        rw [ih, Fin.insertNth_succ_cons]

theorem wordCoordinate_eq {d : ℕ} (j : Fin (d + 1)) (w : Words V (d + 1)) :
    wordCoordinate j w = wordsEquivFunction V (d + 1) w j := by
  obtain ⟨⟨b, x⟩, rfl⟩ := (insertionEquiv V d j).surjective w
  change wordCoordinate j (insertWord j b x) = wordsEquivFunction V (d + 1) (insertWord j b x) j
  rw [wordCoordinate_insertWord, wordsEquivFunction_insertWord, Fin.insertNth_apply_same]

/-- The section conclusion controls a whole cylinder family whenever it
intersects the selected section outside the selected coordinate. -/
theorem spectral_slice_strong [Fintype V] [Nonempty V]
    (hn : 1048576 ≤ Fintype.card V) {d : ℕ}
    (F : Finset (Words V (d + 1))) (hF : CrossIntersecting F F) :
    density F ≤ 1 / (64 * (Fintype.card V : ℝ)) ∨
      ∃ (j : Fin (d + 1)) (b : V),
        density (outsideSlice F j b) ≤ 1 / (64 * (Fintype.card V : ℝ)) ∧
          ∀ G : Finset (Words V (d + 1)),
            (∀ x ∈ F, wordCoordinate j x = b → ∀ y ∈ G,
              ∃ i, i ≠ j ∧ wordsEquivFunction V (d + 1) x i =
                wordsEquivFunction V (d + 1) y i) →
              density G ≤ 1 / (64 * (Fintype.card V : ℝ)) := by
  classical
  obtain hsmall | ⟨j, b, hout, hcross⟩ := spectral_slice hn F hF
  · exact Or.inl hsmall
  refine Or.inr ⟨j, b, hout, ?_⟩
  intro G hG
  have hsection (c : V) : density (wordSection G j c) ≤
      1 / (64 * (Fintype.card V : ℝ)) := by
    apply hcross
    intro x hx y hy hxy
    obtain ⟨i, hij, heq⟩ := hG (insertWord j b x) ((mem_wordSection F j b x).mp hx)
      (wordCoordinate_insertWord j b x) (insertWord j c y) ((mem_wordSection G j c y).mp hy)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    rw [wordsEquivFunction_insertWord, wordsEquivFunction_insertWord,
      Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at heq
    exact (allDifferent_iff x y).mp hxy k heq
  unfold density
  rw [mean_insertion _ j]
  calc
    _ = mean (fun c => density (wordSection G j c)) := by
      apply mean_congr
      intro c
      exact (density_wordSection G j c).symm
    _ ≤ mean (fun _ : V => 1 / (64 * (Fintype.card V : ℝ))) := mean_mono hsection
    _ = 1 / (64 * (Fintype.card V : ℝ)) := mean_const _

/-- Reindex words by any finite coordinate type. -/
def wordFunctionEquiv {d : ℕ} (e : Fin d ≃ I) : Words V d ≃ (I → V) where
  toFun w i := wordsEquivFunction V d w (e.symm i)
  invFun f := (wordsEquivFunction V d).symm (fun k => f (e k))
  left_inv w := by simp
  right_inv f := by simp

@[simp] theorem wordFunctionEquiv_apply {d : ℕ} (e : Fin d ≃ I) (w : Words V d) (k : Fin d) :
    wordFunctionEquiv (V := V) e w (e k) = wordsEquivFunction V d w k := by
  simp [wordFunctionEquiv]

@[simp] theorem wordFunctionEquiv_symm_apply {d : ℕ} (e : Fin d ≃ I) (f : I → V)
    (k : Fin d) : wordsEquivFunction V d ((wordFunctionEquiv (V := V) e).symm f) k = f (e k) := by
  simp [wordFunctionEquiv]

/-- The full slice theorem on any nonempty finite coordinate type, in a
form suitable for simultaneous bad-line families. -/
theorem spectral_slice_functions [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype V] [Nonempty V] [DecidableEq V] (hn : 1048576 ≤ Fintype.card V)
    (F : Finset (I → V))
    (hF : ∀ x ∈ F, ∀ y ∈ F, ∃ i, x i = y i) :
    density F ≤ 1 / (64 * (Fintype.card V : ℝ)) ∨
      ∃ (j : I) (b : V),
        density (F.filter fun x => x j ≠ b) ≤ 1 / (64 * (Fintype.card V : ℝ)) ∧
          ∀ G : Finset (I → V),
            (∀ x ∈ F, x j = b → ∀ y ∈ G, ∃ i, i ≠ j ∧ x i = y i) →
              density G ≤ 1 / (64 * (Fintype.card V : ℝ)) := by
  classical
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos : 0 < Fintype.card I))
  let e : Fin (d + 1) ≃ I := (Fintype.equivFinOfCardEq hd).symm
  let E : Words V (d + 1) ≃ (I → V) := wordFunctionEquiv e
  let A : Finset (Words V (d + 1)) := F.map E.symm.toEmbedding
  have hmem (x : Words V (d + 1)) : x ∈ A ↔ E x ∈ F := by simp [A]
  have hA : CrossIntersecting A A := by
    intro x hx y hy hxy
    obtain ⟨i, hi⟩ := hF (E x) ((hmem x).mp hx) (E y) ((hmem y).mp hy)
    exact (allDifferent_iff x y).mp hxy (e.symm i) hi
  obtain hsmall | ⟨j, b, hout, hcross⟩ := spectral_slice_strong hn A hA
  · exact Or.inl (by simpa only [A, density_map_equiv] using hsmall)
  refine Or.inr ⟨e j, b, ?_, ?_⟩
  · have heq : (F.filter fun x => x (e j) ≠ b).map E.symm.toEmbedding = outsideSlice A j b := by
      ext x
      simp [outsideSlice, A, E, wordCoordinate_eq, wordFunctionEquiv]
    rw [← density_map_equiv E.symm, heq]
    exact hout
  · intro G hG
    let B := G.map E.symm.toEmbedding
    have hbound : density B ≤ 1 / (64 * (Fintype.card V : ℝ)) := by
      apply hcross
      intro x hx hj y hy
      have hx' : E x ∈ F := (hmem x).mp hx
      have hy' : E y ∈ G := by simpa [B] using hy
      have hj' : E x (e j) = b := by simpa [E, wordCoordinate_eq, wordFunctionEquiv] using hj
      obtain ⟨i, hij, heq⟩ := hG (E x) hx' hj' (E y) hy'
      refine ⟨e.symm i, ?_, heq⟩
      intro hi
      exact hij (by simpa using congrArg e hi)
    simpa only [B, density_map_equiv] using hbound

end TuranUniversality.Selector
