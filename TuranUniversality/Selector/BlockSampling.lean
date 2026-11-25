/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.CrossIntersecting
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Sum

/-!
# Balanced sampling inside finite blocks

Cyclic shifts inside each retained clique give pairwise distinct samples
while preserving the uniform marginal at every position. Thus the sampling
argument can be expressed entirely in terms of finite permutations and
finite averages.
-/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

variable {V B J : Type*}

/-- A finite type of at least `k` elements admits `k` permutations whose
images of each individual point are pairwise distinct. Empty types are
handled vacuously. -/
theorem exists_separated_permutations [Fintype V] (k : ℕ)
    (hsize : Nonempty V → k ≤ Fintype.card V) :
    ∃ σ : Fin k → Equiv.Perm V, ∀ x, Function.Injective (fun a => σ a x) := by
  classical
  by_cases hV : Nonempty V
  · let : Nonempty V := hV
    let : NeZero (Fintype.card V) := ⟨ne_of_gt Fintype.card_pos⟩
    let e := Fintype.equivFin V
    let σ : Fin k → Equiv.Perm V := fun a =>
      e.trans ((Equiv.addRight (Fin.castLE (hsize hV) a)).trans e.symm)
    refine ⟨σ, ?_⟩
    intro x a b hab
    have heq := congrArg e hab
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] at heq
    change e x + Fin.castLE (hsize hV) a = e x + Fin.castLE (hsize hV) b at heq
    have hcast := add_left_cancel heq
    apply Fin.ext
    exact congrArg (fun z : Fin (Fintype.card V) => z.val) hcast
  · refine ⟨fun _ => Equiv.refl V, ?_⟩
    intro x
    exact False.elim (hV ⟨x⟩)

/-- The permutations can be chosen within each block of a partition. -/
theorem exists_block_permutations [Fintype V] [DecidableEq B] (k : ℕ) (block : V → B)
    (hsize : ∀ b, Nonempty {x : V // block x = b} →
      k ≤ Fintype.card {x : V // block x = b}) :
    ∃ σ : Fin k → Equiv.Perm V,
      (∀ a x, block (σ a x) = block x) ∧
        ∀ x, Function.Injective (fun a => σ a x) := by
  classical
  have hex (b : B) := exists_separated_permutations (V := {x : V // block x = b}) k (hsize b)
  choose σ hσ using hex
  let e := Equiv.sigmaFiberEquiv block
  let τ : Fin k → Equiv.Perm V := fun a =>
    e.symm.trans ((Equiv.sigmaCongrRight (fun b => σ b a)).trans e)
  refine ⟨τ, ?_, ?_⟩
  · intro a x
    change block (σ (block x) a ⟨x, rfl⟩).val = block x
    exact (σ (block x) a ⟨x, rfl⟩).property
  · intro x a b hab
    change (σ (block x) a ⟨x, rfl⟩).val = (σ (block x) b ⟨x, rfl⟩).val at hab
    exact hσ (block x) ⟨x, rfl⟩ (Subtype.ext hab)

theorem mean_sum [Fintype V] [Fintype J] (f : V → J → ℝ) :
    mean (fun x => ∑ j, f x j) = ∑ j, mean (fun x => f x j) :=
  Finset.expect_sum_comm _ _ _

theorem mean_perm [Fintype V] (σ : Equiv.Perm V) (f : V → ℝ) :
    mean (fun x => f (σ x)) = mean f :=
  Fintype.expect_equiv σ (fun x => f (σ x)) f (fun _ => rfl)

/-- Among `2h` uniformly distributed positions, if the bad set has density
below one half, some starting point has at least `h` good positions. -/
theorem exists_good_positions [Fintype V] [Nonempty V]
    (h : ℕ) (hh : 0 < h) (σ : Fin (2 * h) → Equiv.Perm V)
    (Bad : Finset V) (hBad : density Bad < (1 / 2 : ℝ)) :
    ∃ x : V, ∃ e : Fin h ↪ Fin (2 * h), ∀ a, σ (e a) x ∉ Bad := by
  classical
  let countBad : V → ℝ := fun x => ∑ a : Fin (2 * h), indicator Bad (σ a x)
  have hmean : mean countBad = (2 * h : ℝ) * density Bad := by
    dsimp [countBad]
    rw [mean_sum]
    simp only [mean_perm]
    simp [density]
  have hmeanlt : mean countBad < h := by
    rw [hmean]
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh
    nlinarith
  have hex : ∃ x, countBad x < h := by
    by_contra hn
    push Not at hn
    have hle : (h : ℝ) ≤ mean countBad := by
      rw [← mean_const (α := V) (h : ℝ)]
      exact mean_mono hn
    linarith
  obtain ⟨x, hx⟩ := hex
  let bad : Finset (Fin (2 * h)) := Finset.univ.filter fun a => σ a x ∈ Bad
  let good : Finset (Fin (2 * h)) := Finset.univ.filter fun a => σ a x ∉ Bad
  have hcount : countBad x = bad.card := by simp [countBad, bad, indicator]
  have hbadcard : bad.card < h := by rw [hcount] at hx; exact_mod_cast hx
  have htotal : bad.card + good.card = 2 * h := by
    simpa [bad, good] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * h)))) (p := fun a => σ a x ∈ Bad)
  have hgood : h ≤ Fintype.card {a : Fin (2 * h) // a ∈ good} := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin h) ≤ Fintype.card {a : Fin (2 * h) // a ∈ good} by simpa using hgood)
  refine ⟨x, e.trans (Function.Embedding.subtype _), ?_⟩
  intro a
  exact (Finset.mem_filter.mp (e a).property).2

/-- Restricting uniform measure to an embedded finite set costs at most
the ratio of ambient cardinalities. -/
theorem density_preimage_le [Fintype V] [Nonempty V] [DecidableEq V] {W : Type*}
    [Fintype W] [Nonempty W] (e : W ↪ V) (Bad : Finset V) :
    density (Finset.univ.filter fun w => e w ∈ Bad) ≤
      (Fintype.card V : ℝ) / Fintype.card W * density Bad := by
  classical
  let A : Finset W := Finset.univ.filter fun w => e w ∈ Bad
  have hcard : A.card ≤ Bad.card := by
    calc
      A.card = (A.map e).card := (Finset.card_map e).symm
      _ ≤ Bad.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hx
        exact (Finset.mem_filter.mp hw).2
  have hR : (A.card : ℝ) ≤ Bad.card := by exact_mod_cast hcard
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt Fintype.card_pos : Fintype.card V ≠ 0)
  change density A ≤ _
  rw [density_eq_card, density_eq_card]
  calc
    (A.card : ℝ) / Fintype.card W ≤ (Bad.card : ℝ) / Fintype.card W :=
      div_le_div_of_nonneg_right hR (by positivity)
    _ = (Fintype.card V : ℝ) / Fintype.card W * ((Bad.card : ℝ) / Fintype.card V) := by
      field_simp

/-- Simultaneously choose good words whose entries in every coordinate are
distinct vertices of a single block. -/
theorem choose_good_block_rows {I : Type*} [Fintype I] [DecidableEq I]
    {Y : I → Type*} [∀ i, Fintype (Y i)] [∀ i, Nonempty (Y i)]
    {C : I → Type*} [∀ i, DecidableEq (C i)]
    (h : ℕ) (hh : 0 < h) (block : (i : I) → Y i → C i)
    (hsize : ∀ i c, Nonempty {y : Y i // block i y = c} →
      2 * h ≤ Fintype.card {y : Y i // block i y = c})
    (Bad : Finset ((i : I) → Y i)) (hBad : density Bad < (1 / 2 : ℝ)) :
    ∃ w : Fin h → (i : I) → Y i,
      (∀ a, w a ∉ Bad) ∧
        (∀ i, Function.Injective (fun a => w a i)) ∧
          ∀ i a b, block i (w a i) = block i (w b i) := by
  classical
  have hex (i : I) := exists_block_permutations (2 * h) (block i) (hsize i)
  choose σ hblock hσ using hex
  let τ : Fin (2 * h) → Equiv.Perm ((i : I) → Y i) := fun a =>
    Equiv.piCongrRight (fun i => σ i a)
  obtain ⟨x, e, he⟩ := exists_good_positions h hh τ Bad hBad
  refine ⟨fun a => τ (e a) x, he, ?_, ?_⟩
  · intro i a b hab
    apply e.injective
    exact hσ i (x i) hab
  · intro i a b
    change block i (σ i (e a) (x i)) = block i (σ i (e b) (x i))
    rw [hblock, hblock]

end TuranUniversality.Selector
