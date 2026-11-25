/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.BlockSampling

/-! # Discarding small residual guard blocks -/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

variable {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

def blockFiber (block : V → B) (b : B) : Finset V :=
  Finset.univ.filter fun v => block v = b

def survivingBlock (block : V → B) (Marked : Finset V) (b : B) : Finset V :=
  blockFiber block b \ Marked

/-- Keep unmarked vertices only in blocks with at least `k` survivors. -/
def retainedVertices (block : V → B) (Marked : Finset V) (k : ℕ) : Finset V :=
  Finset.univ.filter fun v => v ∉ Marked ∧ k ≤ (survivingBlock block Marked (block v)).card

omit [Fintype B] [DecidableEq V] in
@[simp] theorem mem_blockFiber (block : V → B) (b : B) (v : V) :
    v ∈ blockFiber block b ↔ block v = b := by simp [blockFiber]

omit [Fintype B] in
@[simp] theorem mem_survivingBlock (block : V → B) (Marked : Finset V) (b : B) (v : V) :
    v ∈ survivingBlock block Marked b ↔ block v = b ∧ v ∉ Marked := by
  simp [survivingBlock]

omit [Fintype B] in
@[simp] theorem mem_retainedVertices (block : V → B) (Marked : Finset V) (k : ℕ) (v : V) :
    v ∈ retainedVertices block Marked k ↔
      v ∉ Marked ∧ k ≤ (survivingBlock block Marked (block v)).card := by
  simp [retainedVertices]

omit [Fintype V] [DecidableEq V] in
theorem sum_fiber_card (block : V → B) (S : Finset V) :
    (∑ b, (S.filter fun v => block v = b).card) = S.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter S Finset.univ block

omit [Fintype B] in
theorem surviving_marked_card (block : V → B) (Marked : Finset V) (b : B) :
    (survivingBlock block Marked b).card +
      (Marked.filter fun v => block v = b).card = (blockFiber block b).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := blockFiber block b) (p := fun v => v ∈ Marked)
  have h1 : (blockFiber block b).filter (fun v => v ∈ Marked) =
      Marked.filter (fun v => block v = b) := by ext v; simp [and_comm]
  have h2 : (blockFiber block b).filter (fun v => v ∉ Marked) =
      survivingBlock block Marked b := by ext v; simp
  rw [h1, h2] at h
  omega

omit [Fintype B] in
theorem retained_fiber (block : V → B) (Marked : Finset V) (k : ℕ) (b : B) :
    (retainedVertices block Marked k).filter (fun v => block v = b) =
      if k ≤ (survivingBlock block Marked b).card then survivingBlock block Marked b else ∅ := by
  ext v
  by_cases hk : k ≤ (survivingBlock block Marked b).card
  · by_cases hb : block v = b <;> simp [hk, hb]
  · by_cases hb : block v = b <;> simp [hk, hb]

/-- After marked vertices and undersized residual blocks are removed, at
most one third as many additional vertices as marked vertices are lost. -/
theorem retained_card_bound (block : V → B) (Marked : Finset V)
    (k t : ℕ) (ht : 4 * k ≤ t)
    (hblocks : ∀ b, (blockFiber block b).card = t) :
    3 * Fintype.card V ≤ 3 * (retainedVertices block Marked k).card + 4 * Marked.card := by
  have hpoint (b : B) : 3 * (blockFiber block b).card ≤
      3 * ((retainedVertices block Marked k).filter fun v => block v = b).card +
        4 * (Marked.filter fun v => block v = b).card := by
    have hbalance := surviving_marked_card block Marked b
    rw [retained_fiber]
    by_cases hkeep : k ≤ (survivingBlock block Marked b).card
    · rw [ite_eq_left hkeep]
      omega
    · rw [ite_eq_right hkeep, Finset.card_empty]
      have hblock := hblocks b
      omega
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset B)) => hpoint b)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [sum_fiber_card block (retainedVertices block Marked k), sum_fiber_card block Marked] at hsum
  have htotal : (∑ b, (blockFiber block b).card) = Fintype.card V := by
    simpa [blockFiber] using sum_fiber_card block (Finset.univ : Finset V)
  rw [htotal] at hsum
  exact hsum

omit [Fintype B] in
/-- Every occupied block of the retained vertex type has at least `k`
vertices. This is the interface for the cyclic block sampler. -/
theorem retained_block_size (block : V → B) (Marked : Finset V) (k : ℕ) (b : B)
    (hb : Nonempty {v : retainedVertices block Marked k // block v.val = b}) :
    k ≤ Fintype.card {v : retainedVertices block Marked k // block v.val = b} := by
  classical
  obtain ⟨v⟩ := hb
  have hsize : k ≤ (survivingBlock block Marked b).card := by
    have h := (mem_retainedVertices block Marked k v.val.val).mp v.val.property
    simpa [v.property] using h.2
  let e : {w : V // w ∈ survivingBlock block Marked b} ≃
      {v : retainedVertices block Marked k // block v.val = b} :=
    { toFun := fun w =>
        ⟨⟨w.val, by
          have hw := (mem_survivingBlock block Marked b w.val).mp w.property
          exact (mem_retainedVertices block Marked k w.val).mpr
            ⟨hw.2, by simpa [hw.1] using hsize⟩⟩,
          ((mem_survivingBlock block Marked b w.val).mp w.property).1⟩
      invFun := fun w => ⟨w.val.val, by
        apply (mem_survivingBlock block Marked b w.val.val).mpr
        exact ⟨w.property, ((mem_retainedVertices block Marked k w.val.val).mp w.val.property).1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, Fintype.card_coe]
  exact hsize

end TuranUniversality.Selector
