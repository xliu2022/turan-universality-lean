module

public import TuranUniversality.Structural.FrameBasic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-! # Balance equations identify the five-point roles

If a nonnegative integer function has a fixed sum on every neutral-frame
edge, it is constant on each source block and on the five data vertices.
These are equations in the actual ordinary frame, not assumptions about its
automorphism group.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

theorem Compiled.edge_sum {V : Type*} [DecidableEq V] {b t : ℕ}
    (Z : Finset (Support.Vertex b)) (X : Finset V) (f : Compiled.Vertex b t V → ℕ) :
    (∑ v ∈ Compiled.edge t Z X, f v) =
      (∑ i : Fin t, f (.inl i)) +
        (∑ v ∈ Z, f (.inr (.inl v))) + ∑ v ∈ X, f (.inr (.inr v)) := by
  rw [Compiled.edge, RGraph.suspendEdge,
    Finset.sum_union (RGraph.suspendEdge_disjoint t (Z.disjSum X))]
  simp [Finset.sum_disjSum, Nat.add_assoc]

namespace Frame

open Cube Support

theorem pentagon_constant (f : Fin 5 → ℕ) (c : ℕ)
    (h : ∀ E ∈ Pentagon.P0.edges, ∑ v ∈ E, f v = c) : ∀ a, f a = f 0 := by
  have h0 := h {0, 1, 2} (by simp [Pentagon.P0])
  have h1 := h {1, 2, 3} (by simp [Pentagon.P0])
  have h2 := h {2, 3, 4} (by simp [Pentagon.P0])
  have h3 := h {0, 3, 4} (by simp [Pentagon.P0])
  have h4 := h {0, 1, 4} (by simp [Pentagon.P0])
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton] at h0 h1 h2 h3 h4
  have h01 : f 1 = f 0 := by omega
  have h02 : f 2 = f 0 := by omega
  have h03 : f 3 = f 0 := by omega
  have h04 : f 4 = f 0 := by omega
  intro a
  fin_cases a
  · rfl
  · exact h01
  · exact h02
  · exact h03
  · exact h04

theorem foursets_constant (f : Fin 5 → ℕ) (c : ℕ)
    (h : ∀ X : Finset (Fin 5), X.card = 4 → ∑ v ∈ X, f v = c) : ∀ a, f a = f 0 := by
  intro a
  have ha := h (Finset.univ.erase a) (by simp)
  have hz := h (Finset.univ.erase 0) (by simp)
  have hsa := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have hsz := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : Fin 5))
  omega

def rowChoice {b : ℕ} (i : Fin b) (E : Pentagon.P0.edges) : Choice (∅ : Word b) :=
  fun j => ⟨if j = i then E.val else {0, 1, 2}, by
    by_cases h : j = i
    · simpa [h, blockGraph, Pentagon.graph] using E.property
    · simp [h, blockGraph, Pentagon.graph, Pentagon.P0]⟩

theorem rowChoice_sum {b : ℕ} (i : Fin b) (E : Pentagon.P0.edges)
    (f : Support.Vertex b → ℕ) :
    (∑ v ∈ choiceEdge ∅ (rowChoice i E), f v) =
      (∑ a ∈ E.val, f ⟨i, a⟩) +
        ∑ j ∈ (Finset.univ : Finset (Fin b)) \ {i}, ∑ a ∈ ({0, 1, 2} : Finset (Fin 5)), f ⟨j, a⟩ := by
  rw [choiceEdge, joinRows, Finset.sum_sigma]
  have hfun : (fun j : Fin b => ∑ a ∈ (rowChoice i E j).val, f ⟨j, a⟩) =
      Function.update (fun j : Fin b => ∑ a ∈ ({0, 1, 2} : Finset (Fin 5)), f ⟨j, a⟩)
        i (∑ a ∈ E.val, f ⟨i, a⟩) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [rowChoice]
    · simp [rowChoice, hj, Function.update_of_ne hj]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]

theorem block_constant {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω)
    (f : Compiled.Vertex b t (Fin 5) → ℕ) (c : ℕ)
    (h : ∀ e ∈ (graph b t Ω).edges, ∑ v ∈ e, f v = c) :
    ∀ (i : Fin b) (a : Fin 5), f (.inr (.inl ⟨i, a⟩)) = f (.inr (.inl ⟨i, 0⟩)) := by
  intro i
  apply pentagon_constant _ (∑ a ∈ ({0, 1, 2} : Finset (Fin 5)), f (.inr (.inl ⟨i, a⟩)))
  intro E hE
  let E0 : Pentagon.P0.edges := ⟨{0, 1, 2}, by simp [Pentagon.P0]⟩
  have hE' := h _ (edge_mem (t := t) hzero (rowChoice i ⟨E, hE⟩)
    (X := {0, 1, 2, 3}) (by decide))
  have h0 := h _ (edge_mem (t := t) hzero (rowChoice i E0)
    (X := {0, 1, 2, 3}) (by decide))
  rw [Compiled.edge_sum, rowChoice_sum] at hE' h0
  dsimp only [E0] at h0
  dsimp only at hE'
  omega

theorem data_constant {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω)
    (f : Compiled.Vertex b t (Fin 5) → ℕ) (c : ℕ)
    (h : ∀ e ∈ (graph b t Ω).edges, ∑ v ∈ e, f v = c) :
    ∀ a : Fin 5, f (.inr (.inr a)) = f (.inr (.inr 0)) := by
  apply foursets_constant _ (∑ a ∈ ({0, 1, 2, 3} : Finset (Fin 5)), f (.inr (.inr a)))
  intro X hX
  have hX' := h _ (edge_mem (t := t) hzero (baseChoice b) hX)
  have h0 := h _ (edge_mem (t := t) hzero (baseChoice b)
    (X := {0, 1, 2, 3}) (by decide))
  rw [Compiled.edge_sum] at hX' h0
  omega

end Frame

end TuranUniversality.Structural
