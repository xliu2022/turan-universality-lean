module

public import TuranUniversality.Weighted.Grounded
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Grounding a finite graph at a zero-weight vertex -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

def pairEnergy {V : Type*} (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => (x a - x b) ^ 2, fun a b => by ring⟩

@[simp] theorem pairEnergy_mk {V : Type*} (x : V → ℝ) (a b : V) :
    pairEnergy x s(a, b) = (x a - x b) ^ 2 := rfl

theorem pairEnergy_nonneg {V : Type*} (x : V → ℝ) (e : Sym2 V) : 0 ≤ pairEnergy x e := by
  induction e using Sym2.ind
  exact sq_nonneg _

theorem path_edge_injective {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) :
    Set.InjOn (fun i => s(p.getVert i, p.getVert (i + 1))) (Finset.range p.length : Set ℕ) := by
  intro i hi j hj hij
  have hi' : i < p.length := Finset.mem_range.mp hi
  have hj' : j < p.length := Finset.mem_range.mp hj
  rcases Sym2.eq_iff.mp hij with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) hleft
  · have hij' : i = j + 1 := hp.getVert_injOn
      (by change i ≤ p.length; omega) (by change j + 1 ≤ p.length; omega) hleft
    have hji' : i + 1 = j := hp.getVert_injOn
      (by change i + 1 ≤ p.length; omega) (by change j ≤ p.length; omega) hright
    omega

/-- A genuine graph path to a zero vertex gives the finite-mass cubic bound.
`E` may contain extra edges; the estimate uses their actual squared energies. -/
theorem graph_grounded_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : ∀ a b, G.Adj a b → s(a, b) ∈ E)
    (x : V → ℝ) (hx : ∀ a, 0 ≤ x a) (a b : V)
    (hb : x b = 0) (hconn : G.Reachable a b) :
    (x a) ^ 3 ≤ 4 * (∑ v, x v) * (∑ e ∈ E, pairEnergy x e) := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  have hmass : pathMass (fun i => x (p.getVert i)) p.length ≤ ∑ v, x v := by
    unfold pathMass
    have hinj : Set.InjOn p.getVert (Finset.range (p.length + 1) : Set ℕ) := by
      intro i hi j hj hij
      exact hp.getVert_injOn (by have := Finset.mem_range.mp hi; change i ≤ p.length; omega)
        (by have := Finset.mem_range.mp hj; change j ≤ p.length; omega) hij
    rw [← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    exact fun v hv hnot => hx v
  have henergy : pathEnergy (fun i => x (p.getVert i)) p.length ≤ ∑ e ∈ E, pairEnergy x e := by
    have hweight : pathEnergy (fun i => x (p.getVert i)) p.length =
        ∑ i ∈ Finset.range p.length, pairEnergy x s(p.getVert i, p.getVert (i + 1)) := by
      rfl
    rw [hweight, ← Finset.sum_image (path_edge_injective p hp)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      exact hE _ _ (p.adj_getVert_succ (Finset.mem_range.mp hi))
    · exact fun e he hnot => pairEnergy_nonneg x e
  have h := grounded_path_bound (fun i => x (p.getVert i)) p.length
    (∑ v, x v) (∑ e ∈ E, pairEnergy x e)
    (fun i hi => hx _) (by simpa using hb) hmass henergy
  simpa using h

end TuranUniversality.Weighted
