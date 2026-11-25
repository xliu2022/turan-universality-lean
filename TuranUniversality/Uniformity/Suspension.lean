module

public import TuranUniversality.Hypergraph.Polynomial
public import Mathlib.Data.Fintype.Sum

@[expose] public section

/-! # Finite suspensions of three-uniform hypergraphs -/

open scoped BigOperators

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V]

def suspendEdge (s : ℕ) (e : Finset V) : Finset (Fin s ⊕ V) :=
  Finset.univ.map Function.Embedding.inl ∪ e.map Function.Embedding.inr

@[simp] theorem mem_suspendEdge_left (s : ℕ) (e : Finset V) (i : Fin s) :
    Sum.inl i ∈ suspendEdge s e := by simp [suspendEdge]

@[simp] theorem mem_suspendEdge_right (s : ℕ) (e : Finset V) (v : V) :
    Sum.inr v ∈ suspendEdge s e ↔ v ∈ e := by simp [suspendEdge]

theorem suspendEdge_disjoint (s : ℕ) (e : Finset V) :
    Disjoint (Finset.univ.map (Function.Embedding.inl : Fin s ↪ Fin s ⊕ V))
      (e.map Function.Embedding.inr) := by
  simp [Finset.disjoint_left]

theorem suspendEdge_card (s : ℕ) (e : Finset V) :
    (suspendEdge s e).card = s + e.card := by
  rw [suspendEdge, Finset.card_union_of_disjoint (suspendEdge_disjoint s e)]
  simp

theorem suspendEdge_injective (s : ℕ) : Function.Injective (suspendEdge (V := V) s) := by
  intro e f h
  ext v
  have := congrArg (fun d => Sum.inr v ∈ d) h
  simpa using this

/-- Add `s` common vertices to each edge of a three-graph. -/
def suspension (G : RGraph V 3) (s : ℕ) : RGraph (Fin s ⊕ V) (s + 3) where
  edges := G.edges.image (suspendEdge s)
  uniform := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    rw [suspendEdge_card, G.uniform d hd]

@[simp] theorem mem_suspension (G : RGraph V 3) (s : ℕ) (e : Finset (Fin s ⊕ V)) :
    e ∈ (G.suspension s).edges ↔ ∃ d ∈ G.edges, suspendEdge s d = e :=
  Finset.mem_image

theorem suspension_edges_card (G : RGraph V 3) (s : ℕ) :
    (G.suspension s).edges.card = G.edges.card :=
  Finset.card_image_of_injective _ (suspendEdge_injective s)

theorem suspension_has_edges (G : RGraph V 3) (s : ℕ) (h : G.edges.Nonempty) :
    (G.suspension s).edges.Nonempty := h.image _

theorem suspendEdge_prod (s : ℕ) (e : Finset V) (y : Fin s → ℝ) (x : V → ℝ) :
    (∏ v ∈ suspendEdge s e, Sum.elim y x v) =
      (∏ i, y i) * ∏ v ∈ e, x v := by
  rw [suspendEdge, Finset.prod_union (suspendEdge_disjoint s e)]
  simp

/-- Exact factorization, valid even for zero or signed weights. -/
theorem suspension_polynomial (G : RGraph V 3) (s : ℕ) (y : Fin s → ℝ) (x : V → ℝ) :
    (G.suspension s).edgePolynomial (Sum.elim y x) =
      (∏ i, y i) * G.edgePolynomial x := by
  unfold edgePolynomial suspension
  rw [Finset.sum_image (fun a _ b _ h => suspendEdge_injective s h)]
  simp only [suspendEdge_prod, Finset.mul_sum]

end TuranUniversality.RGraph
