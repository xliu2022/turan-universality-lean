module

public import TuranUniversality.Hypergraph.Twins

@[expose] public section

/-! # Vertex degrees and genuine link hypergraphs -/

open scoped BigOperators

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] {r : ℕ}

def degree (G : RGraph V r) (v : V) : ℕ :=
  (G.edges.filter (fun e => v ∈ e)).card

theorem erase_injective_on_star (G : RGraph V r) (v : V) :
    Set.InjOn (fun e : Finset V => e.erase v) (G.edges.filter (fun e => v ∈ e)) := by
  intro e he d hd hed
  change e.erase v = d.erase v at hed
  have he' := (Finset.mem_filter.mp he).2
  have hd' := (Finset.mem_filter.mp hd).2
  calc
    e = insert v (e.erase v) := (Finset.insert_erase he').symm
    _ = insert v (d.erase v) := by rw [hed]
    _ = d := Finset.insert_erase hd'

theorem card_link (G : RGraph V r) (v : V) : (G.link v).card = G.degree v :=
  Finset.card_image_of_injOn (G.erase_injective_on_star v)

theorem sum_degrees [Fintype V] (G : RGraph V r) :
    ∑ v, G.degree v = r * G.edges.card := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ G.edges, ∑ v : V, if v ∈ e then 1 else 0) = ∑ e ∈ G.edges, e.card := by
      apply Finset.sum_congr rfl
      intro e _
      simp
    _ = ∑ _e ∈ G.edges, r := Finset.sum_congr rfl (fun e he => G.uniform e he)
    _ = _ := by simp [mul_comm]

def linkGraph (G : RGraph V r) (v : V) : RGraph V (r - 1) where
  edges := G.link v
  uniform s hs := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
    rw [Finset.card_erase_of_mem hv, G.uniform e he]

theorem linkGraph_polynomial (G : RGraph V r) (x : V → ℝ) (v : V) :
    (G.linkGraph v).edgePolynomial x = G.linkPolynomial x v := by
  unfold linkGraph edgePolynomial linkPolynomial link
  rw [Finset.sum_image]
  exact G.erase_injective_on_star v

theorem linkPolynomial_uniform (G : RGraph V r) (v : V) (c : ℝ) :
    G.linkPolynomial (fun _ => c) v = (G.degree v : ℝ) * c ^ (r - 1) := by
  rw [← G.linkGraph_polynomial, (G.linkGraph v).edgePolynomial_uniform]
  exact congrArg (fun n : ℕ => (n : ℝ) * c ^ (r - 1)) (G.card_link v)

theorem linkPolynomial_nonneg (G : RGraph V r) {x : V → ℝ} (hx : ∀ v, 0 ≤ x v)
    (v : V) : 0 ≤ G.linkPolynomial x v := by
  rw [← G.linkGraph_polynomial]
  exact (G.linkGraph v).edgePolynomial_nonneg hx

end TuranUniversality.RGraph
