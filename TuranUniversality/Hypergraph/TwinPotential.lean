module

public import TuranUniversality.Hypergraph.Clone
public import Mathlib.Data.Finset.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The finite twin-class potential

The potential counts ordered pairs with equal actual links. It therefore
equals the sum of squares of the twin-class sizes, without choosing a
partition or discarding isolated vertices. Cloning into an at least as large
twin class strictly increases it whenever the edge count is unchanged.
-/

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

def twinClass (G : RGraph V r) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.link w = G.link v)

@[simp] theorem mem_twinClass (G : RGraph V r) (u v : V) :
    u ∈ G.twinClass v ↔ G.link u = G.link v := by simp [twinClass]

@[simp] theorem self_mem_twinClass (G : RGraph V r) (v : V) : v ∈ G.twinClass v := by simp

def twinPairs (G : RGraph V r) : Finset (V × V) :=
  Finset.univ.filter (fun p => G.link p.1 = G.link p.2)

def twinPotential (G : RGraph V r) : ℕ := G.twinPairs.card

def twinPairsAway (G : RGraph V r) (v : V) : Finset (V × V) :=
  (G.twinPairs.filter (fun p => p.1 ≠ v)).filter (fun p => p.2 ≠ v)

theorem twinPotential_le (G : RGraph V r) :
    G.twinPotential ≤ Fintype.card V ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset (V × V)))
    (p := fun p => G.link p.1 = G.link p.2))
  simpa only [twinPotential, twinPairs, Finset.card_univ, Fintype.card_prod, pow_two] using h

theorem twinPotential_away (G : RGraph V r) (u : V) :
    G.twinPotential + 1 = (G.twinPairsAway u).card + 2 * (G.twinClass u).card := by
  have hfirst : G.twinPairs.filter (fun p => p.1 = u) =
      Finset.product ({u} : Finset V) (G.twinClass u) := by
    ext ⟨a, b⟩
    simp only [twinPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton, mem_twinClass]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨rfl, h.symm⟩
    · rintro ⟨rfl, h⟩
      exact ⟨h.symm, rfl⟩
  have hsecond : (G.twinPairs.filter (fun p => p.1 ≠ u)).filter (fun p => p.2 = u) =
      Finset.product ((G.twinClass u).erase u) ({u} : Finset V) := by
    ext ⟨a, b⟩
    simp only [twinPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_erase, mem_twinClass]
    by_cases h : b = u
    · simp [h, and_comm]
    · simp [h]
  have h₁ := Finset.card_filter_add_card_filter_not (s := G.twinPairs) (fun p => p.1 = u)
  have h₂ := Finset.card_filter_add_card_filter_not
    (s := G.twinPairs.filter (fun p => p.1 ≠ u)) (fun p => p.2 = u)
  rw [hfirst, Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul] at h₁
  rw [hsecond, Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, mul_one] at h₂
  have he := Finset.card_erase_add_one (G.self_mem_twinClass u)
  change ((G.twinClass u).erase u).card + (G.twinPairsAway u).card =
    (G.twinPairs.filter (fun p => p.1 ≠ u)).card at h₂
  change (G.twinClass u).card + (G.twinPairs.filter (fun p => p.1 ≠ u)).card =
    G.twinPotential at h₁
  omega

theorem clone_twinPairsAway (G : RGraph V r) (u v : V) :
    G.twinPairsAway u ⊆ (G.clone u v).twinPairsAway u := by
  intro p hp
  simp only [twinPairsAway, twinPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨⟨G.clone_preserves_twins u v hp.1.2 hp.2 hp.1.1, hp.1.2⟩, hp.2⟩

theorem clone_twinClass_grows (G : RGraph V r) {u v : V}
    (hne : G.link u ≠ G.link v) :
    (G.twinClass v).card + 1 ≤ ((G.clone u v).twinClass u).card := by
  have hu : u ∉ G.twinClass v := by simpa using hne
  have huv : v ≠ u := fun h => hne (h ▸ rfl)
  have hsub : insert u (G.twinClass v) ⊆ (G.clone u v).twinClass u := by
    intro w hw
    rcases Finset.mem_insert.mp hw with hw | hw
    · subst w
      exact (G.clone u v).self_mem_twinClass u
    · apply ((G.clone u v).mem_twinClass _ _).mpr
      have hwu : w ≠ u := fun h => hu (h ▸ hw)
      exact (G.clone_preserves_twins u v hwu huv ((G.mem_twinClass _ _).mp hw)).trans
        (G.clone_twins u v).symm
  simpa only [Finset.card_insert_of_notMem hu] using Finset.card_le_card hsub

theorem clone_twinPotential_increases (G : RGraph V r) {u v : V}
    (hne : G.link u ≠ G.link v) (hc : (G.twinClass u).card ≤ (G.twinClass v).card) :
    G.twinPotential + 2 ≤ (G.clone u v).twinPotential := by
  have h₁ := G.twinPotential_away u
  have h₂ := (G.clone u v).twinPotential_away u
  have ha := Finset.card_le_card (G.clone_twinPairsAway u v)
  have hb := G.clone_twinClass_grows hne
  omega

/-- A natural-number encoding of lexicographic edge count and twin
potential. The base exceeds the largest possible twin potential. -/
def cloneScore (G : RGraph V r) : ℕ :=
  G.edges.card * (Fintype.card V ^ 2 + 1) + G.twinPotential

theorem cloneScore_lt_of_edges_lt (G H : RGraph V r) (h : G.edges.card < H.edges.card) :
    G.cloneScore < H.cloneScore := by
  have hm := Nat.mul_le_mul_right (Fintype.card V ^ 2 + 1) (Nat.succ_le_of_lt h)
  have hp := G.twinPotential_le
  dsimp [cloneScore]
  nlinarith

theorem cloneScore_lt_of_same_edges (G H : RGraph V r) (he : G.edges.card = H.edges.card)
    (hp : G.twinPotential < H.twinPotential) : G.cloneScore < H.cloneScore := by
  simp only [cloneScore, he]
  exact Nat.add_lt_add_left hp _

theorem exists_clone_improvement (G : RGraph V r) (hG : ¬ G.Symmetrized) :
    ∃ u v : V, u ≠ v ∧ (¬ ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e) ∧
      G.edges.card ≤ (G.clone u v).edges.card ∧ G.cloneScore < (G.clone u v).cloneScore := by
  classical
  unfold Symmetrized at hG
  push Not at hG
  obtain ⟨u, v, hp, ht⟩ := hG
  have hp : ¬ ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e := by
    rintro ⟨e, he, hu, hv⟩
    exact hp e he hu hv
  have hstep (a b : V) (hab : G.link a ≠ G.link b)
      (hpab : ¬ ∃ e ∈ G.edges, a ∈ e ∧ b ∈ e)
      (hd : G.degree a < G.degree b ∨
        G.degree a = G.degree b ∧ (G.twinClass a).card ≤ (G.twinClass b).card) :
      G.edges.card ≤ (G.clone a b).edges.card ∧ G.cloneScore < (G.clone a b).cloneScore := by
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    have he := G.clone_card_edges hne hpab
    rcases hd with hd | ⟨hd, hc⟩
    · have hstrict : G.edges.card < (G.clone a b).edges.card := by omega
      exact ⟨hstrict.le, G.cloneScore_lt_of_edges_lt _ hstrict⟩
    · have heq : G.edges.card = (G.clone a b).edges.card := by omega
      have hstrict : G.twinPotential < (G.clone a b).twinPotential :=
        lt_of_lt_of_le (by omega) (G.clone_twinPotential_increases hab hc)
      exact ⟨heq.le, G.cloneScore_lt_of_same_edges _ heq hstrict⟩
  by_cases hd : G.degree u < G.degree v
  · exact ⟨u, v, fun h => ht (h ▸ rfl), hp, hstep u v ht hp (Or.inl hd)⟩
  by_cases he : G.degree u = G.degree v
  · by_cases hc : (G.twinClass u).card ≤ (G.twinClass v).card
    · exact ⟨u, v, fun h => ht (h ▸ rfl), hp, hstep u v ht hp (Or.inr ⟨he, hc⟩)⟩
    · have hp' : ¬ ∃ e ∈ G.edges, v ∈ e ∧ u ∈ e := by simpa only [and_comm] using hp
      exact ⟨v, u, fun h => ht (h ▸ rfl), hp',
        hstep v u (Ne.symm ht) hp' (Or.inr ⟨he.symm, by omega⟩)⟩
  · have hp' : ¬ ∃ e ∈ G.edges, v ∈ e ∧ u ∈ e := by simpa only [and_comm] using hp
    exact ⟨v, u, fun h => ht (h ▸ rfl), hp',
      hstep v u (Ne.symm ht) hp' (Or.inl (by omega))⟩

end TuranUniversality.RGraph
