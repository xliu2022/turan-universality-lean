module

public import TuranUniversality.Hypergraph.Polynomial
public import TuranUniversality.Weighted.Symmetric

/-! # Rooted three-graphs and the four edge contributions

`RootedModel` is an ordinary simple three-graph on the disjoint union of its
root and data vertex types. Its edges are stored as their two projections.
This representation is equivalent to `RGraph (Roots ⊕ Data) 3`, not a
polynomial abstraction or an assumption about the weighted objective.
-/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v

structure RootedModel (Roots : Type u) (Data : Type v)
    [DecidableEq Roots] [DecidableEq Data] where
  edges : Finset (Finset Roots × Finset Data)
  uniform : ∀ p ∈ edges, p.1.card + p.2.card = 3

namespace RootedModel

variable {Roots : Type u} {Data : Type v} [DecidableEq Roots] [DecidableEq Data]

def toRGraph (M : RootedModel Roots Data) : RGraph (Roots ⊕ Data) 3 where
  edges := M.edges.image fun p => p.1.disjSum p.2
  uniform := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    simpa using M.uniform p hp

def ofRGraph (G : RGraph (Roots ⊕ Data) 3) : RootedModel Roots Data where
  edges := G.edges.image fun e => (e.toLeft, e.toRight)
  uniform := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.card_toLeft_add_card_toRight]
    exact G.uniform e he

theorem graph_eq_of_edges (G H : RGraph (Roots ⊕ Data) 3) (h : G.edges = H.edges) : G = H := by
  cases G
  cases H
  cases h
  rfl

@[simp] theorem toRGraph_ofRGraph (G : RGraph (Roots ⊕ Data) 3) :
    (ofRGraph G).toRGraph = G := by
  apply graph_eq_of_edges
  change (G.edges.image (fun e => (e.toLeft, e.toRight))).image
    (fun p => p.1.disjSum p.2) = G.edges
  rw [Finset.image_image]
  simp only [Function.comp_def, Finset.toLeft_disjSum_toRight, Finset.image_id']

omit [DecidableEq Roots] [DecidableEq Data] in
theorem split_edge_injective :
    Function.Injective (fun p : Finset Roots × Finset Data => p.1.disjSum p.2) := by
  intro p q hpq
  exact Prod.ext (Finset.disjSum_inj.mp hpq).1 (Finset.disjSum_inj.mp hpq).2

def term (z : Roots → ℝ) (x : Data → ℝ) (p : Finset Roots × Finset Data) : ℝ :=
  (∏ r ∈ p.1, z r) * ∏ d ∈ p.2, x d

theorem edgePolynomial_split (M : RootedModel Roots Data) (z : Roots → ℝ) (x : Data → ℝ) :
    M.toRGraph.edgePolynomial (Sum.elim z x) = ∑ p ∈ M.edges, term z x p := by
  unfold RGraph.edgePolynomial toRGraph
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    simpa only [term, Sum.elim_inl, Sum.elim_inr] using
      Finset.prod_disjSum p.1 p.2 (Sum.elim z x)
  · intro p hp q hq hpq
    exact split_edge_injective hpq

def contribution (M : RootedModel Roots Data) (k : ℕ) (z : Roots → ℝ) (x : Data → ℝ) : ℝ :=
  ∑ p ∈ M.edges, if p.1.card = k then term z x p else 0

/-- Exact decomposition of the ordinary edge polynomial by number of roots. -/
theorem edgePolynomial_four_shapes (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) :
    M.toRGraph.edgePolynomial (Sum.elim z x) =
      M.contribution 3 z x + M.contribution 2 z x +
        M.contribution 1 z x + M.contribution 0 z x := by
  rw [edgePolynomial_split]
  unfold contribution
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hu := M.uniform p hp
  have hcases : p.1.card = 0 ∨ p.1.card = 1 ∨ p.1.card = 2 ∨ p.1.card = 3 := by omega
  rcases hcases with h | h | h | h <;> simp [h]

theorem contribution_nonneg (M : RootedModel Roots Data) (k : ℕ)
    (z : Roots → ℝ) (x : Data → ℝ) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) :
    0 ≤ M.contribution k z x := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg fun r hr => hz r)
      (Finset.prod_nonneg fun d hd => hx d)
  · rfl

/-- The root-pair link of one data vertex, as an actual finite graph. -/
def rootLink (M : RootedModel Roots Data) (d : Data) : Finset (Finset Roots) :=
  (M.edges.filter fun p => p.2 = {d}).image Prod.fst

/-- The data-pair link of one root vertex, as an actual finite graph. -/
def dataLink (M : RootedModel Roots Data) (r : Roots) : Finset (Finset Data) :=
  (M.edges.filter fun p => p.1 = {r}).image Prod.snd

@[simp] theorem mem_rootLink (M : RootedModel Roots Data) (d : Data) (p : Finset Roots) :
    p ∈ M.rootLink d ↔ (p, {d}) ∈ M.edges := by
  simp only [rootLink, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hp, rfl⟩, rfl⟩
    exact hp
  · intro hp
    exact ⟨p, {d}, ⟨hp, rfl⟩, rfl⟩

@[simp] theorem mem_dataLink (M : RootedModel Roots Data) (r : Roots) (p : Finset Data) :
    p ∈ M.dataLink r ↔ ({r}, p) ∈ M.edges := by
  simp only [dataLink, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hp, rfl⟩, rfl⟩
    exact hp
  · intro hp
    exact ⟨{r}, p, ⟨hp, rfl⟩, rfl⟩

theorem rootLink_uniform (M : RootedModel Roots Data) (d : Data)
    (p : Finset Roots) (hp : p ∈ M.rootLink d) : p.card = 2 := by
  have h := M.uniform (p, {d}) ((M.mem_rootLink d p).mp hp)
  simp only [Finset.card_singleton] at h
  omega

theorem dataLink_uniform (M : RootedModel Roots Data) (r : Roots)
    (p : Finset Data) (hp : p ∈ M.dataLink r) : p.card = 2 := by
  have h := M.uniform ({r}, p) ((M.mem_dataLink r p).mp hp)
  simp only [Finset.card_singleton] at h
  omega

def rootTriples (M : RootedModel Roots Data) : Finset (Finset Roots) :=
  (M.edges.filter fun p => p.2 = ∅).image Prod.fst

def dataTriples (M : RootedModel Roots Data) : Finset (Finset Data) :=
  (M.edges.filter fun p => p.1 = ∅).image Prod.snd

@[simp] theorem mem_rootTriples (M : RootedModel Roots Data) (p : Finset Roots) :
    p ∈ M.rootTriples ↔ (p, ∅) ∈ M.edges := by
  simp only [rootTriples, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hp, rfl⟩, rfl⟩
    exact hp
  · intro hp
    exact ⟨p, ∅, ⟨hp, rfl⟩, rfl⟩

@[simp] theorem mem_dataTriples (M : RootedModel Roots Data) (p : Finset Data) :
    p ∈ M.dataTriples ↔ (∅, p) ∈ M.edges := by
  simp only [dataTriples, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hp, rfl⟩, rfl⟩
    exact hp
  · intro hp
    exact ⟨∅, p, ⟨hp, rfl⟩, rfl⟩

theorem rootTriples_uniform (M : RootedModel Roots Data)
    (p : Finset Roots) (hp : p ∈ M.rootTriples) : p.card = 3 := by
  simpa using M.uniform (p, ∅) ((M.mem_rootTriples p).mp hp)

theorem dataTriples_uniform (M : RootedModel Roots Data)
    (p : Finset Data) (hp : p ∈ M.dataTriples) : p.card = 3 := by
  simpa using M.uniform (∅, p) ((M.mem_dataTriples p).mp hp)

theorem rootLink_weight_eq (M : RootedModel Roots Data) (d : Data) (z : Roots → ℝ) :
    (∑ p ∈ M.rootLink d, ∏ r ∈ p, z r) =
      ∑ p ∈ M.edges, if p.2 = {d} then (∏ r ∈ p.1, z r) else 0 := by
  unfold rootLink
  rw [Finset.sum_image]
  · exact Finset.sum_filter _ _
  · intro p hp q hq hpq
    exact Prod.ext hpq ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)

theorem dataLink_weight_eq (M : RootedModel Roots Data) (r : Roots) (x : Data → ℝ) :
    (∑ p ∈ M.dataLink r, ∏ d ∈ p, x d) =
      ∑ p ∈ M.edges, if p.1 = {r} then (∏ d ∈ p.2, x d) else 0 := by
  unfold dataLink
  rw [Finset.sum_image]
  · exact Finset.sum_filter _ _
  · intro p hp q hq hpq
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) hpq

theorem contribution_three_eq (M : RootedModel Roots Data) (z : Roots → ℝ) (x : Data → ℝ) :
    M.contribution 3 z x = ∑ p ∈ M.rootTriples, ∏ r ∈ p, z r := by
  unfold contribution rootTriples
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hu := M.uniform p hp
    by_cases h3 : p.1.card = 3
    · have hd : p.2 = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [h3, hd, term]
    · have hd : p.2 ≠ ∅ := by
        intro he
        simp only [he, Finset.card_empty, add_zero] at hu
        exact h3 hu
      simp [h3, hd]
  · intro p hp q hq hpq
    exact Prod.ext hpq ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)

theorem contribution_zero_eq (M : RootedModel Roots Data) (z : Roots → ℝ) (x : Data → ℝ) :
    M.contribution 0 z x = ∑ p ∈ M.dataTriples, ∏ d ∈ p, x d := by
  unfold contribution dataTriples
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h0 : p.1.card = 0
    · have hr : p.1 = ∅ := Finset.card_eq_zero.mp h0
      simp [hr, term]
    · have hr : p.1 ≠ ∅ := fun he => h0 (by simp [he])
      simp [h0, hr]
  · intro p hp q hq hpq
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) hpq

theorem contribution_two_eq [Fintype Data] (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) :
    M.contribution 2 z x = ∑ d, x d * ∑ p ∈ M.rootLink d, ∏ r ∈ p, z r := by
  simp_rw [rootLink_weight_eq, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold contribution
  apply Finset.sum_congr rfl
  intro p hp
  have hu := M.uniform p hp
  by_cases h2 : p.1.card = 2
  · have hdcard : p.2.card = 1 := by omega
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hdcard
    simp [h2, hd, term, Finset.singleton_inj, mul_comm]
  · have hd : ∀ d, p.2 ≠ {d} := by
      intro d he
      have hdc : p.2.card = 1 := by simp [he]
      omega
    simp [h2, hd]

theorem contribution_one_eq [Fintype Roots] (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) :
    M.contribution 1 z x = ∑ r, z r * ∑ p ∈ M.dataLink r, ∏ d ∈ p, x d := by
  simp_rw [dataLink_weight_eq, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold contribution
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h1 : p.1.card = 1
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h1
    simp [hr, term, Finset.singleton_inj]
  · have hr : ∀ r, p.1 ≠ {r} := fun r he => h1 (by simp [he])
    simp [h1, hr]

theorem edgePolynomial_links [Fintype Roots] [Fintype Data]
    (M : RootedModel Roots Data) (z : Roots → ℝ) (x : Data → ℝ) :
    M.toRGraph.edgePolynomial (Sum.elim z x) =
      (∑ p ∈ M.rootTriples, ∏ r ∈ p, z r) +
      (∑ d, x d * ∑ p ∈ M.rootLink d, ∏ r ∈ p, z r) +
      (∑ r, z r * ∑ p ∈ M.dataLink r, ∏ d ∈ p, x d) +
      (∑ p ∈ M.dataTriples, ∏ d ∈ p, x d) := by
  rw [edgePolynomial_four_shapes, contribution_three_eq, contribution_two_eq,
    contribution_one_eq, contribution_zero_eq]

theorem contribution_three_le_complete [Fintype Roots] (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (hz : ∀ r, 0 ≤ z r) :
    M.contribution 3 z x ≤ elementary Finset.univ z 3 := by
  rw [contribution_three_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, M.rootTriples_uniform p hp⟩
  · intro p hp hnot
    exact Finset.prod_nonneg fun r hr => hz r

/-- The actual root-only edge contribution satisfies the manuscript's
variance penalty. Missing root vertices can be represented by zero weights. -/
theorem contribution_three_variance_bound [Fintype Roots] (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (hcard : 8 ≤ Fintype.card Roots) (hz : ∀ r, 0 ≤ z r) :
    M.contribution 3 z x ≤ coeffA (Fintype.card Roots) * (∑ r, z r) ^ 3 -
      (∑ r, z r) / 12 * rootVariance Finset.univ z := by
  apply le_trans (contribution_three_le_complete M z x hz)
  simpa using root_triples_variance_bound Finset.univ z (by simpa using hcard)
    (fun r _ => hz r)

end RootedModel

end TuranUniversality.Weighted
