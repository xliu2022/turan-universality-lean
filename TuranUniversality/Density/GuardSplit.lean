module

public import TuranUniversality.Density.CompleteWeighted
public import TuranUniversality.Density.CliqueBound
public import TuranUniversality.Hypergraph.Guard
public import TuranUniversality.Weighted.Coarse

@[expose] public section

/-! # Splitting a guard-free weighted graph at a clique hitting set -/

namespace TuranUniversality.Weighted.RootedModel

open scoped BigOperators

variable {Roots Data : Type*} [DecidableEq Roots] [Fintype Roots]
  [DecidableEq Data] [Fintype Data]

def dataGraph (M : RootedModel Roots Data) : RGraph Data 3 where
  edges := M.dataTriples
  uniform := M.dataTriples_uniform

theorem dataGraph_isHom (M : RootedModel Roots Data) :
    M.dataGraph.IsHom M.toRGraph Sum.inr := by
  intro e he
  apply Finset.mem_image.mpr
  refine ⟨(∅, e), (M.mem_dataTriples e).mp he, ?_⟩
  simp [Finset.map_eq_image]
  rfl

theorem contribution_two_complete_bound (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card Roots ≤ k) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) :
    M.contribution 2 z x ≤ (1 - 1 / (k : ℝ)) * (∑ r, z r) ^ 2 * (∑ d, x d) / 2 := by
  have hlocal (d : Data) : (∑ p ∈ M.rootLink d, ∏ r ∈ p, z r) ≤
      (1 - 1 / (k : ℝ)) * (∑ r, z r) ^ 2 / 2 := by
    apply le_trans (b := elementary Finset.univ z 2)
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, M.rootLink_uniform d p hp⟩
      · exact fun p _ _ => Finset.prod_nonneg fun r _ => hz r
    · exact complete_pairs_card_le _ _ k hk (by simpa using hcard)
  rw [M.contribution_two_eq]
  calc
    _ ≤ ∑ d, x d * ((1 - 1 / (k : ℝ)) * (∑ r, z r) ^ 2 / 2) :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hlocal d) (hx d)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem split_clique_bound (M : RootedModel Roots Data)
    (z : Roots → ℝ) (x : Data → ℝ) (k t : ℕ) (hk : 12 ≤ k) (ht : 3 ≤ t)
    (hcard : Fintype.card Roots ≤ k) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d)
    (hfree : (RGraph.clique (Fin t) 3).HomFree M.dataGraph) :
    6 * M.toRGraph.edgePolynomial (Sum.elim z x) ≤
      6 * coeffA k * (∑ r, z r) ^ 3 +
        3 * (1 - 1 / (k : ℝ)) * (∑ r, z r) ^ 2 * (∑ d, x d) +
        3 * (∑ r, z r) * (∑ d, x d) ^ 2 +
        (1 - 1 / (t.choose 3 : ℝ)) * (∑ d, x d) ^ 3 := by
  have h3 := (M.contribution_three_le_complete z x hz).trans
    (complete_triples_card_le Finset.univ z k hk (by simpa using hcard) (fun r _ => hz r))
  have h2 := M.contribution_two_complete_bound z x k (by omega) hcard hz hx
  have h1 := M.contribution_one_coarse_bound z x hz hx
  have h0 := M.dataGraph.clique_free_weighted_mass_bound ht hfree x hx
  have hzero : M.contribution 0 z x = M.dataGraph.edgePolynomial x := M.contribution_zero_eq z x
  rw [M.edgePolynomial_four_shapes]
  rw [← hzero] at h0
  linarith

end TuranUniversality.Weighted.RootedModel

namespace TuranUniversality.RGraph

open Weighted
open scoped BigOperators

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem guard_polynomial_split (G : RGraph V 3) {s t : ℕ}
    (ht : 3 ≤ t) (hk : 12 ≤ t * (s - 1))
    (hfree : ¬ ∃ f, (cliquePacking s t).IsEmbedding G f)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    ∃ a u : ℝ, 0 ≤ a ∧ 0 ≤ u ∧ a + u = 1 ∧
      6 * G.edgePolynomial x ≤ 6 * coeffA (t * (s - 1) : ℕ) * a ^ 3 +
        3 * (1 - 1 / (t * (s - 1) : ℕ)) * a ^ 2 * u + 3 * a * u ^ 2 +
        (1 - 1 / (t.choose 3 : ℝ)) * u ^ 3 := by
  classical
  obtain ⟨S, hsize, hhit⟩ := G.guard_hitting_set (by omega : 0 < t) hfree
  let R := {v : V // v ∈ S}
  let D := {v : V // v ∉ S}
  let e : R ⊕ D ≃ V := Equiv.Set.sumCompl (S : Set V)
  let J := G.pullback e.toEmbedding
  let M := RootedModel.ofRGraph J
  let z : R → ℝ := fun r => x r.val
  let w : D → ℝ := fun d => x d.val
  have heweights : Sum.elim z w = x ∘ e := by funext v; cases v <;> rfl
  have hpoly : M.toRGraph.edgePolynomial (Sum.elim z w) = G.edgePolynomial x := by
    rw [heweights, RootedModel.toRGraph_ofRGraph]
    exact G.pullback_equiv_polynomial e x
  have hsum : (∑ r, z r) + (∑ d, w d) = 1 := by
    calc
      _ = ∑ v : R ⊕ D, Sum.elim z w v := (Fintype.sum_sum_type _).symm
      _ = ∑ v : V, x v := Fintype.sum_equiv e _ _ (fun v => congrFun heweights v)
      _ = 1 := hx.2
  have hf : M.dataGraph.IsHom G Subtype.val := by
    have hm := M.dataGraph_isHom
    rw [RootedModel.toRGraph_ofRGraph] at hm
    exact (G.pullback_isHom e.toEmbedding).comp hm
  have hclqfree : (clique (Fin t) 3).HomFree M.dataGraph := by
    rintro ⟨f, h⟩
    have hfg := hf.comp h
    have hinj := (clique_coversPairs (V := Fin t) (by omega : 2 ≤ 3)
      (by simpa using ht)).hom_injective hfg
    have hclq := IsCliqueSet.of_embedding G ⟨hinj, hfg⟩
    apply hhit _ hclq
    apply Finset.disjoint_left.mpr
    intro v hv hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (f j).property hS
  have hb := M.split_clique_bound z w (t * (s - 1)) t hk ht
    (by simpa [R] using hsize) (fun r => hx.1 r.val) (fun d => hx.1 d.val) hclqfree
  rw [hpoly] at hb
  exact ⟨∑ r, z r, ∑ d, w d,
    Finset.sum_nonneg (fun r _ => hx.1 r.val), Finset.sum_nonneg (fun d _ => hx.1 d.val), hsum, hb⟩

end TuranUniversality.RGraph
