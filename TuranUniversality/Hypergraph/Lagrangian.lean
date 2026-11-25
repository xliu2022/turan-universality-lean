module

public import TuranUniversality.Hypergraph.Polynomial
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

/-! # The normalized Lagrangian of a finite uniform hypergraph

The supremum ranges over every real probability weighting. Inserting zero
sets the value on an empty vertex type to zero. For a nonempty finite vertex
type the supremum is attained, so this definition agrees with the usual
maximum of `r!` times the edge polynomial.
-/

open scoped BigOperators

namespace TuranUniversality

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

theorem ProbabilityWeights.apply_le_one {x : V → ℝ} (hx : ProbabilityWeights x) (v : V) :
    x v ≤ 1 := by
  calc
    x v ≤ ∑ w, x w := Finset.single_le_sum (fun w _ => hx.1 w) (Finset.mem_univ v)
    _ = 1 := hx.2

theorem probabilityWeights_isCompact : IsCompact {x : V → ℝ | ProbabilityWeights x} := by
  have hclosed : IsClosed {x : V → ℝ | ProbabilityWeights x} := by
    have hi : IsClosed (⋂ v : V, {x : V → ℝ | 0 ≤ x v}) :=
      isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
    have he : IsClosed {x : V → ℝ | ∑ v, x v = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    convert hi.inter he using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, ProbabilityWeights]
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : V → ℝ)) (b := 1)) hclosed
  intro x hx
  exact ⟨hx.1, fun v => hx.apply_le_one v⟩

theorem probabilityWeights_nonempty [Nonempty V] :
    ({x : V → ℝ | ProbabilityWeights x} : Set (V → ℝ)).Nonempty := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨fun w => if w = v then 1 else 0, ?_⟩
  constructor
  · intro w
    by_cases h : w = v <;> simp [h]
  · simp

namespace RGraph

variable {r : ℕ}

/-- All normalized values of real probability weightings, with zero included
to give a canonical empty-vertex convention. -/
def lagrangianValues (G : RGraph V r) : Set ℝ :=
  insert 0 {z | ∃ x : V → ℝ, ProbabilityWeights x ∧
    z = (r.factorial : ℝ) * G.edgePolynomial x}

theorem zero_mem_lagrangianValues (G : RGraph V r) : 0 ∈ G.lagrangianValues :=
  Set.mem_insert _ _

theorem lagrangianValues_nonempty (G : RGraph V r) : G.lagrangianValues.Nonempty :=
  ⟨0, G.zero_mem_lagrangianValues⟩

theorem edgePolynomial_le_edge_card (G : RGraph V r) (x : V → ℝ)
    (hx : ProbabilityWeights x) : G.edgePolynomial x ≤ (G.edges.card : ℝ) := by
  calc
    G.edgePolynomial x ≤ ∑ _e ∈ G.edges, (1 : ℝ) :=
      Finset.sum_le_sum fun e _ =>
        Finset.prod_le_one₀ (fun v _ => hx.1 v) (fun v _ => hx.apply_le_one v)
    _ = _ := by simp

theorem lagrangianValues_bddAbove (G : RGraph V r) : BddAbove G.lagrangianValues := by
  refine ⟨(r.factorial : ℝ) * G.edges.card, ?_⟩
  intro z hz
  rcases hz with rfl | ⟨x, hx, rfl⟩
  · positivity
  · exact mul_le_mul_of_nonneg_left (G.edgePolynomial_le_edge_card x hx) (Nat.cast_nonneg _)

/-- The normalized finite-graph Lagrangian, including all real weightings. -/
noncomputable def lagrangian (G : RGraph V r) : ℝ := sSup G.lagrangianValues

theorem lagrangian_nonneg (G : RGraph V r) : 0 ≤ G.lagrangian :=
  le_csSup G.lagrangianValues_bddAbove G.zero_mem_lagrangianValues

theorem normalizedPolynomial_le_lagrangian (G : RGraph V r)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ G.lagrangian :=
  le_csSup G.lagrangianValues_bddAbove (Or.inr ⟨x, hx, rfl⟩)

/-- Strict excess over a nonnegative threshold is exactly the existence of
a strictly improving real probability weighting, including at empty order. -/
theorem lt_lagrangian_iff (G : RGraph V r) {b : ℝ} (hb : 0 ≤ b) :
    b < G.lagrangian ↔ ∃ x : V → ℝ, ProbabilityWeights x ∧
      b < (r.factorial : ℝ) * G.edgePolynomial x := by
  rw [lagrangian, lt_csSup_iff G.lagrangianValues_bddAbove G.lagrangianValues_nonempty]
  constructor
  · rintro ⟨z, hz, hs⟩
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact ((not_lt_of_ge hb) hs).elim
    · exact ⟨x, hx, hs⟩
  · rintro ⟨x, hx, hs⟩
    exact ⟨_, Or.inr ⟨x, hx, rfl⟩, hs⟩

theorem lagrangian_le_iff (G : RGraph V r) {b : ℝ} (hb : 0 ≤ b) :
    G.lagrangian ≤ b ↔ ∀ x : V → ℝ, ProbabilityWeights x →
      (r.factorial : ℝ) * G.edgePolynomial x ≤ b := by
  constructor
  · intro h x hx
    exact (G.normalizedPolynomial_le_lagrangian x hx).trans h
  · intro h
    apply csSup_le G.lagrangianValues_nonempty
    intro z hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact hb
    · exact h x hx

/-- On a nonempty finite vertex type, a maximizing real weighting exists. -/
theorem exists_lagrangian_maximizer [Nonempty V] (G : RGraph V r) :
    ∃ x : V → ℝ, ProbabilityWeights x ∧
      (r.factorial : ℝ) * G.edgePolynomial x = G.lagrangian := by
  have hc : Continuous (fun x : V → ℝ => (r.factorial : ℝ) * G.edgePolynomial x) := by
    unfold edgePolynomial
    fun_prop
  obtain ⟨x, hx, hmax⟩ := probabilityWeights_isCompact.exists_isMaxOn
    probabilityWeights_nonempty hc.continuousOn
  refine ⟨x, hx, le_antisymm (G.normalizedPolynomial_le_lagrangian x hx) ?_⟩
  apply (G.lagrangian_le_iff
    (mul_nonneg (Nat.cast_nonneg _) (G.edgePolynomial_nonneg hx.1))).mpr
  intro y hy
  exact hmax hy

@[simp] theorem lagrangian_of_isEmpty [IsEmpty V] (G : RGraph V r) : G.lagrangian = 0 := by
  apply le_antisymm ((G.lagrangian_le_iff (le_refl 0)).mpr ?_) G.lagrangian_nonneg
  intro x hx
  have hsum := hx.2
  simp at hsum

end RGraph
end TuranUniversality
