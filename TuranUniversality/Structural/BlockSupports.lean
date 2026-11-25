module

public import TuranUniversality.Structural.CubeBasic
public import TuranUniversality.Structural.Pentagon
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! # Actual root-support hypergraphs for binary word pools

The supports live on disjoint five-vertex blocks. Their ordinary edge sets,
disjointness for different words, exact edge polynomials, common upper bound
and simultaneous averaging property are all proved here.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Support

open Cube

abbrev Vertex (b : ℕ) := (i : Fin b) × Fin 5

def blockGraph {b : ℕ} (w : Word b) (i : Fin b) : RGraph (Fin 5) 3 :=
  Pentagon.graph (decide (i ∈ w))

abbrev Choice {b : ℕ} (w : Word b) := (i : Fin b) → (blockGraph w i).edges

def joinRows {b : ℕ} (es : Fin b → Finset (Fin 5)) : Finset (Vertex b) :=
  Finset.univ.sigma es

@[simp] theorem mem_joinRows {b : ℕ} (es : Fin b → Finset (Fin 5)) (i : Fin b) (j : Fin 5) :
    (⟨i, j⟩ : Vertex b) ∈ joinRows es ↔ j ∈ es i := by
  simp [joinRows]

theorem joinRows_injective {b : ℕ} : Function.Injective (joinRows (b := b)) := by
  intro e f hef
  funext i
  apply Finset.ext
  intro j
  have h := congrArg (fun s : Finset (Vertex b) => (⟨i, j⟩ : Vertex b) ∈ s) hef
  simpa using h

def choiceEdge {b : ℕ} (w : Word b) (e : Choice w) : Finset (Vertex b) :=
  joinRows fun i => (e i).val

theorem choiceEdge_injective {b : ℕ} (w : Word b) : Function.Injective (choiceEdge w) := by
  intro e f hef
  have h := joinRows_injective hef
  funext i
  exact Subtype.ext (congrFun h i)

theorem choiceEdge_card {b : ℕ} (w : Word b) (e : Choice w) :
    (choiceEdge w e).card = 3 * b := by
  have hc (i : Fin b) : (e i).val.card = 3 := (blockGraph w i).uniform _ (e i).property
  simp [choiceEdge, joinRows, Finset.card_sigma, hc, Nat.mul_comm]

def wordGraph {b : ℕ} (w : Word b) : RGraph (Vertex b) (3 * b) where
  edges := Finset.univ.image (choiceEdge w)
  uniform := by
    intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    exact choiceEdge_card w a

@[simp] theorem mem_wordGraph {b : ℕ} (w : Word b) (e : Finset (Vertex b)) :
    e ∈ (wordGraph w).edges ↔ ∃ a : Choice w, choiceEdge w a = e := by
  simp [wordGraph]

theorem pentagon_phase_unique (a c : Bool) (e : Finset (Fin 5))
    (ha : e ∈ (Pentagon.graph a).edges) (hc : e ∈ (Pentagon.graph c).edges) : a = c := by
  have h : ∀ a c : Bool, ∀ e : Finset (Fin 5),
      e ∈ (Pentagon.graph a).edges → e ∈ (Pentagon.graph c).edges → a = c := by decide
  exact h a c e ha hc

theorem word_eq_of_common_edge {b : ℕ} {u v : Word b} {e : Finset (Vertex b)}
    (hu : e ∈ (wordGraph u).edges) (hv : e ∈ (wordGraph v).edges) : u = v := by
  obtain ⟨a, ha⟩ := (mem_wordGraph u e).mp hu
  obtain ⟨c, hc⟩ := (mem_wordGraph v e).mp hv
  have hrows := joinRows_injective (ha.trans hc.symm)
  apply Finset.ext
  intro i
  have hci : (a i).val ∈ (blockGraph v i).edges := by
    rw [congrFun hrows i]
    exact (c i).property
  have hp := pentagon_phase_unique (decide (i ∈ u)) (decide (i ∈ v)) (a i).val
    (a i).property hci
  by_cases hi : i ∈ u <;> by_cases hj : i ∈ v <;> simp_all

theorem wordGraph_disjoint {b : ℕ} {u v : Word b} (h : u ≠ v) :
    Disjoint (wordGraph u).edges (wordGraph v).edges := by
  exact Finset.disjoint_left.mpr fun _ hu hv => h (word_eq_of_common_edge hu hv)

theorem wordGraph_polynomial {b : ℕ} (w : Word b) (x : Vertex b → ℝ) :
    (wordGraph w).edgePolynomial x =
      ∏ i : Fin b, (blockGraph w i).edgePolynomial (fun j => x ⟨i, j⟩) := by
  classical
  unfold RGraph.edgePolynomial wordGraph
  rw [Finset.sum_image (fun a _ c _ h => choiceEdge_injective w h)]
  calc
    (∑ a : Choice w, ∏ v ∈ choiceEdge w a, x v) =
        ∑ a : Choice w, ∏ i : Fin b, ∏ j ∈ (a i).val, x ⟨i, j⟩ := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.prod_sigma _ _ _
    _ = ∏ i : Fin b, ∑ e : (blockGraph w i).edges, ∏ j ∈ e.val, x ⟨i, j⟩ :=
      (Fintype.prod_sum (fun (i : Fin b) (e : (blockGraph w i).edges) =>
        ∏ j ∈ e.val, x ⟨i, j⟩)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact Finset.sum_coe_sort (blockGraph w i).edges (fun e => ∏ j ∈ e, x ⟨i, j⟩)

/-- The union of all disjoint support families in a finite word pool. -/
def poolGraph {b : ℕ} (Ω : Finset (Word b)) : RGraph (Vertex b) (3 * b) where
  edges := Ω.biUnion fun w => (wordGraph w).edges
  uniform := by
    intro e he
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp he
    exact (wordGraph w).uniform e hw

theorem poolGraph_polynomial {b : ℕ} (Ω : Finset (Word b)) (x : Vertex b → ℝ) :
    (poolGraph Ω).edgePolynomial x =
      ∑ w ∈ Ω, ∏ i : Fin b, (blockGraph w i).edgePolynomial (fun j => x ⟨i, j⟩) := by
  classical
  change (∑ e ∈ Ω.biUnion (fun w => (wordGraph w).edges), ∏ v ∈ e, x v) = _
  rw [Finset.sum_biUnion (fun a _ c _ hac => wordGraph_disjoint hac)]
  apply Finset.sum_congr rfl
  intro w _
  exact wordGraph_polynomial w x

def blockMass {b : ℕ} (x : Vertex b → ℝ) (i : Fin b) : ℝ := ∑ j : Fin 5, x ⟨i, j⟩

noncomputable def average {b : ℕ} (x : Vertex b → ℝ) (v : Vertex b) : ℝ := blockMass x v.1 / 5

theorem wordGraph_le {b : ℕ} (w : Word b) (x : Vertex b → ℝ)
    (hx : ∀ v, 0 ≤ x v) :
    (wordGraph w).edgePolynomial x ≤ (1 / 25 : ℝ) ^ b * ∏ i : Fin b, blockMass x i ^ 3 := by
  rw [wordGraph_polynomial]
  calc
    _ ≤ ∏ i : Fin b, (blockMass x i ^ 3 / 25) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact (blockGraph w i).edgePolynomial_nonneg (fun j => hx ⟨i, j⟩)
      · intro i _
        exact Pentagon.edgePolynomial_le _ (fun j => hx ⟨i, j⟩)
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, one_mul]
      ring

theorem wordGraph_average {b : ℕ} (w : Word b) (x : Vertex b → ℝ) :
    (wordGraph w).edgePolynomial (average x) =
      (1 / 25 : ℝ) ^ b * ∏ i : Fin b, blockMass x i ^ 3 := by
  rw [wordGraph_polynomial]
  have h (i : Fin b) : (blockGraph w i).edgePolynomial (fun j => average x ⟨i, j⟩) =
      blockMass x i ^ 3 / 25 := by
    change (Pentagon.graph _).edgePolynomial (fun _ => blockMass x i / 5) = _
    rw [Pentagon.uniform_polynomial]
    ring
  simp only [h, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_mul]
  ring

theorem poolGraph_le {b : ℕ} (Ω : Finset (Word b)) (x : Vertex b → ℝ)
    (hx : ∀ v, 0 ≤ x v) :
    (poolGraph Ω).edgePolynomial x ≤
      (Ω.card : ℝ) * ((1 / 25 : ℝ) ^ b * ∏ i : Fin b, blockMass x i ^ 3) := by
  rw [poolGraph_polynomial]
  calc
    _ ≤ ∑ _w ∈ Ω, ((1 / 25 : ℝ) ^ b * ∏ i : Fin b, blockMass x i ^ 3) := by
      apply Finset.sum_le_sum
      intro w _
      rw [← wordGraph_polynomial]
      exact wordGraph_le w x hx
    _ = _ := by simp

theorem poolGraph_average {b : ℕ} (Ω : Finset (Word b)) (x : Vertex b → ℝ) :
    (poolGraph Ω).edgePolynomial (average x) =
      (Ω.card : ℝ) * ((1 / 25 : ℝ) ^ b * ∏ i : Fin b, blockMass x i ^ 3) := by
  rw [poolGraph_polynomial]
  simp_rw [← wordGraph_polynomial, wordGraph_average]
  simp

/-- Averaging inside each block simultaneously increases every pool value. -/
theorem averaging_increases {b : ℕ} (Ω : Finset (Word b)) (x : Vertex b → ℝ)
    (hx : ∀ v, 0 ≤ x v) :
    (poolGraph Ω).edgePolynomial x ≤ (poolGraph Ω).edgePolynomial (average x) := by
  rw [poolGraph_average]
  exact poolGraph_le Ω x hx

end TuranUniversality.Structural.Support
