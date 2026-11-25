module

public import TuranUniversality.Structural.BlockSupports
public import TuranUniversality.Structural.Record
public import TuranUniversality.Uniformity.Suspension
public import Mathlib.Data.Finset.Sum

@[expose] public section

/-! # Ordinary hypergraphs compiled from actual records

The carrier separates suspension vertices, five-point blocks, and data.
Every recorded four-set is expanded by precisely its assigned word pool.
The construction includes all supports of an available record and does not
create any new data records.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Compiled

variable {V : Type*} [DecidableEq V]

abbrev Vertex (b t : ℕ) (V : Type*) := Fin t ⊕ (Support.Vertex b ⊕ V)

def edge {b : ℕ} (t : ℕ) (Z : Finset (Support.Vertex b)) (X : Finset V) :
    Finset (Vertex b t V) := RGraph.suspendEdge t (Z.disjSum X)

@[simp] theorem mem_edge_susp {b t : ℕ} (Z : Finset (Support.Vertex b))
    (X : Finset V) (i : Fin t) : Sum.inl i ∈ edge t Z X := by
  simp [edge]

@[simp] theorem mem_edge_block {b t : ℕ} (Z : Finset (Support.Vertex b))
    (X : Finset V) (v : Support.Vertex b) :
    Sum.inr (Sum.inl v) ∈ edge t Z X ↔ v ∈ Z := by
  simp [edge]

@[simp] theorem mem_edge_data {b t : ℕ} (Z : Finset (Support.Vertex b))
    (X : Finset V) (v : V) : Sum.inr (Sum.inr v) ∈ edge t Z X ↔ v ∈ X := by
  simp [edge]

theorem edge_card {b : ℕ} (t : ℕ) (Z : Finset (Support.Vertex b)) (X : Finset V) :
    (edge t Z X).card = t + (Z.card + X.card) := by
  simp [edge, RGraph.suspendEdge_card]

theorem edge_injective {b t : ℕ} :
    Function.Injective (fun p : Finset (Support.Vertex b) × Finset V => edge t p.1 p.2) := by
  intro a c h
  apply Prod.ext
  · apply Finset.ext
    intro v
    have hv := congrArg (fun e : Finset (Vertex b t V) => Sum.inr (Sum.inl v) ∈ e) h
    simpa using hv
  · apply Finset.ext
    intro v
    have hv := congrArg (fun e : Finset (Vertex b t V) => Sum.inr (Sum.inr v) ∈ e) h
    simpa using hv

def graph {b : ℕ} (t : ℕ) (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V) :
    RGraph (Vertex b t V) (t + (3 * b + 4)) where
  edges := R.recorded.edges.biUnion fun X =>
    (Support.poolGraph (Ω (R.label X))).edges.image (fun Z => edge t Z X)
  uniform := by
    intro e he
    obtain ⟨X, hX, hXe⟩ := Finset.mem_biUnion.mp he
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hXe
    rw [edge_card, (Support.poolGraph _).uniform Z hZ, R.recorded.uniform X hX]

theorem mem_graph {b t : ℕ} (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (e : Finset (Vertex b t V)) :
    e ∈ (graph t Ω R).edges ↔
      ∃ X ∈ R.recorded.edges, ∃ Z ∈ (Support.poolGraph (Ω (R.label X))).edges,
        edge t Z X = e := by
  simp [graph]

theorem edge_prod {b t : ℕ} (Z : Finset (Support.Vertex b)) (X : Finset V)
    (x : Vertex b t V → ℝ) :
    (∏ v ∈ edge t Z X, x v) =
      (∏ i : Fin t, x (.inl i)) *
        (∏ v ∈ Z, x (.inr (.inl v))) * ∏ v ∈ X, x (.inr (.inr v)) := by
  have hx : x = Sum.elim (fun i => x (.inl i)) (fun v => x (.inr v)) := by
    funext v; cases v <;> rfl
  rw [edge, hx, RGraph.suspendEdge_prod]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_disjSum]
  ring

theorem support_expansions_disjoint {b t : ℕ} (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) {X Y : Finset V} (hXY : X ≠ Y) :
    Disjoint ((Support.poolGraph (Ω (R.label X))).edges.image (fun Z => edge t Z X))
      ((Support.poolGraph (Ω (R.label Y))).edges.image (fun Z => edge t Z Y)) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨Z, _, hZ⟩ := Finset.mem_image.mp he
  obtain ⟨W, _, hW⟩ := Finset.mem_image.mp hf
  have hp : (Z, X) = (W, Y) := edge_injective (hZ.trans hW.symm)
  exact hXY (congrArg Prod.snd hp)

/-- The exact edge polynomial, before any inequality or optimization. -/
theorem polynomial {b t : ℕ} (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (x : Vertex b t V → ℝ) :
    (graph t Ω R).edgePolynomial x =
      (∏ i : Fin t, x (.inl i)) * ∑ X ∈ R.recorded.edges,
        (Support.poolGraph (Ω (R.label X))).edgePolynomial (fun v => x (.inr (.inl v))) *
          ∏ v ∈ X, x (.inr (.inr v)) := by
  unfold RGraph.edgePolynomial graph
  rw [Finset.sum_biUnion (fun X _ Y _ h => support_expansions_disjoint Ω R h),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X hX
  have hinj : Function.Injective (fun Z : Finset (Support.Vertex b) => edge t Z X) := by
    intro Z W h
    have hp : (Z, X) = (W, X) := edge_injective h
    exact congrArg Prod.fst hp
  rw [Finset.sum_image (fun Z _ W _ h => hinj h), Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Z hZ
  rw [edge_prod]
  ring

/-- The common support bound, still with the actual integer pool sizes. -/
theorem polynomial_le {b t : ℕ} (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem V)
    (x : Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    (graph t Ω R).edgePolynomial x ≤
      (∏ i : Fin t, x (.inl i)) *
        ((1 / 25 : ℝ) ^ b * ∏ i : Fin b, Support.blockMass (fun v => x (.inr (.inl v))) i ^ 3) *
        ∑ X ∈ R.recorded.edges, ((Ω (R.label X)).card : ℝ) * ∏ v ∈ X, x (.inr (.inr v)) := by
  rw [polynomial]
  calc
    _ ≤ (∏ i : Fin t, x (.inl i)) * ∑ X ∈ R.recorded.edges,
        (((Ω (R.label X)).card : ℝ) *
          ((1 / 25 : ℝ) ^ b * ∏ i : Fin b, Support.blockMass (fun v => x (.inr (.inl v))) i ^ 3)) *
          ∏ v ∈ X, x (.inr (.inr v)) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hx _)
      apply Finset.sum_le_sum
      intro X hX
      exact mul_le_mul_of_nonneg_right
        (Support.poolGraph_le _ _ (fun v => hx _)) (Finset.prod_nonneg fun v _ => hx _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X hX
      ring

end TuranUniversality.Structural.Compiled
