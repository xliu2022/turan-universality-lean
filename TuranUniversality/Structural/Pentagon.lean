module

public import TuranUniversality.Hypergraph.Polynomial
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # The two pentagon codes

The actual five-vertex three-graphs of Lemma 8.1.  The square identity is
verified as a polynomial identity; the equality case uses every nonnegative
summand, including the possibility of zero vertex weights.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Pentagon

/-- The cyclic consecutive triples on five vertices. -/
def P0 : RGraph (Fin 5) 3 where
  edges := {{0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {0, 3, 4}, {0, 1, 4}}
  uniform := by decide

/-- The complementary five triples. -/
def P1 : RGraph (Fin 5) 3 where
  edges := {{0, 1, 3}, {0, 2, 3}, {0, 2, 4}, {1, 2, 4}, {1, 3, 4}}
  uniform := by decide

theorem P1_complement :
    P1.edges = (Finset.univ : Finset (Fin 5)).powersetCard 3 \ P0.edges := by
  decide

theorem P0_card : P0.edges.card = 5 := by decide
theorem P1_card : P1.edges.card = 5 := by decide

/-- Multiplication by two in the cyclic group of order five. -/
def doublePerm : Fin 5 ≃ Fin 5 where
  toFun i := 2 * i
  invFun i := 3 * i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem doublePerm_edges :
    P0.edges.image (fun e => e.image doublePerm) = P1.edges := by decide

theorem P0_cyclic :
    P0.edges = Finset.univ.image (fun i : Fin 5 => ({i, i + 1, i + 2} : Finset (Fin 5))) := by
  decide

def graph (phase : Bool) : RGraph (Fin 5) 3 := if phase then P1 else P0

def mass (x : Fin 5 → ℝ) : ℝ := ∑ i, x i

theorem P0_polynomial (x : Fin 5 → ℝ) :
    P0.edgePolynomial x = x 0 * x 1 * x 2 + x 1 * x 2 * x 3 +
      x 2 * x 3 * x 4 + x 0 * x 3 * x 4 + x 0 * x 1 * x 4 := by
  simp (disch := decide) only [P0, RGraph.edgePolynomial, Finset.sum_insert,
    Finset.sum_singleton, Finset.prod_insert, Finset.prod_singleton]
  ring

theorem P1_polynomial (x : Fin 5 → ℝ) :
    P1.edgePolynomial x = x 0 * x 1 * x 3 + x 0 * x 2 * x 3 +
      x 0 * x 2 * x 4 + x 1 * x 2 * x 4 + x 1 * x 3 * x 4 := by
  simp (disch := decide) only [P1, RGraph.edgePolynomial, Finset.sum_insert,
    Finset.sum_singleton, Finset.prod_insert, Finset.prod_singleton]
  ring

theorem P1_polynomial_doublePerm (x : Fin 5 → ℝ) :
    P1.edgePolynomial x = P0.edgePolynomial (x ∘ doublePerm) := by
  rw [P1_polynomial, P0_polynomial]
  norm_num [Function.comp_def, doublePerm]
  ring

theorem mass_doublePerm (x : Fin 5 → ℝ) : mass (x ∘ doublePerm) = mass x := by
  exact doublePerm.sum_comp x

/-- One nonnegative summand in the paper's sum of squares. -/
def squareTerm (x : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  x i * ((5 * x i - mass x) ^ 2 +
    5 * (x (i + 1) + x (i - 1) - x (i + 2) - x (i - 2)) ^ 2 +
    50 * (x (i + 1) - x (i - 1) - x (i + 2) + x (i - 2)) ^ 2)

/-- The exact identity (8.1), valid without a sign hypothesis. -/
theorem squares_identity (x : Fin 5 → ℝ) :
    400 * (mass x ^ 3 / 25 - P0.edgePolynomial x) = ∑ i, squareTerm x i := by
  rw [P0_polynomial]
  have hn1 : (-1 : Fin 5) = 4 := rfl
  have hn2 : (-2 : Fin 5) = 3 := rfl
  norm_num [squareTerm, mass, Fin.sum_univ_succ, hn1, hn2]
  simp only [hn1, hn2]
  ring

theorem squareTerm_nonneg {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) (i : Fin 5) :
    0 ≤ squareTerm x i := by
  apply mul_nonneg (hx i)
  positivity

theorem P0_polynomial_le {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    P0.edgePolynomial x ≤ mass x ^ 3 / 25 := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    squareTerm_nonneg hx i)
  rw [← squares_identity] at h
  linarith

theorem uniform_polynomial (phase : Bool) (c : ℝ) :
    (graph phase).edgePolynomial (fun _ => c) = 5 * c ^ 3 := by
  cases phase <;> simp [graph, RGraph.edgePolynomial_uniform, P0_card, P1_card]

theorem P0_eq_iff {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) (hs : 0 < mass x) :
    P0.edgePolynomial x = mass x ^ 3 / 25 ↔ ∀ i, x i = mass x / 5 := by
  constructor
  · intro heq
    have hsum : (∑ i, squareTerm x i) = 0 := by rw [← squares_identity, heq]; ring
    have hterm (i : Fin 5) : squareTerm x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => squareTerm_nonneg hx j)).mp hsum i
        (Finset.mem_univ i)
    have hle (i : Fin 5) : x i ≤ mass x / 5 := by
      by_cases hi : x i = 0
      · rw [hi]; positivity
      · have hinner := (mul_eq_zero.mp (hterm i)).resolve_left hi
        have hsq : (5 * x i - mass x) ^ 2 = 0 := by
          nlinarith [sq_nonneg (5 * x i - mass x),
            sq_nonneg (x (i + 1) + x (i - 1) - x (i + 2) - x (i - 2)),
            sq_nonneg (x (i + 1) - x (i - 1) - x (i + 2) + x (i - 2))]
        nlinarith [sq_nonneg (5 * x i - mass x)]
    have htot : (∑ i, x i) = ∑ _i : Fin 5, mass x / 5 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change mass x = _
      ring
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp htot i
      (Finset.mem_univ i)
  · intro hxuniform
    have he : x = fun _ => mass x / 5 := funext hxuniform
    calc
      P0.edgePolynomial x = P0.edgePolynomial (fun _ => mass x / 5) := congrArg _ he
      _ = mass x ^ 3 / 25 := by rw [RGraph.edgePolynomial_uniform, P0_card]; norm_num; ring

/-- Lemma 8.1: the same sharp bound for both actual code graphs. -/
theorem edgePolynomial_le (phase : Bool) {x : Fin 5 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (graph phase).edgePolynomial x ≤ mass x ^ 3 / 25 := by
  cases phase
  · exact P0_polynomial_le hx
  · change P1.edgePolynomial x ≤ _
    rw [P1_polynomial_doublePerm, ← mass_doublePerm x]
    exact P0_polynomial_le (fun i => hx (doublePerm i))

/-- At positive total mass, equality requires all five weights to be equal. -/
theorem edgePolynomial_eq_iff (phase : Bool) {x : Fin 5 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : 0 < mass x) :
    (graph phase).edgePolynomial x = mass x ^ 3 / 25 ↔
      ∀ i, x i = mass x / 5 := by
  cases phase
  · exact P0_eq_iff hx hs
  · change P1.edgePolynomial x = _ ↔ _
    rw [P1_polynomial_doublePerm, ← mass_doublePerm x]
    have hs' : 0 < mass (x ∘ doublePerm) := by rw [mass_doublePerm]; exact hs
    rw [P0_eq_iff (x := x ∘ doublePerm) (fun i => hx (doublePerm i)) hs']
    constructor
    · intro h i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h (doublePerm.symm i)
    · intro h i
      exact h (doublePerm i)

end TuranUniversality.Structural.Pentagon
