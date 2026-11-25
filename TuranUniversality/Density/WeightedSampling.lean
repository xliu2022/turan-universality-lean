module

public import TuranUniversality.Density.EdgeDensity
public import TuranUniversality.Density.Averages

@[expose] public section

/-! # Independent finite samples with arbitrary real probability weights -/

open scoped BigOperators

namespace TuranUniversality.Density

variable {A B V : Type*}

def productWeight [Fintype A] (x : V → ℝ) (f : A → V) : ℝ := ∏ a, x (f a)

def weightedMean [Fintype A] [DecidableEq A] [Fintype V] (x : V → ℝ) (F : (A → V) → ℝ) : ℝ :=
  ∑ f, productWeight x f * F f

theorem sum_productWeight [Fintype A] [DecidableEq A] [Fintype V] (x : V → ℝ)
    (hx : ∑ v, x v = 1) : (∑ f : A → V, productWeight x f) = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : A => (Finset.univ : Finset V))
    (fun _ v => x v)
  simpa [hx, productWeight] using h.symm

theorem weightedMean_const [Fintype A] [DecidableEq A] [Fintype V] (x : V → ℝ)
    (hx : ∑ v, x v = 1) (c : ℝ) : weightedMean (A := A) x (fun _ => c) = c := by
  unfold weightedMean
  rw [← Finset.sum_mul, sum_productWeight x hx, one_mul]

theorem weightedMean_mono [Fintype A] [DecidableEq A] [Fintype V] (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) {F G : (A → V) → ℝ} (h : ∀ f, F f ≤ G f) :
    weightedMean x F ≤ weightedMean x G := by
  apply Finset.sum_le_sum
  intro f _
  exact mul_le_mul_of_nonneg_left (h f) (Finset.prod_nonneg fun _ _ => hx _)

theorem weightedMean_congr [Fintype A] [DecidableEq A] [Fintype V] (x : V → ℝ)
    {F G : (A → V) → ℝ} (h : ∀ f, F f = G f) : weightedMean x F = weightedMean x G := by
  unfold weightedMean
  exact Finset.sum_congr rfl fun f _ => congrArg (productWeight x f * ·) (h f)

theorem weightedMean_sum [Fintype A] [DecidableEq A] [Fintype V] {I : Type*}
    (x : V → ℝ) (s : Finset I) (F : I → (A → V) → ℝ) :
    weightedMean x (fun f => ∑ i ∈ s, F i f) = ∑ i ∈ s, weightedMean x (F i) := by
  simp only [weightedMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem weightedMean_restrict_injective [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Fintype V]
    (x : V → ℝ) (hx : ∑ v, x v = 1)
    (i : A → B) (hi : Function.Injective i) (F : (A → V) → ℝ) :
    weightedMean x (fun f : B → V => F (f ∘ i)) = weightedMean x F := by
  classical
  let D := {b : B // b ∉ Set.range i}
  let e : A ⊕ D ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective i hi) (Equiv.refl D)).trans
      (Equiv.Set.sumCompl (Set.range i))
  let q : (B → V) ≃ (A → V) × (D → V) :=
    (Equiv.arrowCongr e.symm (Equiv.refl V)).trans
      (Equiv.sumArrowEquivProdArrow A D V)
  have hq (f : B → V) : (q f).1 = f ∘ i := rfl
  have hw (f : B → V) : productWeight x f =
      productWeight x (q f).1 * productWeight x (q f).2 := by
    unfold productWeight
    calc
      (∏ b, x (f b)) = ∏ a : A ⊕ D, x (f (e a)) :=
        (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
      _ = _ := by rw [Fintype.prod_sum_type]; rfl
  unfold weightedMean
  calc
    (∑ f : B → V, productWeight x f * F (f ∘ i)) =
        ∑ p : (A → V) × (D → V),
          (productWeight x p.1 * productWeight x p.2) * F p.1 := by
      apply Fintype.sum_equiv q
      intro f
      rw [hw, hq]
    _ = ∑ a : A → V, ∑ d : D → V,
        (productWeight x a * productWeight x d) * F a := Fintype.sum_prod_type _
    _ = ∑ a : A → V, productWeight x a * F a := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ d : D → V, (productWeight x a * productWeight x d) * F a) =
            (productWeight x a * F a) * ∑ d : D → V, productWeight x d := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
        _ = _ := by rw [sum_productWeight x hx, mul_one]

end TuranUniversality.Density

namespace TuranUniversality.RGraph

open Density

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem orderingFunction_weight (G : RGraph V r) (p : EdgeOrdering G) (x : V → ℝ) :
    productWeight x (G.orderingFunction p) = ∏ v ∈ p.1.val, x v := by
  unfold productWeight orderingFunction
  calc
    (∏ j, x (p.2 j).val) = ∏ v : p.1.val, x v.val :=
      Fintype.prod_equiv p.2 _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort _ _

theorem weightedMean_oneEdge (G : RGraph V r) (x : V → ℝ) :
    weightedMean x ((oneEdge r).homIndicator G) =
      (r.factorial : ℝ) * G.edgePolynomial x := by
  classical
  unfold weightedMean homIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_subtype _
    (p := fun f : Fin r → V => (oneEdge r).IsHom G f) (by intro f; simp only
      [Finset.mem_filter, Finset.mem_univ, true_and])]
  calc
    (∑ f : {f : Fin r → V // (oneEdge r).IsHom G f}, productWeight x f.val) =
        ∑ p : EdgeOrdering G, productWeight x (G.orderingFunction p) := by
      symm
      apply Fintype.sum_equiv (Equiv.ofBijective G.orderedEdgeMap G.orderedEdgeMap_bijective)
      intro p
      rfl
    _ = ∑ p : EdgeOrdering G, ∏ v ∈ p.1.val, x v :=
      Finset.sum_congr rfl (fun p _ => G.orderingFunction_weight p x)
    _ = (r.factorial : ℝ) * G.edgePolynomial x := by
      rw [Fintype.sum_sigma]
      have hc (e : G.edges) : Fintype.card (Fin r ≃ e.val) = r.factorial := by
        have he : Fintype.card (Fin r) = Fintype.card e.val := by
          simp [G.uniform _ e.property]
        rw [Fintype.card_equiv (Fintype.equivOfCardEq he), Fintype.card_fin]
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort G.edges (fun e : Finset V => ∏ v ∈ e, x v)

end TuranUniversality.RGraph
