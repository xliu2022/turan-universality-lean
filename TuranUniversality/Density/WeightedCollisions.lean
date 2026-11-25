module

public import TuranUniversality.Density.WeightedHom
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Distinct sampling with a subprobability weighting

No normalization or positive total mass is needed. The weight of repeated
samples is bounded by the second moment, using an ordered-pair union bound.
Consequently distinct `k`-samples have asymptotic weight equal to the `k`th
power of their total mass whenever the second moment tends to zero.
-/

open scoped BigOperators

namespace TuranUniversality.Density

variable {A B V : Type*}
variable [DecidableEq V]

theorem sum_productWeight_mass [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) :
    (∑ f : A → V, productWeight x f) = (∑ v, x v) ^ Fintype.card A := by
  classical
  have h := Finset.prod_univ_sum (fun _ : A => (Finset.univ : Finset V))
    (fun _ v => x v)
  simpa [productWeight] using h.symm

theorem weightedMean_restrict_mass [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Fintype V]
    (x : V → ℝ) (i : A → B) (hi : Function.Injective i) (F : (A → V) → ℝ) :
    weightedMean x (fun f : B → V => F (f ∘ i)) =
      weightedMean x F * (∑ v, x v) ^ (Fintype.card B - Fintype.card A) := by
  classical
  let D := {b : B // b ∉ Set.range i}
  let e : A ⊕ D ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective i hi) (Equiv.refl D)).trans
      (Equiv.Set.sumCompl (Set.range i))
  let q : (B → V) ≃ (A → V) × (D → V) :=
    (Equiv.arrowCongr e.symm (Equiv.refl V)).trans
      (Equiv.sumArrowEquivProdArrow A D V)
  have hq (f : B → V) : (q f).1 = f ∘ i := rfl
  have hc : Fintype.card D = Fintype.card B - Fintype.card A := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_sum] at h
    omega
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
    _ = ∑ a : A → V,
        (productWeight x a * F a) * (∑ v, x v) ^ Fintype.card D := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ d : D → V, (productWeight x a * productWeight x d) * F a) =
            (productWeight x a * F a) * ∑ d : D → V, productWeight x d := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
        _ = _ := by rw [sum_productWeight_mass]
    _ = _ := by rw [← Finset.sum_mul, hc]

theorem weightedMean_pair_equal [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (i j : A) (hij : i ≠ j) :
    weightedMean x (fun f : A → V => if f i = f j then (1 : ℝ) else 0) =
      (∑ v, (x v) ^ 2) * (∑ v, x v) ^ (Fintype.card A - 2) := by
  classical
  let a : Fin 2 → A := ![i, j]
  have ha : Function.Injective a := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all [a, eq_comm]
  have h := weightedMean_restrict_mass x a ha
    (fun f : Fin 2 → V => if f 0 = f 1 then (1 : ℝ) else 0)
  have ht : weightedMean x (fun f : Fin 2 → V => if f 0 = f 1 then (1 : ℝ) else 0) =
      ∑ v, (x v) ^ 2 := by
    unfold weightedMean
    calc
      _ = ∑ p : V × V, (x p.1 * x p.2) * if p.1 = p.2 then (1 : ℝ) else 0 := by
        apply Fintype.sum_equiv (finTwoArrowEquiv V)
        intro f
        simp [productWeight, Fin.prod_univ_two, finTwoArrowEquiv]
      _ = _ := by
        simp [Fintype.sum_prod_type, mul_ite, sq]
  simpa only [Function.comp_apply, a, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Fintype.card_fin, ht] using h

noncomputable def distinctWeight [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) : ℝ :=
  weightedMean x (fun f : A → V => if Function.Injective f then 1 else 0)

theorem distinctWeight_eq_sum [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) :
    distinctWeight (A := A) x = ∑ f : {f : A → V // Function.Injective f}, productWeight x f.val := by
  classical
  unfold distinctWeight weightedMean
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_subtype _
    (p := fun f : A → V => Function.Injective f)
    (by intro f; simp only [Finset.mem_filter, Finset.mem_univ, true_and])]

theorem distinctWeight_deficit [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) :
    (∑ v, x v) ^ Fintype.card A - distinctWeight (A := A) x =
      weightedMean x (fun f : A → V => if ¬ Function.Injective f then (1 : ℝ) else 0) := by
  classical
  rw [← sum_productWeight_mass (A := A) x]
  unfold distinctWeight weightedMean
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : Function.Injective f <;> simp [hf]

/-- A convenient uniform collision estimate for arbitrary finite sample types. -/
theorem distinctWeight_subprob_bounds [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (hs : ∑ v, x v ≤ 1) :
    0 ≤ (∑ v, x v) ^ Fintype.card A - distinctWeight (A := A) x ∧
      (∑ v, x v) ^ Fintype.card A - distinctWeight (A := A) x ≤
        (Fintype.card A : ℝ) ^ 2 * ∑ v, (x v) ^ 2 := by
  classical
  rw [distinctWeight_deficit]
  let E (p : A × A) (f : A → V) : ℝ :=
    if p.1 ≠ p.2 ∧ f p.1 = f p.2 then 1 else 0
  have hE (p : A × A) (f : A → V) : 0 ≤ E p f := by unfold E; split <;> norm_num
  refine ⟨Finset.sum_nonneg (fun f _ => mul_nonneg
    (Finset.prod_nonneg fun _ _ => hx _) (by dsimp only; split <;> norm_num)), ?_⟩
  have hp (f : A → V) :
      (if ¬ Function.Injective f then (1 : ℝ) else 0) ≤ ∑ p : A × A, E p f := by
    by_cases hf : Function.Injective f
    · simp only [hf, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun p _ => hE p f)
    · have hn := hf
      simp only [Function.Injective, not_forall] at hn
      obtain ⟨i, j, hij, hne⟩ := hn
      have h := Finset.single_le_sum (fun p _ => hE p f) (Finset.mem_univ (i, j))
      simpa [hf, E, hne, hij] using h
  have hmean (p : A × A) : weightedMean x (E p) ≤ ∑ v, (x v) ^ 2 := by
    by_cases hp : p.1 = p.2
    · simp only [E, hp, ne_eq, not_true_eq_false, false_and, ite_false,
        weightedMean, mul_zero, Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun v _ => sq_nonneg _)
    · have he : E p = fun f : A → V => if f p.1 = f p.2 then (1 : ℝ) else 0 := by
        funext f
        simp [E, hp]
      rw [he, weightedMean_pair_equal x _ _ hp]
      have hpw : (∑ v, x v) ^ (Fintype.card A - 2) ≤ 1 :=
        pow_le_one₀ (Finset.sum_nonneg fun v _ => hx v) hs
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpw
        (Finset.sum_nonneg fun v _ => sq_nonneg (x v))
  calc
    _ ≤ weightedMean x (fun f : A → V => ∑ p : A × A, E p f) :=
      weightedMean_mono x hx hp
    _ = ∑ p : A × A, weightedMean x (E p) := weightedMean_sum x _ _
    _ ≤ ∑ _p : A × A, ∑ v, (x v) ^ 2 := Finset.sum_le_sum (fun p _ => hmean p)
    _ = _ := by simp [Fintype.card_prod, pow_two]

end TuranUniversality.Density
