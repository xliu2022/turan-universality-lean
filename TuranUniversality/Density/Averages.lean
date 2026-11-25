module

public import TuranUniversality.Selector.FiniteAverages
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-! # Finite uniform sampling identities -/

open scoped BigOperators

namespace TuranUniversality.Density

open Selector

variable {A B C : Type*}

/-- Uniformly random values on a finite set restrict to uniformly random
values on any injected subset of coordinates. -/
theorem mean_restrict_injective [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype C] [Nonempty C] (i : A → B) (hi : Function.Injective i)
    (F : (A → C) → ℝ) :
    mean (fun f : B → C => F (f ∘ i)) = mean F := by
  classical
  let D := {b : B // b ∉ Set.range i}
  let e : A ⊕ D ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective i hi) (Equiv.refl D)).trans
      (Equiv.Set.sumCompl (Set.range i))
  let q : (B → C) ≃ (A → C) × (D → C) :=
    (Equiv.arrowCongr e.symm (Equiv.refl C)).trans
      (Equiv.sumArrowEquivProdArrow A D C)
  have hq (f : B → C) : (q f).1 = f ∘ i := rfl
  calc
    mean (fun f : B → C => F (f ∘ i)) =
        mean (fun p : (A → C) × (D → C) => F p.1) := by
      apply Fintype.expect_equiv q
      intro f
      rw [hq]
    _ = mean (fun a : A → C => mean (fun _b : D → C => F a)) :=
      mean_prod _
    _ = mean F := by simp

/-- Jensen's power inequality for a finite uniform average. -/
theorem mean_pow_le [Fintype A] [Nonempty A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) (s : ℕ) :
    mean f ^ s ≤ mean (fun a => f a ^ s) := by
  classical
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hweights : (∑ _a : A, (Fintype.card A : ℝ)⁻¹) = 1 := by
    simp [ne_of_gt hn]
  have h := (convexOn_pow s).map_sum_le
    (t := Finset.univ) (w := fun _a : A => (Fintype.card A : ℝ)⁻¹)
    (p := f) (fun _ _ => inv_nonneg.mpr hn.le) hweights (fun a _ => hf a)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  simpa only [mean_eq_sum_div_card, div_eq_mul_inv, mul_comm] using h

/-- Independent uniform samples agree with probability the reciprocal of
the size of the finite sample space. -/
theorem mean_equal_pair [Fintype C] [Nonempty C] [DecidableEq C] :
    mean (fun p : C × C => if p.1 = p.2 then (1 : ℝ) else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
  rw [mean_prod]
  have h (c : C) : mean (fun d : C => if c = d then (1 : ℝ) else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
    simp [mean_eq_sum_div_card]
  simp_rw [h]
  exact mean_const _

/-- Two different coordinates in a random function are independent uniform
samples. -/
theorem mean_equal_coordinates [Fintype A] [DecidableEq A]
    [Fintype C] [Nonempty C] [DecidableEq C]
    (u v : A) (huv : u ≠ v) :
    mean (fun f : A → C => if f u = f v then (1 : ℝ) else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
  classical
  let i : Bool → A := fun b => bif b then v else u
  have hi : Function.Injective i := by
    intro a b h
    cases a <;> cases b <;> simp_all [i]
  calc
    mean (fun f : A → C => if f u = f v then (1 : ℝ) else 0) =
        mean (fun g : Bool → C => if g false = g true then (1 : ℝ) else 0) := by
      simpa only [Function.comp_apply, i, Bool.cond_false, Bool.cond_true] using
        mean_restrict_injective i hi
          (fun g : Bool → C => if g false = g true then (1 : ℝ) else 0)
    _ = mean (fun p : C × C => if p.1 = p.2 then (1 : ℝ) else 0) := by
      apply Fintype.expect_equiv (Equiv.boolArrowEquivProd C)
      intro f
      rfl
    _ = _ := mean_equal_pair

end TuranUniversality.Density
