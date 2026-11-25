/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

/-!
# Finite averages for the product selector

All expectations here are uniform averages on finite types. The identities
are proved from finite sums and do not assume a spectral estimate.
-/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

variable {α β γ : Type*}

/-- Uniform average of a real-valued function on a finite type. -/
noncomputable def mean [Fintype α] (f : α → ℝ) : ℝ := 𝔼 x, f x

/-- Uniform second moment. -/
noncomputable def energy [Fintype α] (f : α → ℝ) : ℝ := mean fun x => f x ^ 2

theorem mean_eq_sum_div_card [Fintype α] (f : α → ℝ) :
    mean f = (∑ x, f x) / Fintype.card α := Fintype.expect_eq_sum_div_card f

@[simp] theorem mean_zero [Fintype α] : mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]

@[simp] theorem mean_const [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := Fintype.expect_const c

@[simp] theorem mean_add [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ _ _

@[simp] theorem mean_sub [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ _ _

@[simp] theorem mean_mul_const [Fintype α] (f : α → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c := (Finset.expect_mul _ _ _).symm

@[simp] theorem mean_const_mul [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := (Finset.mul_expect _ _ _).symm

theorem mean_congr [Fintype α] {f g : α → ℝ} (h : ∀ x, f x = g x) :
    mean f = mean g := congrArg mean (funext h)

theorem mean_comm [Fintype α] [Fintype β] (f : α → β → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  exact Finset.expect_comm _ _ _

theorem mean_prod [Fintype α] [Fintype β] (f : α × β → ℝ) :
    mean f = mean (fun x => mean (fun y => f (x, y))) := by
  simpa [mean] using Finset.expect_product Finset.univ Finset.univ f

theorem mean_nonneg [Fintype α] {f : α → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ mean f := Finset.expect_nonneg (fun x _ => h x)

theorem mean_mono [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    mean f ≤ mean g := Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonneg [Fintype α] (f : α → ℝ) : 0 ≤ energy f :=
  mean_nonneg fun x => sq_nonneg (f x)

theorem mean_mul_sq_le [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x * g x) ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq _ _ _

theorem mean_sq_le_energy [Fintype α] [Nonempty α] (f : α → ℝ) :
    mean f ^ 2 ≤ energy f := by
  simpa [energy] using mean_mul_sq_le f (fun _ => 1)

theorem centered_mean [Fintype α] [Nonempty α] (f : α → ℝ) :
    mean (fun x => f x - mean f) = 0 := by simp

theorem energy_centered [Fintype α] [Nonempty α] (f : α → ℝ) :
    energy (fun x => f x - mean f) = energy f - mean f ^ 2 := by
  unfold energy
  calc
    mean (fun x => (f x - mean f) ^ 2) =
        mean (fun x => f x ^ 2 - (2 * mean f) * f x + mean f ^ 2) :=
      mean_congr fun x => by ring
    _ = mean (fun x => f x ^ 2) - mean f ^ 2 := by simp; ring

theorem mean_affine_sq [Fintype α] [Nonempty α]
    (c r : ℝ) (f : α → ℝ) :
    mean (fun x => (c - r * f x) ^ 2) =
      c ^ 2 - 2 * c * r * mean f + r ^ 2 * energy f := by
  calc
    mean (fun x => (c - r * f x) ^ 2) =
        mean (fun x => c ^ 2 - (2 * c * r) * f x + r ^ 2 * f x ^ 2) :=
      mean_congr fun x => by ring
    _ = c ^ 2 - 2 * c * r * mean f + r ^ 2 * energy f := by
      simp [energy]

theorem row_residual_energy [Fintype α] [Nonempty α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun i => energy (fun x => f i x - mean (fun j => f j x))) =
      mean (fun i => energy (f i)) - energy (fun x => mean (fun i => f i x)) := by
  unfold energy
  rw [mean_comm]
  calc
    mean (fun x => mean (fun i => (f i x - mean (fun j => f j x)) ^ 2)) =
        mean (fun x => mean (fun i => f i x ^ 2) - mean (fun i => f i x) ^ 2) := by
      apply mean_congr
      intro x
      exact energy_centered (fun i => f i x)
    _ = mean (fun i => mean (fun x => f i x ^ 2)) -
        mean (fun x => mean (fun i => f i x) ^ 2) := by
      rw [mean_sub, mean_comm (fun x i => f i x ^ 2)]

/-- A real-linear map commutes with finite uniform averaging. -/
theorem linearMap_mean [Fintype α]
    (T : (β → ℝ) →ₗ[ℝ] (γ → ℝ)) (f : α → β → ℝ) :
    T (fun x => mean (fun i => f i x)) = fun y => mean (fun i => T (f i) y) := by
  have heq : (fun x => mean (fun i => f i x)) =
      (Fintype.card α : ℝ)⁻¹ • ∑ i, f i := by
    ext x
    simp [mean_eq_sum_div_card, div_eq_mul_inv, mul_comm]
  rw [heq, map_smul, map_sum]
  ext y
  simp [mean_eq_sum_div_card, div_eq_mul_inv, mul_comm]

end TuranUniversality.Selector
