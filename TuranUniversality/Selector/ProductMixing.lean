/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.FiniteAverages

/-!
# Mixing on finite products

We prove the contraction estimate by splitting each function into its
coordinate average and its mean-zero remainder. Iteration gives the
product estimate without assuming an operator norm or a spectral theorem.
-/

@[expose] public section

namespace TuranUniversality.Selector

open scoped BigOperators

variable {α β : Type*}

@[simp] theorem map_fun_add (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (f g : β → ℝ) (y : β) :
    T (fun x => f x + g x) y = T f y + T g y :=
  congrFun (T.map_add f g) y

@[simp] theorem map_fun_sub (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (f g : β → ℝ) (y : β) :
    T (fun x => f x - g x) y = T f y - T g y :=
  congrFun (map_sub T f g) y

@[simp] theorem map_fun_mul (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (c : ℝ) (f : β → ℝ) (y : β) :
    T (fun x => c * f x) y = c * T f y :=
  congrFun (map_smul T c f) y

/-- The sharp second-moment bound with contraction factor `r` away from
constant functions. -/
def MixingBound [Fintype β] (r : ℝ) (T : (β → ℝ) →ₗ[ℝ] (β → ℝ)) : Prop :=
  ∀ f, energy (T f) ≤ r ^ 2 * energy f + (1 - r ^ 2) * mean f ^ 2

theorem MixingBound.energy_le [Fintype β] [Nonempty β]
    {r : ℝ} {T : (β → ℝ) →ₗ[ℝ] (β → ℝ)}
    (hT : MixingBound r T) (hr : r ^ 2 ≤ 1) (f : β → ℝ) :
    energy (T f) ≤ energy f := by
  calc
    energy (T f) ≤ r ^ 2 * energy f + (1 - r ^ 2) * mean f ^ 2 := hT f
    _ ≤ r ^ 2 * energy f + (1 - r ^ 2) * energy f :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (mean_sq_le_energy f)
        (sub_nonneg.mpr hr))
    _ = energy f := by ring

/-- Add a coordinate whose centered part is multiplied by `-r`. -/
noncomputable def tensorStep [Fintype α] (r : ℝ)
    (T : (β → ℝ) →ₗ[ℝ] (β → ℝ)) :
    (α × β → ℝ) →ₗ[ℝ] (α × β → ℝ) where
  toFun f p := T (fun y => mean (fun i => f (i, y))) p.2 -
    r * (T (fun y => f (p.1, y)) p.2 - T (fun y => mean (fun i => f (i, y))) p.2)
  map_add' f g := by
    funext p
    simp only [Pi.add_apply, mean_add, map_fun_add]
    ring
  map_smul' c f := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, mean_const_mul, map_fun_mul,
      RingHom.id_apply]
    ring

theorem tensorStep_apply [Fintype α] (r : ℝ)
    (T : (β → ℝ) →ₗ[ℝ] (β → ℝ)) (f : α × β → ℝ) (p : α × β) :
    tensorStep r T f p = T (fun y => mean (fun i => f (i, y))) p.2 -
      r * (T (fun y => f (p.1, y)) p.2 -
        T (fun y => mean (fun i => f (i, y))) p.2) := rfl

theorem tensorStep_energy [Fintype α] [Nonempty α] [Fintype β]
    (r : ℝ) (T : (β → ℝ) →ₗ[ℝ] (β → ℝ)) (f : α × β → ℝ) :
    energy (tensorStep r T f) =
      energy (T (fun y => mean (fun i => f (i, y)))) +
        r ^ 2 * mean (fun i => energy (T (fun y =>
          f (i, y) - mean (fun j => f (j, y))))) := by
  let g : β → ℝ := fun y => mean (fun i => f (i, y))
  let B : α → β → ℝ := fun i => T (fun y => f (i, y) - g y)
  have hzero : (fun y => mean (fun i => f (i, y) - g y)) = 0 := by
    funext y
    simp [g]
  have hB (y : β) : mean (fun i => B i y) = 0 := by
    have h := congrArg (fun k : β → ℝ => k y)
      (linearMap_mean T (fun i y => f (i, y) - g y))
    rw [hzero, map_zero] at h
    exact h.symm
  have hstep (p : α × β) : tensorStep r T f p = T g p.2 - r * B p.1 p.2 := by
    simp [tensorStep_apply, B, g]
  change mean (fun p => tensorStep r T f p ^ 2) =
    energy (T g) + r ^ 2 * mean (fun i => energy (B i))
  simp_rw [hstep]
  rw [mean_prod, mean_comm]
  calc
    mean (fun y => mean (fun i => (T g y - r * B i y) ^ 2)) =
        mean (fun y => (T g y) ^ 2 + r ^ 2 * energy (fun i => B i y)) := by
      apply mean_congr
      intro y
      rw [mean_affine_sq, hB]
      ring
    _ = energy (T g) + r ^ 2 * mean (fun i => energy (B i)) := by
      simp only [mean_add, mean_const_mul, energy]
      rw [mean_comm (fun y i => B i y ^ 2)]

theorem tensorStep_mean [Fintype α] [Nonempty α] [Fintype β]
    (r : ℝ) (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (hT : ∀ f, mean (T f) = mean f) (f : α × β → ℝ) :
    mean (tensorStep r T f) = mean f := by
  let g : β → ℝ := fun y => mean (fun i => f (i, y))
  have hcomm (y : β) : mean (fun i => T (fun x => f (i, x)) y) = T g y := by
    exact (congrArg (fun k : β → ℝ => k y) (linearMap_mean T (fun i x => f (i, x)))).symm
  rw [mean_prod, mean_comm]
  simp only [tensorStep_apply]
  change mean (fun y => mean (fun i => T g y -
    r * (T (fun x => f (i, x)) y - T g y))) = mean f
  simp only [mean_sub, mean_const, mean_const_mul, hcomm, sub_self, mul_zero, sub_zero]
  rw [hT]
  change mean (fun y => mean (fun i => f (i, y))) = mean f
  rw [mean_comm]
  exact (mean_prod f).symm

theorem tensorStep_const [Fintype α] [Nonempty α]
    (r : ℝ) (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (hT : ∀ c, T (fun _ => c) = fun _ => c) (c : ℝ) :
    tensorStep r T (fun _ : α × β => c) = fun _ => c := by
  funext p
  simp [tensorStep_apply, hT]

theorem tensorStep_bound [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    {r : ℝ} (T : (β → ℝ) →ₗ[ℝ] (β → ℝ))
    (hr : r ^ 2 ≤ 1) (hT : MixingBound r T) :
    MixingBound r (tensorStep (α := α) r T) := by
  intro f
  let g : β → ℝ := fun y => mean (fun i => f (i, y))
  have hrow : mean (fun i => energy (fun y => f (i, y))) = energy f := by
    exact (mean_prod (fun p => f p ^ 2)).symm
  have hmean : mean g = mean f := by
    change mean (fun y => mean (fun i => f (i, y))) = mean f
    rw [mean_comm]
    exact (mean_prod f).symm
  calc
    energy (tensorStep r T f) = energy (T g) +
        r ^ 2 * mean (fun i => energy (T (fun y => f (i, y) - g y))) :=
      tensorStep_energy r T f
    _ ≤ (r ^ 2 * energy g + (1 - r ^ 2) * mean g ^ 2) +
        r ^ 2 * mean (fun i => energy (fun y => f (i, y) - g y)) := by
      apply add_le_add (hT g)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
      apply mean_mono
      intro i
      exact hT.energy_le hr _
    _ = r ^ 2 * energy f + (1 - r ^ 2) * mean f ^ 2 := by
      rw [row_residual_energy (fun i y => f (i, y)), hrow, hmean]
      change r ^ 2 * energy g + (1 - r ^ 2) * mean f ^ 2 +
        r ^ 2 * (energy f - energy g) = _
      ring

universe u

/-- A recursively presented finite word, convenient for induction on the
number of coordinates. -/
@[reducible] def Words (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × Words α n

instance wordsFintype [Fintype α] (n : ℕ) : Fintype (Words α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (α × Words α n))

instance wordsNonempty [Nonempty α] (n : ℕ) : Nonempty (Words α n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty PUnit)
  | succ n ih =>
      let := ih
      exact inferInstanceAs (Nonempty (α × Words α n))

/-- Tensor powers of the map that fixes constants and multiplies the
centered part in each coordinate by `-r`. -/
noncomputable def productNoise [Fintype α] (r : ℝ) :
    (n : ℕ) → (Words α n → ℝ) →ₗ[ℝ] (Words α n → ℝ)
  | 0 => LinearMap.id
  | n + 1 => tensorStep r (productNoise r n)

theorem productNoise_mean [Fintype α] [Nonempty α] (r : ℝ) (n : ℕ)
    (f : Words α n → ℝ) : mean (productNoise r n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => exact tensorStep_mean r (productNoise r n) ih f

theorem productNoise_const [Fintype α] [Nonempty α] (r : ℝ) (n : ℕ) (c : ℝ) :
    productNoise (α := α) r n (fun _ => c) = fun _ => c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact tensorStep_const r (productNoise r n) ih c

theorem productNoise_bound [Fintype α] [Nonempty α]
    (r : ℝ) (hr : r ^ 2 ≤ 1) (n : ℕ) : MixingBound r (productNoise (α := α) r n) := by
  induction n with
  | zero =>
      intro f
      have hf : f = fun _ => f PUnit.unit := by
        funext x
        cases x
        rfl
      rw [hf]
      simp only [productNoise, LinearMap.id_coe, id_eq, energy, mean_const]
      exact le_of_eq (by ring)
  | succ n ih => exact tensorStep_bound (productNoise r n) hr ih

end TuranUniversality.Selector
