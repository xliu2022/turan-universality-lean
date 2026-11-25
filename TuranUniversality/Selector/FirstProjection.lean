/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ProductMixing

/-!
# The first-coordinate projection and the higher-order remainder

The decomposition is constructed recursively from finite coordinate
averages. In particular, the higher-order contraction estimate below is
proved, rather than supplied as an eigenvalue assumption.
-/

@[expose] public section

namespace TuranUniversality.Selector

variable {α β : Type*}

theorem mean_mul_centered [Fintype α] [Nonempty α] (f : α → ℝ) :
    mean (fun x => f x * (f x - mean f)) = energy (fun x => f x - mean f) := by
  rw [energy_centered]
  calc
    mean (fun x => f x * (f x - mean f)) =
        mean (fun x => f x ^ 2 - f x * mean f) := mean_congr fun x => by ring
    _ = energy f - mean f ^ 2 := by simp [energy]; ring

theorem mean_separated_mul [Fintype α] [Fintype β] (u : α → ℝ) (v : β → ℝ) :
    mean (fun p : α × β => u p.1 * v p.2) = mean u * mean v := by
  rw [mean_prod]
  simp

theorem energy_separated_add [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (u : α → ℝ) (v : β → ℝ) :
    energy (fun p : α × β => u p.1 + v p.2) =
      energy u + energy v + 2 * mean u * mean v := by
  unfold energy
  calc
    mean (fun p : α × β => (u p.1 + v p.2) ^ 2) =
        mean (fun p : α × β => u p.1 ^ 2 + v p.2 ^ 2 + 2 * (u p.1 * v p.2)) :=
      mean_congr fun p => by ring
    _ = mean (fun i => u i ^ 2) + mean (fun y => v y ^ 2) +
        2 * mean u * mean v := by
      rw [mean_add, mean_add, mean_const_mul, mean_separated_mul]
      rw [mean_prod (fun p : α × β => u p.1 ^ 2),
        mean_prod (fun p : α × β => v p.2 ^ 2)]
      simp
      ring

theorem mean_mul_row [Fintype α] [Fintype β]
    (f : α × β → ℝ) (u : α → ℝ) :
    mean (fun p => f p * u p.1) = mean (fun i => mean (fun y => f (i, y)) * u i) := by
  rw [mean_prod]
  simp

theorem mean_mul_column [Fintype α] [Fintype β]
    (f : α × β → ℝ) (v : β → ℝ) :
    mean (fun p => f p * v p.2) = mean (fun y => mean (fun i => f (i, y)) * v y) := by
  rw [mean_prod, mean_comm]
  simp

/-- The sum of the centered one-coordinate conditional averages. -/
noncomputable def firstProjection [Fintype α] :
    (d : ℕ) → (Words α d → ℝ) → (Words α d → ℝ)
  | 0, _ => fun _ => 0
  | d + 1, f => fun p =>
      (mean (fun y => f (p.1, y)) - mean f) +
        firstProjection d (fun y => mean (fun i => f (i, y))) p.2

theorem firstProjection_mean [Fintype α] [Nonempty α]
    (d : ℕ) (f : Words α d → ℝ) : mean (firstProjection d f) = 0 := by
  induction d with
  | zero => exact mean_zero
  | succ d ih =>
      change mean (fun p : α × Words α d =>
        (mean (fun y => f (p.1, y)) - mean f) +
          firstProjection d (fun y => mean (fun i => f (i, y))) p.2) = 0
      rw [mean_prod]
      simp only [mean_add, mean_const, ih, add_zero, mean_sub]
      rw [← mean_prod f]
      simp

theorem firstProjection_energy [Fintype α] [Nonempty α]
    (d : ℕ) (f : Words α (d + 1) → ℝ) :
    energy (firstProjection (d + 1) f) =
      energy (fun i => mean (fun y => f (i, y)) - mean f) +
        energy (firstProjection d (fun y => mean (fun i => f (i, y)))) := by
  change energy (fun p : α × Words α d =>
    (mean (fun y => f (p.1, y)) - mean f) +
      firstProjection d (fun y => mean (fun i => f (i, y))) p.2) = _
  rw [energy_separated_add
    (fun i => mean (fun y => f (i, y)) - mean f)
    (firstProjection d (fun y => mean (fun i => f (i, y)))), firstProjection_mean]
  ring

theorem firstProjection_inner [Fintype α] [Nonempty α]
    (d : ℕ) (f : Words α d → ℝ) :
    mean (fun x => f x * firstProjection d f x) = energy (firstProjection d f) := by
  induction d with
  | zero => simp [firstProjection, energy]
  | succ d ih =>
      let u : α → ℝ := fun i => mean (fun y => f (i, y)) - mean f
      let g : Words α d → ℝ := fun y => mean (fun i => f (i, y))
      have hrow : mean (fun p : α × Words α d => f p * u p.1) = energy u := by
        rw [mean_mul_row]
        change mean (fun i => mean (fun y => f (i, y)) *
          (mean (fun y => f (i, y)) - mean f)) =
          energy (fun i => mean (fun y => f (i, y)) - mean f)
        rw [mean_prod f]
        exact mean_mul_centered (fun i => mean (fun y => f (i, y)))
      change mean (fun p : α × Words α d => f p * (u p.1 + firstProjection d g p.2)) = _
      calc
        _ = mean (fun p : α × Words α d => f p * u p.1) +
            mean (fun p : α × Words α d => f p * firstProjection d g p.2) := by
          simp only [mul_add, mean_add]
        _ = energy u + energy (firstProjection d g) := by
          rw [hrow, mean_mul_column, ih]
        _ = energy (firstProjection (d + 1) f) := (firstProjection_energy d f).symm

/-- Vanishing constant and one-coordinate averages, expressed recursively. -/
def FirstOrderZero [Fintype α] : (d : ℕ) → (Words α d → ℝ) → Prop
  | 0, f => mean f = 0
  | d + 1, f =>
      (∀ i, mean (fun y => f (i, y)) = 0) ∧
        FirstOrderZero d (fun y => mean (fun i => f (i, y)))

theorem FirstOrderZero.mean_eq_zero [Fintype α] [Nonempty α]
    {d : ℕ} {f : Words α d → ℝ} (hf : FirstOrderZero d f) : mean f = 0 := by
  cases d with
  | zero => exact hf
  | succ d =>
      rw [mean_prod]
      simp only [hf.1, mean_zero]

/-- Remove the constant and first-coordinate terms. -/
noncomputable def highRemainder [Fintype α] (d : ℕ) (f : Words α d → ℝ) :
    Words α d → ℝ := fun x => f x - mean f - firstProjection d f x

theorem highRemainder_firstOrderZero [Fintype α] [Nonempty α]
    (d : ℕ) (f : Words α d → ℝ) : FirstOrderZero d (highRemainder d f) := by
  induction d with
  | zero =>
      change mean (fun x => f x - mean f - 0) = 0
      simp
  | succ d ih =>
      let g : Words α d → ℝ := fun y => mean (fun i => f (i, y))
      have hg : mean g = mean f := by
        dsimp [g]
        rw [mean_comm]
        exact (mean_prod f).symm
      constructor
      · intro i
        change mean (fun y => f (i, y) - mean f -
          ((mean (fun z => f (i, z)) - mean f) + firstProjection d g y)) = 0
        simp [firstProjection_mean]
      · have heq : (fun y => mean (fun i => highRemainder (d + 1) f (i, y))) =
            highRemainder d g := by
          funext y
          simp only [highRemainder, firstProjection, mean_sub, mean_add, mean_const]
          rw [← mean_prod f]
          change g y - mean f - ((mean f - mean f) + firstProjection d g y) =
            g y - mean g - firstProjection d g y
          rw [hg]
          ring
        rw [heq]
        exact ih g

theorem energy_orthogonal_remainder [Fintype β] [Nonempty β]
    (f p : β → ℝ) (hp : mean p = 0)
    (hfp : mean (fun x => f x * p x) = energy p) :
    energy (fun x => f x - mean f - p x) = energy f - mean f ^ 2 - energy p := by
  unfold energy
  calc
    mean (fun x => (f x - mean f - p x) ^ 2) =
        mean (fun x => f x ^ 2 - (2 * mean f) * f x + mean f ^ 2 -
          2 * (f x * p x) + (2 * mean f) * p x + p x ^ 2) :=
      mean_congr fun x => by ring
    _ = mean (fun x => f x ^ 2) - mean f ^ 2 - mean (fun x => p x ^ 2) := by
      simp only [mean_add, mean_sub, mean_const_mul, mean_const, hp, hfp]
      dsimp [energy]
      ring

theorem highRemainder_energy [Fintype α] [Nonempty α]
    (d : ℕ) (f : Words α d → ℝ) :
    energy (highRemainder d f) = energy f - mean f ^ 2 - energy (firstProjection d f) :=
  energy_orthogonal_remainder f (firstProjection d f)
    (firstProjection_mean d f) (firstProjection_inner d f)

theorem highRemainder_energy_le [Fintype α] [Nonempty α]
    (d : ℕ) (f : Words α d → ℝ) : energy (highRemainder d f) ≤ energy f := by
  rw [highRemainder_energy]
  have := energy_nonneg (firstProjection d f)
  nlinarith [sq_nonneg (mean f)]

theorem productNoise_firstProjection [Fintype α] [Nonempty α]
    (r : ℝ) (d : ℕ) (f : Words α d → ℝ) :
    productNoise r d (firstProjection d f) = fun x => -r * firstProjection d f x := by
  induction d with
  | zero => simp [productNoise, firstProjection]
  | succ d ih =>
      let u : α → ℝ := fun i => mean (fun y => f (i, y)) - mean f
      let g : Words α d → ℝ := fun y => mean (fun i => f (i, y))
      let q := firstProjection d g
      have hu : mean u = 0 := by
        dsimp [u]
        rw [mean_sub, mean_const, ← mean_prod f]
        ring
      have hq := ih g
      funext p
      change tensorStep r (productNoise r d) (fun p : α × Words α d => u p.1 + q p.2) p =
        -r * (u p.1 + q p.2)
      rw [tensorStep_apply]
      simp only [mean_add, hu, mean_const, zero_add, map_fun_add]
      rw [productNoise_const]
      change productNoise r d q p.2 - r * (u p.1 + productNoise r d q p.2 -
        productNoise r d q p.2) = _
      change productNoise r d (firstProjection d g) p.2 -
        r * (u p.1 + productNoise r d (firstProjection d g) p.2 -
          productNoise r d (firstProjection d g) p.2) = _
      rw [hq]
      dsimp [q]
      ring

/-- The remainder beyond the first level contracts by the square of the
one-coordinate factor. -/
theorem productNoise_highOrder_bound [Fintype α] [Nonempty α]
    (r : ℝ) (hr : r ^ 2 ≤ 1) (d : ℕ)
    (f : Words α d → ℝ) (hf : FirstOrderZero d f) :
    energy (productNoise r d f) ≤ r ^ 4 * energy f := by
  induction d with
  | zero =>
      have hconst : f = fun _ => f PUnit.unit := by
        funext x
        cases x
        rfl
      have hval : f PUnit.unit = 0 := by
        have hmean := hf.mean_eq_zero
        rw [hconst, mean_const] at hmean
        exact hmean
      rw [hconst, hval]
      simp [productNoise, energy]
  | succ d ih =>
      let g : Words α d → ℝ := fun y => mean (fun i => f (i, y))
      have hg : FirstOrderZero d g := hf.2
      have hres (i : α) : mean (fun y => f (i, y) - g y) = 0 := by
        rw [mean_sub, hf.1 i, hg.mean_eq_zero]
        ring
      have hrow : mean (fun i => energy (fun y => f (i, y))) = energy f :=
        (mean_prod (fun p => f p ^ 2)).symm
      change energy (tensorStep r (productNoise r d) f) ≤ _
      rw [tensorStep_energy]
      calc
        _ ≤ r ^ 4 * energy g + r ^ 2 *
            mean (fun i => r ^ 2 * energy (fun y => f (i, y) - g y)) := by
          apply add_le_add (ih g hg)
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
          apply mean_mono
          intro i
          have h := productNoise_bound (α := α) r hr d (fun y => f (i, y) - g y)
          simpa only [hres i, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h
        _ = r ^ 4 * energy f := by
          rw [mean_const_mul, row_residual_energy (fun i y => f (i, y)), hrow]
          change r ^ 4 * energy g + r ^ 2 * (r ^ 2 * (energy f - energy g)) = _
          ring

end TuranUniversality.Selector
