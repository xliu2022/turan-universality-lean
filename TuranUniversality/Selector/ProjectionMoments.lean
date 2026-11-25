/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.FirstProjection
public import TuranUniversality.Selector.CrossIntersecting

/-!
# Moment estimates for the first-coordinate projection
-/

@[expose] public section

namespace TuranUniversality.Selector

variable {α β : Type*}

theorem fourth_separated_add [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (u : α → ℝ) (v : β → ℝ) (hu : mean u = 0) (hv : mean v = 0) :
    mean (fun p : α × β => (u p.1 + v p.2) ^ 4) =
      mean (fun i => u i ^ 4) + mean (fun y => v y ^ 4) + 6 * energy u * energy v := by
  calc
    _ = mean (fun p : α × β => u p.1 ^ 4 + v p.2 ^ 4 +
        4 * (u p.1 ^ 3 * v p.2) + 6 * (u p.1 ^ 2 * v p.2 ^ 2) +
          4 * (u p.1 * v p.2 ^ 3)) := mean_congr fun p => by ring
    _ = _ := by
      rw [mean_prod]
      simp [energy, hu, hv]
      ring

/-- Bounds on all the one-coordinate components in the recursive
first-order projection. -/
def ComponentBound [Fintype α] (M : ℝ) : (d : ℕ) → (Words α d → ℝ) → Prop
  | 0, _ => True
  | d + 1, f =>
      (∀ i, |mean (fun y => f (i, y)) - mean f| ≤ M) ∧
        ComponentBound M d (fun y => mean (fun i => f (i, y)))

theorem fourth_le_bound_mul_energy [Fintype β]
    (M : ℝ) (f : β → ℝ) (hf : ∀ x, |f x| ≤ M) :
    mean (fun x => f x ^ 4) ≤ M ^ 2 * energy f := by
  unfold energy
  rw [← mean_const_mul]
  apply mean_mono
  intro x
  have hlow := (abs_le.mp (hf x)).1
  have hupp := (abs_le.mp (hf x)).2
  have hsq : f x ^ 2 ≤ M ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hupp) (show 0 ≤ M + f x by linarith)
    nlinarith
  have := mul_le_mul_of_nonneg_right hsq (sq_nonneg (f x))
  nlinarith

theorem firstProjection_fourth [Fintype α] [Nonempty α]
    (M : ℝ) (d : ℕ) (f : Words α d → ℝ) (hf : ComponentBound M d f) :
    mean (fun x => firstProjection d f x ^ 4) ≤
      M ^ 2 * energy (firstProjection d f) + 3 * energy (firstProjection d f) ^ 2 := by
  induction d with
  | zero => simp [firstProjection, energy]
  | succ d ih =>
      let u : α → ℝ := fun i => mean (fun y => f (i, y)) - mean f
      let g : Words α d → ℝ := fun y => mean (fun i => f (i, y))
      let q := firstProjection d g
      have hu : mean u = 0 := by
        dsimp [u]
        rw [mean_sub, mean_const, ← mean_prod f]
        ring
      have hq : mean q = 0 := firstProjection_mean d g
      have hu4 := fourth_le_bound_mul_energy M u hf.1
      have hq4 := ih g hf.2
      have he : energy (firstProjection (d + 1) f) = energy u + energy q :=
        firstProjection_energy d f
      change mean (fun p : α × Words α d => (u p.1 + q p.2) ^ 4) ≤ _
      rw [fourth_separated_add u q hu hq, he]
      change mean (fun y => q y ^ 4) ≤ M ^ 2 * energy q + 3 * energy q ^ 2 at hq4
      nlinarith [sq_nonneg (energy u)]

/-- The first-level energy lower bound obtained from zero correlation with
the complete-product operator. -/
theorem firstProjection_lower_of_zero_correlation [Fintype α] [Nonempty α]
    (r : ℝ) (hr : r ^ 2 ≤ 1) (d : ℕ) (f : Words α d → ℝ)
    (hzero : mean (fun x => f x * productNoise r d f x) = 0) :
    mean f ^ 2 ≤ r * energy (firstProjection d f) + r ^ 2 * energy f := by
  let p := firstProjection d f
  let h := highRemainder d f
  let T := productNoise (α := α) r d
  have hdecomp : f = fun x => mean f + p x + h x := by
    funext x
    dsimp [p, h, highRemainder]
    ring
  have hPdecomp (x : Words α d) : T f x = mean f - r * p x + T h x := by
    have heq := congrArg (fun k : Words α d → ℝ => T k x) hdecomp
    simp only [map_fun_add] at heq
    change T f x = _ at heq
    rw [productNoise_const, productNoise_firstProjection] at heq
    dsimp [p] at *
    nlinarith [heq]
  have hidentity : mean (fun x => f x * T h x) =
      r * energy p - mean f ^ 2 := by
    have heq : mean (fun x => f x * T f x) =
        mean f ^ 2 - r * energy p + mean (fun x => f x * T h x) := by
      calc
        _ = mean (fun x => f x * mean f - r * (f x * p x) + f x * T h x) := by
          apply mean_congr
          intro x
          rw [hPdecomp]
          ring
        _ = _ := by
          simp only [mean_add, mean_sub, mean_mul_const, mean_const_mul]
          rw [firstProjection_inner]
          ring
    rw [hzero] at heq
    linarith
  have henergy : energy (T h) ≤ r ^ 4 * energy f := by
    calc
      energy (T h) ≤ r ^ 4 * energy h :=
        productNoise_highOrder_bound r hr d h (highRemainder_firstOrderZero d f)
      _ ≤ r ^ 4 * energy f :=
        mul_le_mul_of_nonneg_left (highRemainder_energy_le d f) (by positivity)
  have hsq : mean (fun x => f x * T h x) ^ 2 ≤ (r ^ 2 * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (T h) := mean_mul_sq_le f (T h)
      _ ≤ energy f * (r ^ 4 * energy f) :=
        mul_le_mul_of_nonneg_left henergy (energy_nonneg f)
      _ = _ := by ring
  have hnonneg : 0 ≤ r ^ 2 * energy f := mul_nonneg (sq_nonneg r) (energy_nonneg f)
  have habs : |mean (fun x => f x * T h x)| ≤ r ^ 2 * energy f := by
    apply (sq_le_sq₀ (abs_nonneg _) hnonneg).mp
    simpa only [sq_abs] using hsq
  have hlow := (abs_le.mp habs).1
  rw [hidentity] at hlow
  change mean f ^ 2 ≤ r * energy p + r ^ 2 * energy f
  linarith

theorem energy_indicator_mul [Fintype β] (A : Finset β) (f : β → ℝ) :
    energy (fun x => indicator A x * f x) = mean (fun x => indicator A x * f x ^ 2) := by
  classical
  apply mean_congr
  intro x
  by_cases hx : x ∈ A <;> simp [indicator, hx]

theorem mean_indicator_mul_self [Fintype β] (A : Finset β) (f : β → ℝ) :
    mean (fun x => indicator A x * (indicator A x * f x)) =
      mean (fun x => indicator A x * f x) := by
  classical
  apply mean_congr
  intro x
  by_cases hx : x ∈ A <;> simp [indicator, hx]

/-- The special fourth-moment Hölder estimate needed for indicator
functions, derived from two applications of finite Cauchy--Schwarz. -/
theorem indicator_correlation_fourth [Fintype β] (A : Finset β) (p : β → ℝ) :
    mean (fun x => indicator A x * p x) ^ 4 ≤
      density A ^ 3 * mean (fun x => p x ^ 4) := by
  classical
  let S := mean (fun x => indicator A x * p x ^ 2)
  let C := mean (fun x => indicator A x * p x)
  have ha : 0 ≤ density A := density_nonneg A
  have hS : 0 ≤ S := by
    apply mean_nonneg
    intro x
    by_cases hx : x ∈ A <;> simp [indicator, hx, sq_nonneg]
  have h1 : C ^ 2 ≤ density A * S := by
    have h := mean_mul_sq_le (indicator A) (fun x => indicator A x * p x)
    rw [mean_indicator_mul_self, energy_indicator, energy_indicator_mul] at h
    exact h
  have h2 : S ^ 2 ≤ density A * mean (fun x => p x ^ 4) := by
    have h := mean_mul_sq_le (indicator A) (fun x => indicator A x * p x ^ 2)
    rw [mean_indicator_mul_self, energy_indicator, energy_indicator_mul] at h
    calc
      S ^ 2 ≤ density A * mean (fun x => indicator A x * (p x ^ 2) ^ 2) := h
      _ ≤ density A * mean (fun x => p x ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ ha
        apply mean_mono
        intro x
        by_cases hx : x ∈ A
        · simp [indicator, hx, ← pow_mul]
        · simp [indicator, hx]
          positivity
  have hsq : (C ^ 2) ^ 2 ≤ (density A * S) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg C) (mul_nonneg ha hS)).mpr h1
  have hmul := mul_le_mul_of_nonneg_left h2 (sq_nonneg (density A))
  change C ^ 4 ≤ _
  nlinarith [hsq, hmul]

end TuranUniversality.Selector
