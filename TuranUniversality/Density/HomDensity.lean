module

public import TuranUniversality.Density.Averages
public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-! # Finite homomorphism densities and collision estimates -/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Selector Density

universe u v w
variable {V : Type u} {W : Type v} {U : Type w}
variable [DecidableEq V] [DecidableEq W] [DecidableEq U] {r : ℕ}

noncomputable def homIndicator (F : RGraph V r) (G : RGraph W r) (f : V → W) : ℝ := by
  classical
  exact if F.IsHom G f then 1 else 0

@[simp] theorem homIndicator_of_hom (F : RGraph V r) (G : RGraph W r)
    {f : V → W} (h : F.IsHom G f) : F.homIndicator G f = 1 := by
  simp [homIndicator, h]

@[simp] theorem homIndicator_of_not_hom (F : RGraph V r) (G : RGraph W r)
    {f : V → W} (h : ¬ F.IsHom G f) : F.homIndicator G f = 0 := by
  simp [homIndicator, h]

theorem homIndicator_nonneg (F : RGraph V r) (G : RGraph W r) (f : V → W) :
    0 ≤ F.homIndicator G f := by
  unfold homIndicator
  split <;> norm_num

theorem homIndicator_le_one (F : RGraph V r) (G : RGraph W r) (f : V → W) :
    F.homIndicator G f ≤ 1 := by
  unfold homIndicator
  split <;> norm_num

/-- The ordinary uniform homomorphism density, with replacement. -/
noncomputable def homDensity [Fintype V] [Fintype W]
    (F : RGraph V r) (G : RGraph W r) : ℝ := mean (F.homIndicator G)

theorem homDensity_nonneg [Fintype V] [Fintype W]
    (F : RGraph V r) (G : RGraph W r) : 0 ≤ F.homDensity G :=
  mean_nonneg (F.homIndicator_nonneg G)

theorem homDensity_le_one [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) : F.homDensity G ≤ 1 := by
  calc
    F.homDensity G ≤ mean (fun _ : V → W => (1 : ℝ)) :=
      mean_mono (F.homIndicator_le_one G)
    _ = 1 := mean_const _

theorem homDensity_pos_iff [Fintype V] [Fintype W]
    (F : RGraph V r) (G : RGraph W r) :
    0 < F.homDensity G ↔ ∃ f, F.IsHom G f := by
  classical
  constructor
  · intro hp
    by_contra hn
    have hz : F.homDensity G = 0 := by
      unfold homDensity
      convert mean_zero (α := V → W) using 1
      apply mean_congr
      intro f
      exact homIndicator_of_not_hom F G (fun hf => hn ⟨f, hf⟩)
    linarith
  · rintro ⟨f, hf⟩
    exact Finset.expect_pos' (fun f _ => F.homIndicator_nonneg G f)
      ⟨f, Finset.mem_univ _, by simp [hf]⟩

theorem homDensity_eq_zero_iff [Fintype V] [Fintype W]
    (F : RGraph V r) (G : RGraph W r) :
    F.homDensity G = 0 ↔ F.HomFree G := by
  rw [HomFree, ← F.homDensity_pos_iff]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact le_antisymm (le_of_not_gt h) (F.homDensity_nonneg G)

/-- An ordinary embedded source can only have larger homomorphism density. -/
theorem homDensity_le_of_embedding [Fintype V] [Fintype W] [Fintype U] [Nonempty W]
    (F : RGraph V r) (Q : RGraph U r) (G : RGraph W r)
    {i : V → U} (hi : F.IsEmbedding Q i) :
    Q.homDensity G ≤ F.homDensity G := by
  calc
    Q.homDensity G ≤ mean (fun f : U → W => F.homIndicator G (f ∘ i)) := by
      apply mean_mono
      intro f
      by_cases hf : Q.IsHom G f
      · simp [hf, hf.comp hi.isHom]
      · rw [homIndicator_of_not_hom Q G hf]
        exact F.homIndicator_nonneg G _
    _ = F.homDensity G := mean_restrict_injective i hi.1 _

/-- If there is no ordinary embedded copy, every homomorphism has a collision.
The coarser ordered-pair bound avoids a separate choice of pair orientation. -/
theorem homDensity_le_collision_bound [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r)
    (hfree : ¬ ∃ f, F.IsEmbedding G f) :
    F.homDensity G ≤ (Fintype.card V : ℝ) ^ 2 / Fintype.card W := by
  classical
  let X (f : V → W) (p : V × V) : ℝ :=
    if p.1 ≠ p.2 ∧ f p.1 = f p.2 then 1 else 0
  have hpoint (f : V → W) : F.homIndicator G f ≤ ∑ p : V × V, X f p := by
    by_cases hf : F.IsHom G f
    · have hn : ¬ Function.Injective f := fun h => hfree ⟨f, h, hf⟩
      simp only [Function.Injective, not_forall] at hn
      obtain ⟨u, v, huv, hne⟩ := hn
      rw [homIndicator_of_hom F G hf]
      have hp : X f (u, v) = 1 := by simp [X, hne, huv]
      rw [← hp]
      exact Finset.single_le_sum (fun p _ => by simp only [X]; split <;> norm_num)
        (Finset.mem_univ (u, v))
    · rw [homIndicator_of_not_hom F G hf]
      exact Finset.sum_nonneg (fun p _ => by simp only [X]; split <;> norm_num)
  have havg (p : V × V) : mean (fun f : V → W => X f p) ≤
      (Fintype.card W : ℝ)⁻¹ := by
    by_cases hp : p.1 = p.2
    · simp [X, hp]
    · simpa [X, hp] using
        (mean_equal_coordinates (C := W) p.1 p.2 hp).le
  calc
    F.homDensity G ≤ mean (fun f : V → W => ∑ p : V × V, X f p) := mean_mono hpoint
    _ = ∑ p : V × V, mean (fun f : V → W => X f p) :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _p : V × V, (Fintype.card W : ℝ)⁻¹ :=
      Finset.sum_le_sum (fun p _ => havg p)
    _ = _ := by simp [Fintype.card_prod, pow_two, div_eq_mul_inv]

end TuranUniversality.RGraph
