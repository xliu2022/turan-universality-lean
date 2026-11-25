module

public import TuranUniversality.Density.Sampling

@[expose] public section

/-! # Sampling estimates for every finite homomorphism-density coordinate

All probabilities are finite uniform averages. The estimates are uniform in
the host graph and use only collisions of sampled indices. They apply to
arbitrary finite test graphs, not only to the one-edge coordinate.
-/

open scoped BigOperators

namespace TuranUniversality.Density

open Selector

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem mean_noninjective_le [Nonempty B] :
    mean (fun f : A → B => truth (¬ Function.Injective f)) ≤
      (Fintype.card A : ℝ) ^ 2 / Fintype.card B := by
  classical
  let X (f : A → B) (p : A × A) : ℝ :=
    if p.1 ≠ p.2 ∧ f p.1 = f p.2 then 1 else 0
  have hpoint (f : A → B) : truth (¬ Function.Injective f) ≤ ∑ p : A × A, X f p := by
    by_cases hf : Function.Injective f
    · simp only [truth, hf, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun p _ => by simp only [X]; split <;> norm_num)
    · have hn := hf
      simp only [Function.Injective, not_forall] at hn
      obtain ⟨u, v, huv, hne⟩ := hn
      have hp : X f (u, v) = 1 := by simp [X, hne, huv]
      simp only [truth, hf, not_false_eq_true, ite_true]
      rw [← hp]
      exact Finset.single_le_sum (fun p _ => by simp only [X]; split <;> norm_num)
        (Finset.mem_univ (u, v))
  have havg (p : A × A) : mean (fun f : A → B => X f p) ≤
      (Fintype.card B : ℝ)⁻¹ := by
    by_cases hp : p.1 = p.2
    · simp [X, hp]
    · simpa [X, hp] using (mean_equal_coordinates (C := B) p.1 p.2 hp).le
  calc
    _ ≤ mean (fun f : A → B => ∑ p : A × A, X f p) := mean_mono hpoint
    _ = ∑ p : A × A, mean (fun f : A → B => X f p) := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _p : A × A, (Fintype.card B : ℝ)⁻¹ := Finset.sum_le_sum (fun p _ => havg p)
    _ = _ := by simp [Fintype.card_prod, pow_two, div_eq_mul_inv]

theorem mean_bounds_of_eq_on_injections [Nonempty B]
    (f : (A → B) → ℝ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hf0 : ∀ g, 0 ≤ f g) (hf1 : ∀ g, f g ≤ 1)
    (heq : ∀ g, Function.Injective g → f g = μ) :
    μ - (Fintype.card A : ℝ) ^ 2 / Fintype.card B ≤ mean f ∧
      mean f ≤ μ + (Fintype.card A : ℝ) ^ 2 / Fintype.card B := by
  classical
  have hl (g : A → B) : μ - truth (¬ Function.Injective g) ≤ f g := by
    by_cases hg : Function.Injective g
    · simp [truth, hg, heq g hg]
    · simp only [truth, hg, not_false_eq_true, ite_true]
      linarith [hf0 g]
  have hu (g : A → B) : f g ≤ μ + truth (¬ Function.Injective g) := by
    by_cases hg : Function.Injective g
    · simp [truth, hg, heq g hg]
    · simp only [truth, hg, not_false_eq_true, ite_true]
      linarith [hf1 g]
  have hlm := mean_mono hl
  have hum := mean_mono hu
  simp only [mean_sub, mean_add, mean_const] at hlm hum
  have hc := mean_noninjective_le (A := A) (B := B)
  constructor <;> linarith

end TuranUniversality.Density

namespace TuranUniversality.RGraph

open Selector Density

universe u v w
variable {V : Type u} {W : Type v} {U : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq U] {r : ℕ}

theorem isHom_sample_iff_of_injective (F : RGraph V r) (G : RGraph W r)
    {m : ℕ} (g : V → Fin m) (hg : Function.Injective g) (f : Fin m → W) :
    F.IsHom (G.sample m f) g ↔ F.IsHom G (f ∘ g) := by
  constructor
  · intro h
    exact (G.sample_projection m f).comp h
  · intro h e he
    apply (G.mem_sample m f _).mpr
    constructor
    · rw [Finset.card_image_of_injective _ hg]
      exact F.uniform e he
    · simpa only [Finset.image_image] using h e he

theorem mean_homIndicator_sample_of_injective [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) {m : ℕ}
    (g : V → Fin m) (hg : Function.Injective g) :
    mean (fun f : Fin m → W => F.homIndicator (G.sample m f) g) = F.homDensity G := by
  calc
    _ = mean (fun f : Fin m → W => F.homIndicator G (f ∘ g)) := by
      apply mean_congr
      intro f
      simp only [homIndicator, F.isHom_sample_iff_of_injective G g hg f]
    _ = _ := mean_restrict_injective g hg _

theorem mean_sample_homDensity_bounds [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) (m : ℕ) (hm : 0 < m) :
    F.homDensity G - (Fintype.card V : ℝ) ^ 2 / m ≤
        mean (fun f : Fin m → W => F.homDensity (G.sample m f)) ∧
      mean (fun f : Fin m → W => F.homDensity (G.sample m f)) ≤
        F.homDensity G + (Fintype.card V : ℝ) ^ 2 / m := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h := mean_bounds_of_eq_on_injections
    (fun g : V → Fin m => mean (fun f : Fin m → W => F.homIndicator (G.sample m f) g))
    (F.homDensity G) (F.homDensity_nonneg G) (F.homDensity_le_one G)
    (fun g => mean_nonneg (fun f => F.homIndicator_nonneg _ g))
    (fun g => by
      calc
        _ ≤ mean (fun _f : Fin m → W => (1 : ℝ)) :=
          mean_mono (fun f => F.homIndicator_le_one _ g)
        _ = 1 := mean_const _)
    (F.mean_homIndicator_sample_of_injective G)
  have heq : mean (fun f : Fin m → W => F.homDensity (G.sample m f)) =
      mean (fun g : V → Fin m => mean (fun f : Fin m → W =>
        F.homIndicator (G.sample m f) g)) := mean_comm _
  simpa only [Fintype.card_fin, heq] using h

/-- Disjoint union on a disjoint vertex type. -/
def sumGraph (F : RGraph V r) (H : RGraph U r) : RGraph (V ⊕ U) r where
  edges := F.edges.image (fun e => e.image Sum.inl) ∪ H.edges.image (fun e => e.image Sum.inr)
  uniform e he := by
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
      exact F.uniform a ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.card_image_of_injective _ Sum.inr_injective]
      exact H.uniform a ha

theorem sumGraph_isHom_iff (F : RGraph V r) (H : RGraph U r) (G : RGraph W r)
    (f : V ⊕ U → W) :
    (F.sumGraph H).IsHom G f ↔ F.IsHom G (f ∘ Sum.inl) ∧ H.IsHom G (f ∘ Sum.inr) := by
  constructor
  · intro h
    constructor
    · intro e he
      have := h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
      simpa only [Finset.image_image] using this
    · intro e he
      have := h _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
      simpa only [Finset.image_image] using this
  · rintro ⟨hF, hH⟩ e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      simpa only [Finset.image_image] using hF a ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      simpa only [Finset.image_image] using hH a ha

theorem sumGraph_homDensity [Fintype V] [Fintype U] [Fintype W]
    (F : RGraph V r) (H : RGraph U r) (G : RGraph W r) :
    (F.sumGraph H).homDensity G = F.homDensity G * H.homDensity G := by
  classical
  calc
    _ = mean (fun p : (V → W) × (U → W) => F.homIndicator G p.1 * H.homIndicator G p.2) := by
      apply Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow V U W)
      intro f
      simp only [homIndicator, sumGraph_isHom_iff]
      change (if F.IsHom G (f ∘ Sum.inl) ∧ H.IsHom G (f ∘ Sum.inr) then 1 else 0) =
        (if F.IsHom G (f ∘ Sum.inl) then 1 else 0) *
        (if H.IsHom G (f ∘ Sum.inr) then 1 else 0)
      split_ifs <;> simp_all
    _ = _ := by rw [mean_prod]; simp only [mean_const_mul, mean_mul_const, homDensity]

theorem mean_sample_homDensity_square_error [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) (m : ℕ) (hm : 0 < m) :
    mean (fun f : Fin m → W => (F.homDensity (G.sample m f) - F.homDensity G) ^ 2) ≤
      6 * (Fintype.card V : ℝ) ^ 2 / m := by
  let μ := F.homDensity G
  let Y (f : Fin m → W) := F.homDensity (G.sample m f)
  let δ : ℝ := (Fintype.card V : ℝ) ^ 2 / m
  have hμ0 : 0 ≤ μ := F.homDensity_nonneg G
  have hμ1 : μ ≤ 1 := F.homDensity_le_one G
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hlo : μ - δ ≤ mean Y := (F.mean_sample_homDensity_bounds G m hm).1
  have hup : mean (fun f => Y f ^ 2) ≤ μ ^ 2 + 4 * δ := by
    have h := ((F.sumGraph F).mean_sample_homDensity_bounds G m hm).2
    simp only [sumGraph_homDensity, Fintype.card_sum, Nat.cast_add] at h
    calc
      _ = mean (fun f => Y f * Y f) := mean_congr (fun f => by ring)
      _ ≤ μ * μ + ((Fintype.card V : ℝ) + Fintype.card V) ^ 2 / m := h
      _ = _ := by dsimp [δ]; ring
  have heq : mean (fun f => (Y f - μ) ^ 2) =
      mean (fun f => Y f ^ 2) - 2 * μ * mean Y + μ ^ 2 := by
    calc
      _ = mean (fun f => Y f ^ 2 - (2 * μ) * Y f + μ ^ 2) :=
        mean_congr (fun f => by ring)
      _ = _ := by simp
  have hp := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2 * μ by positivity)
  have hμδ := mul_le_mul_of_nonneg_right hμ1 hδ
  change mean (fun f => (Y f - μ) ^ 2) ≤ _
  rw [heq]
  calc
    _ ≤ 6 * δ := by nlinarith
    _ = _ := by dsimp [δ]; ring

end TuranUniversality.RGraph
