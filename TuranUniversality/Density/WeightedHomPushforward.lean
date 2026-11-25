module

public import TuranUniversality.Density.WeightedHom

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Independent sampling under an arbitrary vertex map

Fiber weights are summed exactly. The inverse-image graph has every edge
whose image is an edge of the target; its entire weighted homomorphism
profile equals the target profile with the pushforward weighting. A
homomorphism into the target gives the corresponding one-sided bounds.
-/

open scoped BigOperators

namespace TuranUniversality.Density

variable {A V W : Type*} [DecidableEq W] [Fintype V]

def pushforwardWeight (f : V → W) (x : V → ℝ) (w : W) : ℝ :=
  ∑ v : {v : V // f v = w}, x v.val

theorem pushforwardWeight_nonneg (f : V → W) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (w : W) : 0 ≤ pushforwardWeight f x w :=
  Finset.sum_nonneg (fun v _ => hx v.val)

theorem sum_pushforwardWeight [Fintype W] (f : V → W) (x : V → ℝ) :
    (∑ w, pushforwardWeight f x w) = ∑ v, x v :=
  Fintype.sum_fiberwise f x

theorem pushforwardWeight_probability [Fintype W] (f : V → W) (x : V → ℝ)
    (hx : ProbabilityWeights x) : ProbabilityWeights (pushforwardWeight f x) :=
  ⟨pushforwardWeight_nonneg f x hx.1, (sum_pushforwardWeight f x).trans hx.2⟩

def functionSigmaEquiv (A W : Type*) (B : W → Type*) :
    (A → Σ w, B w) ≃ Σ θ : A → W, ∀ a, B (θ a) where
  toFun f := ⟨fun a => (f a).1, fun a => (f a).2⟩
  invFun p a := ⟨p.1 a, p.2 a⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def functionFiberEquiv (A : Type*) (f : V → W) :
    (A → V) ≃ Σ θ : A → W, ∀ a, {v : V // f v = θ a} :=
  (Equiv.arrowCongr (Equiv.refl A) (Equiv.sigmaFiberEquiv f).symm).trans
    (functionSigmaEquiv A W _)

theorem weightedMean_pushforward [Fintype A] [DecidableEq A] [Fintype W]
    (f : V → W) (x : V → ℝ) (S : (A → W) → ℝ) :
    weightedMean x (fun g : A → V => S (f ∘ g)) =
      weightedMean (pushforwardWeight f x) S := by
  classical
  unfold weightedMean
  calc
    _ = ∑ p : Σ θ : A → W, ∀ a, {v : V // f v = θ a},
        (∏ a, x (p.2 a).val) * S p.1 := by
      apply Fintype.sum_equiv (functionFiberEquiv A f)
      intro g
      rfl
    _ = ∑ θ : A → W, (∏ a, pushforwardWeight f x (θ a)) * S θ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro θ _
      dsimp only
      rw [← Finset.sum_mul]
      congr 1
      have h := Finset.prod_univ_sum
        (fun a : A => (Finset.univ : Finset {v : V // f v = θ a}))
        (fun _ v => x v.val)
      simpa [pushforwardWeight] using h.symm
    _ = _ := rfl

end TuranUniversality.Density

namespace TuranUniversality.RGraph

open Density

variable {U V W : Type*}
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable [Fintype V] {r : ℕ}

def inverseImage (H : RGraph W r) (f : V → W) : RGraph V r where
  edges := (Finset.univ.powersetCard r).filter (fun e => e.image f ∈ H.edges)
  uniform e he := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_inverseImage (H : RGraph W r) (f : V → W) (e : Finset V) :
    e ∈ (H.inverseImage f).edges ↔ e.card = r ∧ e.image f ∈ H.edges := by
  simp [inverseImage, Finset.mem_powersetCard]

theorem inverseImage_projection (H : RGraph W r) (f : V → W) :
    (H.inverseImage f).IsHom H f := by
  intro e he
  exact ((H.mem_inverseImage f e).mp he).2

theorem isHom_inverseImage_iff (F : RGraph U r) (H : RGraph W r) (f : V → W)
    (g : U → V) : F.IsHom (H.inverseImage f) g ↔ F.IsHom H (f ∘ g) := by
  constructor
  · intro hg
    exact (H.inverseImage_projection f).comp hg
  · intro hg e he
    apply (H.mem_inverseImage f _).mpr
    refine ⟨?_, ?_⟩
    · have hi : Set.InjOn g e := by
        intro a ha b hb hab
        exact hg.injOn_edge he ha hb (congrArg f hab)
      rw [Finset.card_image_of_injOn hi]
      exact F.uniform e he
    · simpa only [Finset.image_image] using hg e he

theorem weightedHomDensity_inverseImage [Fintype U] [Fintype W]
    (F : RGraph U r) (H : RGraph W r) (f : V → W) (x : V → ℝ) :
    F.weightedHomDensity (H.inverseImage f) x =
      F.weightedHomDensity H (pushforwardWeight f x) := by
  unfold weightedHomDensity
  calc
    _ = weightedMean x (fun g : U → V => F.homIndicator H (f ∘ g)) := by
      apply weightedMean_congr
      intro g
      simp only [homIndicator, isHom_inverseImage_iff]
    _ = _ := weightedMean_pushforward f x _

theorem weightedHomDensity_le_pushforward [Fintype U] [Fintype W]
    (F : RGraph U r) (G : RGraph V r) (H : RGraph W r) (f : V → W)
    (hf : G.IsHom H f) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    F.weightedHomDensity G x ≤ F.weightedHomDensity H (pushforwardWeight f x) := by
  unfold weightedHomDensity
  calc
    _ ≤ weightedMean x (fun g : U → V => F.homIndicator H (f ∘ g)) := by
      apply weightedMean_mono x hx
      intro g
      by_cases hg : F.IsHom G g
      · simp [hg, hf.comp hg]
      · rw [homIndicator_of_not_hom F G hg]
        exact F.homIndicator_nonneg H _
    _ = _ := weightedMean_pushforward f x _

theorem edgePolynomial_le_pushforward [Fintype W]
    (G : RGraph V r) (H : RGraph W r) (f : V → W)
    (hf : G.IsHom H f) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    G.edgePolynomial x ≤ H.edgePolynomial (pushforwardWeight f x) := by
  have h := (oneEdge r).weightedHomDensity_le_pushforward G H f hf x hx
  rw [weightedHomDensity_oneEdge, weightedHomDensity_oneEdge] at h
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast Nat.factorial_pos r : (0 : ℝ) < r.factorial)).mp h

theorem edgePolynomial_inverseImage [Fintype W]
    (H : RGraph W r) (f : V → W) (x : V → ℝ) :
    (H.inverseImage f).edgePolynomial x = H.edgePolynomial (pushforwardWeight f x) := by
  have h := (oneEdge r).weightedHomDensity_inverseImage H f x
  rw [weightedHomDensity_oneEdge, weightedHomDensity_oneEdge] at h
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero r : (r.factorial : ℝ) ≠ 0) h

end TuranUniversality.RGraph
