module

public import TuranUniversality.Density.PinnedSampling
public import TuranUniversality.Density.WeightedHomPushforward
public import TuranUniversality.Structural.CommonFrameNormalize

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A genuine common frame from finite link-defect bounds

Unconditioned independent samples avoid all pinned missing-edge events at
once. Canonical role equality makes each relevant replacement an edge of
the actual completion; avoidance of the missing edge set then makes it an
edge of the original graph. The allowed root action is normalized last.
-/

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem hasReplacementFrame_of_link_bounds
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ : V → Option (Roots (CodePools.blockCount q) t)) (R : RecordSystem V)
    (hh : G.IsHom (Compiled.graph t (CodePools.pool p q hpq) R) (place ρ))
    (S : Finset V) (x : V → ℝ) (hx : ProbabilityWeights x) (ε : ℝ)
    (hlink : ∀ y ∈ S, (((Compiled.graph t (CodePools.pool p q hpq) R).inverseImage (place ρ)).edgeDifference G).linkPolynomial x y ≤ ε)
    (hpos : (S.card : ℝ) * Fintype.card (Compiled.Vertex (CodePools.blockCount q) t (Fin 5)) *
        (Frame.graph (CodePools.blockCount q) t
          (CodePools.pool p q hpq CodePools.neutralLabel)).edges.card *
        (t + (3 * CodePools.blockCount q + 4) - 1).factorial * ε <
      (Frame.graph (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)).weightedHomDensity G x) :
    HasReplacementFrame p q hpq G ρ S := by
  let J := Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)
  let H := (Compiled.graph t (CodePools.pool p q hpq) R).inverseImage (place ρ)
  obtain ⟨f, hf, hav⟩ := J.exists_hom_avoiding_pinned_difference G H S x hx ε hlink hpos
  obtain ⟨α, _, hroot, _⟩ := frame_roles p q hpq hq G ρ R hh f hf
  have hmatched : HasRoleMatchedFrame p q hpq G ρ S := by
    refine ⟨f, hf, ?_⟩
    intro y hy r hmatch
    let a := rootVertex (Fin 5) r
    have hp : place ρ y = place ρ (f a) := by
      rw [place_root ρ (hmatch.trans (hroot r)), place_root ρ (hroot r)]
    have heq : place ρ ∘ Function.update f a y = place ρ ∘ f := by
      funext u
      by_cases hua : u = a
      · subst u
        simpa only [Function.comp_apply, Function.update_self] using hp
      · simp only [Function.comp_apply, Function.update_of_ne hua]
    have hH : J.IsHom H (Function.update f a y) := by
      apply (J.isHom_inverseImage_iff _ (place ρ) _).mpr
      rw [heq]
      exact hh.comp hf
    intro e he
    by_cases ha : a ∈ e
    · have heH := hH e he
      by_contra hn
      exact hav y hy a e he ha (Finset.mem_sdiff.mpr ⟨heH, hn⟩)
    · have him : e.image (Function.update f a y) = e.image f := by
        apply Finset.image_congr
        intro u hu
        have hua : u ≠ a := by
          intro h
          subst u
          exact ha hu
        exact Function.update_of_ne hua y f
      rw [him]
      exact hf e he
  exact hmatched.normalize p q hpq hq R hh

end TuranUniversality.Structural.Roles
