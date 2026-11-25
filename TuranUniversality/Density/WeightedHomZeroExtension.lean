module

public import TuranUniversality.Density.WeightedHomRestriction

@[expose] public section

/-! # Adding or deleting vertices of zero weight

An omitted vertex can participate in actual homomorphisms, but every such
homomorphism has weight zero. This is the equality needed when completing
a partial rooting by new isolated or nonisolated zero-weight roots.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density

universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable [Fintype U] [Fintype V] [Fintype W] {r : ℕ}

theorem weightedHomDensity_zero_extension
    (F : RGraph U r) (G : RGraph W r) (i : V ↪ W)
    (x : W → ℝ) (hz : ∀ w, w ∉ Set.range i → x w = 0) :
    F.weightedHomDensity (G.pullback i) (x ∘ i) = F.weightedHomDensity G x := by
  classical
  rw [weightedHomDensity_eq_sum_homs, weightedHomDensity_eq_sum_homs]
  apply Fintype.sum_of_injective (pullbackHomMap F G i)
  · intro f g hfg
    apply Subtype.ext
    funext u
    exact i.injective (congrFun (congrArg Subtype.val hfg) u)
  · intro g hg
    have hn : ∃ u, g.val u ∉ Set.range i := by
      by_contra! hall
      choose f hf using hall
      have he : i ∘ f = g.val := funext hf
      have hhom : F.IsHom (G.pullback i) f :=
        (isHom_pullback_iff F G i f).mpr (he.symm ▸ g.property)
      exact hg ⟨⟨f, hhom⟩, Subtype.ext he⟩
    obtain ⟨u, hu⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ u) (hz _ hu)
  · intro f
    rfl

theorem weightedHomDensity_supportGraph
    (F : RGraph U r) (G : RGraph V r) (x : V → ℝ) :
    F.weightedHomDensity (G.supportGraph x) (fun v => x v.val) =
      F.weightedHomDensity G x := by
  apply weightedHomDensity_zero_extension F G (Function.Embedding.subtype _) x
  intro v hv
  change v ∉ Set.range (Subtype.val : WeightVertex x → V) at hv
  simpa only [weightSupport_range, not_not] using hv

end TuranUniversality.RGraph
