module

public import TuranUniversality.Density.WeightedHom
public import TuranUniversality.Hypergraph.Restriction

@[expose] public section

/-! # Restricting weighted homomorphisms to their actual target support

The restriction hypothesis concerns the images of genuine homomorphisms.
The resulting equality holds for all real vertex weights; omitted vertices
need not have weight zero when no source homomorphism can use them.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density

universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable [Fintype V] {r : ℕ}

theorem isHom_pullback_iff (F : RGraph U r) (G : RGraph W r) (i : V ↪ W)
    (f : U → V) : F.IsHom (G.pullback i) f ↔ F.IsHom G (i ∘ f) := by
  constructor
  · intro hf
    exact (G.pullback_isHom i).comp hf
  · intro hf e he
    have him : (e.image f).map i = e.image (i ∘ f) := by
      simp [Finset.map_eq_image, Finset.image_image]
    apply (G.mem_pullback i _).mpr
    refine ⟨?_, ?_⟩
    · calc
        (e.image f).card = ((e.image f).map i).card := (Finset.card_map _).symm
        _ = r := by rw [him]; exact G.uniform _ (hf e he)
    · rw [him]
      exact hf e he

def pullbackHomMap (F : RGraph U r) (G : RGraph W r) (i : V ↪ W)
    (f : {f : U → V // F.IsHom (G.pullback i) f}) :
    {g : U → W // F.IsHom G g} :=
  ⟨i ∘ f.val, (isHom_pullback_iff F G i f.val).mp f.property⟩

theorem pullbackHomMap_bijective (F : RGraph U r) (G : RGraph W r) (i : V ↪ W)
    (hs : ∀ g : U → W, F.IsHom G g → ∀ u, g u ∈ Set.range i) :
    Function.Bijective (pullbackHomMap F G i) := by
  classical
  constructor
  · intro f g hfg
    apply Subtype.ext
    funext u
    exact i.injective (congrFun (congrArg Subtype.val hfg) u)
  · rintro ⟨g, hg⟩
    choose f hf using hs g hg
    have he : i ∘ f = g := funext hf
    refine ⟨⟨f, (isHom_pullback_iff F G i f).mpr ?_⟩, Subtype.ext he⟩
    simpa only [he] using hg

theorem weightedHomDensity_pullback_of_hom_supported [Fintype U] [Fintype W]
    (F : RGraph U r) (G : RGraph W r) (i : V ↪ W)
    (hs : ∀ g : U → W, F.IsHom G g → ∀ u, g u ∈ Set.range i)
    (x : W → ℝ) :
    F.weightedHomDensity (G.pullback i) (x ∘ i) = F.weightedHomDensity G x := by
  classical
  rw [weightedHomDensity_eq_sum_homs, weightedHomDensity_eq_sum_homs]
  apply Fintype.sum_equiv (Equiv.ofBijective (pullbackHomMap F G i)
    (pullbackHomMap_bijective F G i hs))
  intro f
  rfl

end TuranUniversality.RGraph
