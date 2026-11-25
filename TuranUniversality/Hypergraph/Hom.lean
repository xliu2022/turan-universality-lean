module

public import TuranUniversality.Hypergraph.Basic

@[expose] public section

/-!
# Homomorphisms of finite simple uniform hypergraphs

Homomorphisms preserve edges. Global injectivity is required only for embeddings.
Uniformity implies injectivity on each edge of a homomorphism.
-/

namespace TuranUniversality.RGraph

universe u v w
variable {V : Type u} {W : Type v} {X : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq X] {r : ℕ}

/-- Edge preservation, with no global injectivity requirement. -/
def IsHom (F : RGraph V r) (G : RGraph W r) (f : V → W) : Prop :=
  ∀ e ∈ F.edges, e.image f ∈ G.edges

instance (F : RGraph V r) (G : RGraph W r) (f : V → W) : Decidable (F.IsHom G f) :=
  inferInstanceAs (Decidable (∀ e ∈ F.edges, e.image f ∈ G.edges))

/-- Absence of any edge-preserving map from the forbidden graph. -/
def HomFree (F : RGraph V r) (G : RGraph W r) : Prop :=
  ¬ ∃ f : V → W, F.IsHom G f

theorem isHom_id (F : RGraph V r) : F.IsHom F id := by
  intro e he
  simpa using he

theorem IsHom.comp {F : RGraph V r} {G : RGraph W r} {H : RGraph X r}
    {f : V → W} {g : W → X} (hg : G.IsHom H g) (hf : F.IsHom G f) :
    F.IsHom H (g ∘ f) := by
  intro e he
  simpa [Finset.image_image] using hg (e.image f) (hf e he)

theorem IsEmbedding.isHom {F : RGraph V r} {G : RGraph W r}
    {f : V → W} (hf : F.IsEmbedding G f) : F.IsHom G f := hf.2

theorem IsEmbedding.comp {F : RGraph V r} {G : RGraph W r} {H : RGraph X r}
    {f : V → W} {g : W → X} (hg : G.IsEmbedding H g) (hf : F.IsEmbedding G f) :
    F.IsEmbedding H (g ∘ f) :=
  ⟨hg.1.comp hf.1, hg.isHom.comp hf.isHom⟩

theorem IsHom.injOn_edge {F : RGraph V r} {G : RGraph W r}
    {f : V → W} (hf : F.IsHom G f) {e : Finset V} (he : e ∈ F.edges) :
    Set.InjOn f (e : Set V) := by
  apply Finset.card_image_iff.mp
  rw [G.uniform _ (hf e he), F.uniform _ he]

theorem HomFree.free {F : RGraph V r} {G : RGraph W r}
    (h : F.HomFree G) : ¬ ∃ f, F.IsEmbedding G f := by
  rintro ⟨f, hf⟩
  exact h ⟨f, hf.isHom⟩

theorem HomFree.of_hom {F : RGraph V r} {G : RGraph W r} {H : RGraph X r}
    {f : V → W} (h : F.HomFree H) (hf : F.IsHom G f) : G.HomFree H := by
  rintro ⟨g, hg⟩
  exact h ⟨g ∘ f, hg.comp hf⟩

/-- Every pair of distinct vertices occurs together in an edge. -/
def CoversPairs (G : RGraph V r) : Prop :=
  ∀ u v : V, u ≠ v → ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e

theorem CoversPairs.hom_injective {F : RGraph V r} {G : RGraph W r}
    (hF : F.CoversPairs) {f : V → W} (hf : F.IsHom G f) :
    Function.Injective f := by
  intro u v huv
  by_contra hne
  obtain ⟨e, he, hu, hv⟩ := hF u v hne
  exact hne (hf.injOn_edge he hu hv huv)

theorem CoversPairs.hom_iff_embedding {F : RGraph V r} {G : RGraph W r}
    (hF : F.CoversPairs) {f : V → W} :
    F.IsHom G f ↔ F.IsEmbedding G f :=
  ⟨fun h => ⟨hF.hom_injective h, h⟩, fun h => h.2⟩

end TuranUniversality.RGraph
