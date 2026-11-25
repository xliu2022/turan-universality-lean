module

public import TuranUniversality.Hypergraph.FiniteBasis
public import TuranUniversality.Hypergraph.Restriction
public import TuranUniversality.Hypergraph.Blowup

@[expose] public section

/-! # Ordinary and homomorphism avoidance of a finite forbidden family -/

namespace TuranUniversality

universe u v

variable {r : ℕ} {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W]

/-- Ordinary avoidance requires injective maps, including on isolated vertices. -/
def familyFree (F : Finset (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, ¬ ∃ f, A.2.IsEmbedding G f

/-- Every member of the finite family is forbidden as a homomorphic image. -/
def familyHomFree (F : Finset (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, A.2.HomFree G

instance [Fintype V] (F : Finset (FiniteGraph r)) (G : RGraph V r) :
    Decidable (familyFree F G) :=
  inferInstanceAs (Decidable (∀ A ∈ F, ¬ ∃ f, A.2.IsEmbedding G f))

instance [Fintype V] (F : Finset (FiniteGraph r)) (G : RGraph V r) :
    Decidable (familyHomFree F G) :=
  inferInstanceAs (Decidable (∀ A ∈ F, ¬ ∃ f, A.2.IsHom G f))

@[simp] theorem familyFree_singleton (A : FiniteGraph r) (G : RGraph V r) :
    familyFree {A} G ↔ ¬ ∃ f, A.2.IsEmbedding G f := by
  simp [familyFree]

@[simp] theorem familyHomFree_singleton (A : FiniteGraph r) (G : RGraph V r) :
    familyHomFree {A} G ↔ A.2.HomFree G := by
  simp [familyHomFree]

@[simp] theorem familyFree_empty_family (G : RGraph V r) : familyFree ∅ G := by
  simp [familyFree]

@[simp] theorem familyHomFree_empty_family (G : RGraph V r) : familyHomFree ∅ G := by
  simp [familyHomFree]

theorem familyHomFree_free (F : Finset (FiniteGraph r)) (G : RGraph V r)
    (hfree : familyHomFree F G) : familyFree F G :=
  fun A hA => (hfree A hA).free

theorem familyFree_of_embedding (F : Finset (FiniteGraph r))
    (G : RGraph V r) (H : RGraph W r) {f : V → W}
    (hf : G.IsEmbedding H f) (hfree : familyFree F H) : familyFree F G := by
  intro A hA h
  obtain ⟨g, hg⟩ := h
  exact hfree A hA ⟨f ∘ g, hf.comp hg⟩

theorem familyHomFree_of_hom (F : Finset (FiniteGraph r))
    (G : RGraph V r) (H : RGraph W r) {f : V → W}
    (hf : G.IsHom H f) (hfree : familyHomFree F H) : familyHomFree F G := by
  intro A hA h
  obtain ⟨g, hg⟩ := h
  exact hfree A hA ⟨f ∘ g, hf.comp hg⟩

theorem familyFree_pullback [Fintype V] (F : Finset (FiniteGraph r))
    (G : RGraph W r) (f : V ↪ W) (hfree : familyFree F G) :
    familyFree F (G.pullback f) :=
  familyFree_of_embedding F _ G ⟨f.injective, G.pullback_isHom f⟩ hfree

theorem familyFree_empty (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    familyFree F (RGraph.empty (Fin n) r) := by
  intro A hA
  exact A.2.empty_is_free (Finset.card_pos.mpr (hedges A hA))

theorem familyHomFree_blowup [Fintype V] (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyHomFree F G) (sizes : V → ℕ) :
    familyHomFree F (G.blowup sizes) :=
  fun A hA => A.2.blowup_homFree G (hfree A hA) sizes

theorem familyFree_blowup [Fintype V] (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyHomFree F G) (sizes : V → ℕ) :
    familyFree F (G.blowup sizes) :=
  familyHomFree_free F _ (familyHomFree_blowup F G hfree sizes)

end TuranUniversality
