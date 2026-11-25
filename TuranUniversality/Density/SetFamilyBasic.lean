module

public import TuranUniversality.Density.FamilyBasic

@[expose] public section

/-! # Ordinary and homomorphism avoidance for arbitrary forbidden families

The forbidden family is a set of labelled finite simple uniform hypergraphs.
Ordinary embeddings are globally injective, including on isolated vertices.
Truncation by source order is finite even when family membership is not
decidable; the mathematical truncation does not claim such a decision procedure.
-/

namespace TuranUniversality.SetFamily

universe u v

variable {r : ℕ} {V : Type u} {W : Type v}
  [DecidableEq V] [DecidableEq W]

def Free (F : Set (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, ¬ ∃ f, A.2.IsEmbedding G f

def HomFree (F : Set (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, A.2.HomFree G

@[simp] theorem free_finset (F : Finset (FiniteGraph r)) (G : RGraph V r) :
    Free (F : Set (FiniteGraph r)) G ↔ familyFree F G := Iff.rfl

@[simp] theorem homFree_finset (F : Finset (FiniteGraph r)) (G : RGraph V r) :
    HomFree (F : Set (FiniteGraph r)) G ↔ familyHomFree F G := Iff.rfl

@[simp] theorem free_empty (G : RGraph V r) : Free ∅ G := by
  simp [Free]

@[simp] theorem homFree_empty (G : RGraph V r) : HomFree ∅ G := by
  simp [HomFree]

theorem Free.mono {F H : Set (FiniteGraph r)} (hFH : F ⊆ H)
    {G : RGraph V r} (hG : Free H G) : Free F G :=
  fun A hA => hG A (hFH hA)

theorem HomFree.mono {F H : Set (FiniteGraph r)} (hFH : F ⊆ H)
    {G : RGraph V r} (hG : HomFree H G) : HomFree F G :=
  fun A hA => hG A (hFH hA)

theorem HomFree.free {F : Set (FiniteGraph r)} {G : RGraph V r}
    (hG : HomFree F G) : Free F G :=
  fun A hA => (hG A hA).free

theorem Free.of_embedding (F : Set (FiniteGraph r))
    (G : RGraph V r) (H : RGraph W r) {f : V → W}
    (hf : G.IsEmbedding H f) (hH : Free F H) : Free F G := by
  rintro A hA ⟨g, hg⟩
  exact hH A hA ⟨f ∘ g, hf.comp hg⟩

theorem HomFree.of_hom (F : Set (FiniteGraph r))
    (G : RGraph V r) (H : RGraph W r) {f : V → W}
    (hf : G.IsHom H f) (hH : HomFree F H) : HomFree F G := by
  rintro A hA ⟨g, hg⟩
  exact hH A hA ⟨f ∘ g, hf.comp hg⟩

theorem Free.pullback [Fintype V] (F : Set (FiniteGraph r))
    (G : RGraph W r) (f : V ↪ W) (hG : Free F G) : Free F (G.pullback f) :=
  Free.of_embedding F _ G ⟨f.injective, G.pullback_isHom f⟩ hG

theorem free_emptyGraph (F : Set (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    Free F (RGraph.empty (Fin n) r) :=
  fun A hA => A.2.empty_is_free (Finset.card_pos.mpr (hedges A hA))

theorem homFree_emptyGraph (F : Set (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    HomFree F (RGraph.empty (Fin n) r) := by
  rintro A hA ⟨f, hf⟩
  obtain ⟨e, he⟩ := hedges A hA
  exact Finset.notMem_empty _ (hf e he)

theorem HomFree.blowup [Fintype V] (F : Set (FiniteGraph r))
    (G : RGraph V r) (hG : HomFree F G) (sizes : V → ℕ) :
    HomFree F (G.blowup sizes) :=
  fun A hA => A.2.blowup_homFree G (hG A hA) sizes

theorem Free.blowup [Fintype V] (F : Set (FiniteGraph r))
    (G : RGraph V r) (hG : HomFree F G) (sizes : V → ℕ) :
    Free F (G.blowup sizes) := (HomFree.blowup F G hG sizes).free

theorem not_free_of_edgeless (F : Set (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (he : A.2.edges = ∅)
    {n : ℕ} (hn : A.1 ≤ n) (G : RGraph (Fin n) r) : ¬ Free F G := by
  intro hG
  apply hG A hA
  refine ⟨Fin.castLE hn, Fin.castLE_injective hn, ?_⟩
  intro e he'
  simp [he] at he'

noncomputable section

def truncate (F : Set (FiniteGraph r)) (n : ℕ) : Finset (FiniteGraph r) := by
  classical
  exact (FiniteGraph.bounded r n).filter (fun A => A ∈ F)

@[simp] theorem mem_truncate (F : Set (FiniteGraph r)) (n : ℕ) (A : FiniteGraph r) :
    A ∈ truncate F n ↔ A.1 ≤ n ∧ A ∈ F := by
  classical
  simp [truncate]

theorem truncate_subset (F : Set (FiniteGraph r)) (n : ℕ) :
    (truncate F n : Set (FiniteGraph r)) ⊆ F :=
  fun A hA => ((mem_truncate F n A).mp hA).2

theorem truncate_mono (F : Set (FiniteGraph r)) {n m : ℕ} (h : n ≤ m) :
    truncate F n ⊆ truncate F m := by
  intro A hA
  obtain ⟨hn, hF⟩ := (mem_truncate F n A).mp hA
  exact (mem_truncate F m A).mpr ⟨hn.trans h, hF⟩

theorem finite_subset_truncate (F : Set (FiniteGraph r)) (E : Finset (FiniteGraph r))
    (hE : (E : Set (FiniteGraph r)) ⊆ F) :
    E ⊆ truncate F (E.sup fun A => A.1) := by
  intro A hA
  exact (mem_truncate F _ A).mpr
    ⟨Finset.le_sup (f := fun B : FiniteGraph r => B.1) hA, hE hA⟩

/-- Larger forbidden graphs cannot embed in an n-vertex host. -/
theorem free_truncate_iff (F : Set (FiniteGraph r)) (n : ℕ) (G : RGraph (Fin n) r) :
    familyFree (truncate F n) G ↔ Free F G := by
  constructor
  · intro hG A hA
    rintro ⟨f, hf⟩
    have hn : A.1 ≤ n := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf.1
    exact hG A ((mem_truncate F n A).mpr ⟨hn, hA⟩) ⟨f, hf⟩
  · intro hG
    exact hG.mono (truncate_subset F n)

end
end TuranUniversality.SetFamily
