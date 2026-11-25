module

public import TuranUniversality.Structural.RootGroup
public import TuranUniversality.Structural.RecordComplete
public import TuranUniversality.Uniformity.Extensions

@[expose] public section

/-! # The actual ordinary readback test

The test consists of the neutral frame, a disjoint copy of the inner
three-graph, and one added edge for each inner edge. All added edges use
one fixed support and the same distinguished frame data vertex. In
particular, the test does not expand each added record by a whole pool.
-/

namespace TuranUniversality.Structural.Readback

open Cube Support TripleClasses

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

abbrev FrameVertex (b t : ℕ) := Compiled.Vertex b t (Fin 5)
abbrev Vertex (b t : ℕ) (U : Type*) := FrameVertex b t ⊕ U

def addedEdge {b : ℕ} (t : ℕ) (Z : Finset (Support.Vertex b)) (e : Finset U) :
    Finset (Vertex b t U) := (Compiled.edge t Z {0}).disjSum e

@[simp] theorem mem_added_frame {b t : ℕ} (Z : Finset (Support.Vertex b))
    (e : Finset U) (v : FrameVertex b t) :
    Sum.inl v ∈ addedEdge t Z e ↔ v ∈ Compiled.edge t Z {0} := by
  simp [addedEdge]

@[simp] theorem mem_added_inner {b t : ℕ} (Z : Finset (Support.Vertex b))
    (e : Finset U) (v : U) : Sum.inr v ∈ addedEdge t Z e ↔ v ∈ e := by
  simp [addedEdge]

theorem addedEdge_card {b : ℕ} (t : ℕ) (Z : Finset (Support.Vertex b))
    (e : Finset U) : (addedEdge t Z e).card = t + (Z.card + 1) + e.card := by
  simp [addedEdge, Compiled.edge_card]

def test {b : ℕ} (t : ℕ) (Ω : Finset (Word b)) (Z : Finset (Support.Vertex b))
    (hZ : Z.card = 3 * b) (F : RGraph U 3) : RGraph (Vertex b t U) (t + (3 * b + 4)) where
  edges := (Frame.graph b t Ω).edges.image (fun e => e.image Sum.inl) ∪
    F.edges.image (addedEdge t Z)
  uniform := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
      exact (Frame.graph b t Ω).uniform d hd
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      rw [addedEdge_card, hZ, F.uniform d hd]
      omega

theorem frame_inclusion {b : ℕ} (t : ℕ) (Ω : Finset (Word b))
    (Z : Finset (Support.Vertex b)) (hZ : Z.card = 3 * b) (F : RGraph U 3) :
    (Frame.graph b t Ω).IsEmbedding (test t Ω Z hZ F) Sum.inl := by
  refine ⟨Sum.inl_injective, ?_⟩
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem addedEdge_mem {b : ℕ} (t : ℕ) (Ω : Finset (Word b))
    (Z : Finset (Support.Vertex b)) (hZ : Z.card = 3 * b) (F : RGraph U 3)
    {e : Finset U} (he : e ∈ F.edges) : addedEdge t Z e ∈ (test t Ω Z hZ F).edges :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem isHom_iff {b t : ℕ} (Ω : Finset (Word b))
    (Z : Finset (Support.Vertex b)) (hZ : Z.card = 3 * b) (F : RGraph U 3)
    (G : RGraph V (t + (3 * b + 4))) (f : Vertex b t U → V) :
    (test t Ω Z hZ F).IsHom G f ↔
      (Frame.graph b t Ω).IsHom G (f ∘ Sum.inl) ∧
        ∀ e ∈ F.edges, (addedEdge t Z e).image f ∈ G.edges := by
  constructor
  · intro hf
    exact ⟨hf.comp (frame_inclusion t Ω Z hZ F).isHom,
      fun e he => hf _ (addedEdge_mem t Ω Z hZ F he)⟩
  · rintro ⟨hframe, hinner⟩ e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      simpa [Finset.image_image] using hframe d hd
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      exact hinner d hd

def dataVertex {b t : ℕ} (v : V) : Compiled.Vertex b t V := .inr (.inr v)

def extend {b t : ℕ} (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V) (g : U → V) :
    Vertex b t U → Compiled.Vertex b t V :=
  Sum.elim (Frame.vertexMap σ π τ d) (fun u => dataVertex (g u))

theorem image_addedEdge {b t : ℕ} (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V) (g : U → V)
    (Z : Finset (Support.Vertex b)) (e : Finset U) :
    (addedEdge t Z e).image (extend σ π τ d g) =
      Compiled.edge t (Z.image (blockMap π τ)) (insert (d 0) (e.image g)) := by
  ext v
  cases v with
  | inl i =>
    constructor
    · intro _; simp
    · intro _
      exact Finset.mem_image.mpr ⟨.inl (.inl (σ.symm i)), by simp, by simp [extend, Frame.vertexMap]⟩
  | inr v =>
    cases v with
    | inl v =>
      simp only [Finset.mem_image, Compiled.mem_edge_block]
      constructor
      · rintro ⟨u, hu, huf⟩
        cases u with
        | inl u =>
          cases u with
          | inl i => simp [extend, Frame.vertexMap] at huf
          | inr u =>
            cases u with
            | inl u =>
              exact ⟨u, by simpa using hu, by simpa [extend, Frame.vertexMap] using huf⟩
            | inr a => simp [extend, Frame.vertexMap] at huf
        | inr u => simp [extend, dataVertex] at huf
      · rintro ⟨u, hu, rfl⟩
        exact ⟨.inl (.inr (.inl u)), by simpa using hu, rfl⟩
    | inr v =>
      simp only [Finset.mem_image, Compiled.mem_edge_data, Finset.mem_insert]
      constructor
      · rintro ⟨u, hu, huf⟩
        cases u with
        | inl u =>
          cases u with
          | inl i => simp [extend, Frame.vertexMap] at huf
          | inr u =>
            cases u with
            | inl u => simp [extend, Frame.vertexMap] at huf
            | inr a =>
              have ha : a = 0 := by simpa using hu
              subst a
              exact Or.inl (by simpa [extend, Frame.vertexMap] using huf.symm)
        | inr u => exact Or.inr ⟨u, by simpa using hu, by simpa [extend, dataVertex] using huf⟩
      · rintro (rfl | ⟨u, hu, rfl⟩)
        · exact ⟨.inl (.inr (.inr 0)), by simp, rfl⟩
        · exact ⟨.inr u, by simpa using hu, rfl⟩

end TuranUniversality.Structural.Readback
