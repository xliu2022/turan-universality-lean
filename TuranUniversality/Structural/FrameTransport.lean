module

public import TuranUniversality.Structural.FrameRoles
public import TuranUniversality.Structural.TripleAction

@[expose] public section

/-! # Transporting supports after role recovery -/

namespace TuranUniversality.Structural.Frame

open Cube Support TripleClasses

variable {V : Type*} [DecidableEq V] {b t : ℕ}

def vertexMap (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V) :
    Compiled.Vertex b t (Fin 5) → Compiled.Vertex b t V
  | .inl i => .inl (σ i)
  | .inr (.inl v) => .inr (.inl (blockMap π τ v))
  | .inr (.inr a) => .inr (.inr (d a))

theorem image_edge (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V)
    (Z : Finset (Support.Vertex b)) (X : Finset (Fin 5)) :
    (Compiled.edge t Z X).image (vertexMap σ π τ d) =
      Compiled.edge t (Z.image (blockMap π τ)) (X.image d) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    cases u with
    | inl i => simp [vertexMap]
    | inr u =>
      cases u with
      | inl u =>
        simp only [vertexMap, Compiled.mem_edge_block] at hu ⊢
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      | inr u =>
        simp only [vertexMap, Compiled.mem_edge_data] at hu ⊢
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · intro hv
    cases v with
    | inl i =>
      exact Finset.mem_image.mpr ⟨.inl (σ.symm i), by simp, by simp [vertexMap]⟩
    | inr v =>
      cases v with
      | inl v =>
        simp only [Compiled.mem_edge_block] at hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨.inr (.inl u), by simpa using hu, rfl⟩
      | inr v =>
        simp only [Compiled.mem_edge_data] at hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨.inr (.inr u), by simpa using hu, rfl⟩

theorem roles_eq_map {f : Compiled.Vertex b t (Fin 5) → Compiled.Vertex b t V}
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V)
    (hs : ∀ i, f (.inl i) = .inl (σ i))
    (hb : ∀ i a, f (.inr (.inl ⟨i, a⟩)) = .inr (.inl ⟨π i, τ i a⟩))
    (hd : ∀ a, f (.inr (.inr a)) = .inr (.inr (d a))) :
    f = vertexMap σ π τ d := by
  funext v
  cases v with
  | inl i => exact hs i
  | inr v =>
    cases v with
    | inl v => exact hb v.1 v.2
    | inr a => exact hd a

theorem transported_support {Ω : Finset (Word b)} {pools : Label → Finset (Word b)}
    {R : RecordSystem V} (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) (vertexMap σ π τ d))
    {X : Finset (Fin 5)} (hX : X.card = 4) {Z : Finset (Support.Vertex b)}
    (hZ : Z ∈ (poolGraph Ω).edges) :
    X.image d ∈ R.recorded.edges ∧
      Z.image (blockMap π τ) ∈ (poolGraph (pools (R.label (X.image d)))).edges := by
  have he := hf (Compiled.edge t Z X) ((mem_graph Ω _).mpr ⟨X, hX, Z, hZ, rfl⟩)
  rw [image_edge] at he
  obtain ⟨Y, hY, W, hW, heq⟩ := (Compiled.mem_graph pools R _).mp he
  have hp : (W, Y) = (Z.image (blockMap π τ), X.image d) := Compiled.edge_injective heq
  have hWy : W = Z.image (blockMap π τ) := congrArg Prod.fst hp
  have hYx : Y = X.image d := congrArg Prod.snd hp
  simpa only [hWy, hYx] using And.intro hY hW

end TuranUniversality.Structural.Frame
