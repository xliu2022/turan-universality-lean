module

public import TuranUniversality.Structural.CanonicalLocal
public import TuranUniversality.Structural.RootActions

@[expose] public section

/-! # Allowed root actions on arbitrary canonical presentations -/

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def liftRoot (π : Equiv.Perm (Roots b t)) : Equiv.Perm (Compiled.Vertex b t V) :=
  (Equiv.sumAssoc (Fin t) (Support.Vertex b) V).symm.trans
    ((Equiv.sumCongr π (Equiv.refl V)).trans (Equiv.sumAssoc (Fin t) (Support.Vertex b) V))

def renameRoles (π : Equiv.Perm (Roots b t)) (ρ : V → Option (Roots b t)) :
    V → Option (Roots b t) := fun v => (ρ v).map π

theorem liftRoot_symm (π : Equiv.Perm (Roots b t)) :
    liftRoot (V := V) π.symm = (liftRoot π).symm := by
  rfl

theorem place_renameRoles (π : Equiv.Perm (Roots b t)) (ρ : V → Option (Roots b t)) (v : V) :
    place (renameRoles π ρ) v = liftRoot π (place ρ v) := by
  cases h : ρ v with
  | none => simp [renameRoles, place, Selector.rootedVertex, h, liftRoot]
  | some r =>
    cases r <;> simp [renameRoles, place, Selector.rootedVertex, h, liftRoot]

theorem perm_hom_inverse {A : Type*} [DecidableEq A] {r : ℕ}
    (G : RGraph A r) (π : Equiv.Perm A) (hπ : G.IsHom G π) : G.IsHom G π.symm := by
  have hi : Function.Injective (fun e : Finset A => e.image π) := by
    intro e f h
    have hh := congrArg (fun e : Finset A => e.image π.symm) h
    simpa [Finset.image_image, Function.comp_def] using hh
  have heq : G.edges.image (fun e => e.image π) = G.edges := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      exact hπ d hd
    · rw [Finset.card_image_of_injective _ hi]
  intro e he
  rw [← heq] at he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  simpa [Finset.image_image, Function.comp_def] using hd

theorem admissible_rename (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (π : Equiv.Perm (Roots b t))
    (hπ : ∀ R : RecordSystem V, (Compiled.graph t Ω R).IsHom
      (Compiled.graph t Ω R) (liftRoot π))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t))
    (hρ : Admissible B Ω G ρ) : Admissible B Ω G (renameRoles π ρ) := by
  obtain ⟨R, _, hR, hh⟩ := extract_records B Ω hdis G ρ hρ
  apply admissible_of_records B Ω G _ R hR
  have hf := (hπ R).comp hh
  have heq : place (renameRoles π ρ) = liftRoot π ∘ place ρ :=
    funext (place_renameRoles π ρ)
  rw [heq]
  exact hf

def blockRoot (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) : Equiv.Perm (Roots b t) :=
  Equiv.sumCongr σ (RootActions.blockEquiv π τ)

theorem liftRoot_block_susp (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (i : Fin t) :
    liftRoot (V := V) (blockRoot σ π τ) (.inl i) = .inl (σ i) := rfl

theorem liftRoot_block_code (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (v : Support.Vertex b) :
    liftRoot (V := V) (blockRoot σ π τ) (.inr (.inl v)) =
      .inr (.inl (TripleClasses.blockMap π τ v)) := rfl

theorem liftRoot_block_data (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (v : V) :
    liftRoot (blockRoot σ π τ) (.inr (.inr v)) = .inr (.inr v) := rfl

theorem image_edge (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (Z : Finset (Support.Vertex b)) (X : Finset V) :
    (Compiled.edge t Z X).image (liftRoot (blockRoot σ π τ)) =
      Compiled.edge t (Z.image (TripleClasses.blockMap π τ)) X := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rcases u with i | (u | u)
    · simp [liftRoot_block_susp]
    · rw [liftRoot_block_code, Compiled.mem_edge_block]
      exact Finset.mem_image.mpr ⟨u, (Compiled.mem_edge_block _ _ _).mp hu, rfl⟩
    · simpa only [liftRoot_block_data, Compiled.mem_edge_data] using hu
  · intro hv
    rcases v with i | (v | v)
    · exact Finset.mem_image.mpr ⟨.inl (σ.symm i), by simp,
        by simp only [liftRoot_block_susp, Equiv.apply_symm_apply]⟩
    · rw [Compiled.mem_edge_block] at hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨.inr (.inl u), by simpa using hu, rfl⟩
    · exact Finset.mem_image.mpr ⟨.inr (.inr v), by simpa only [Compiled.mem_edge_data] using hv, rfl⟩

theorem allowed_lift_hom (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5))
    (hact : Frame.AllowedBlockAction π τ) (R : RecordSystem V) :
    (Compiled.graph t (CodePools.pool p q hpq) R).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) R) (liftRoot (blockRoot σ π τ)) := by
  intro e he
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (Compiled.mem_graph _ _ _).mp he
  rw [image_edge]
  exact (Compiled.mem_graph _ _ _).mpr ⟨X, hX, Z.image (TripleClasses.blockMap π τ),
    Frame.allowed_pool_preservation p q hpq π τ hact _ Z hZ, rfl⟩

theorem permutations_eq_of_away {A : Type*} (α β : Equiv.Perm A) (i : A)
    (h : ∀ j, j ≠ i → α j = β j) : α = β := by
  apply Equiv.ext
  intro j
  by_cases hji : j = i
  · subst j
    have hi : α.symm (β i) = i := by
      by_contra hne
      exact hne (β.injective ((h _ hne).symm.trans (α.apply_symm_apply _)))
    simpa only [Equiv.apply_symm_apply] using (congrArg α hi).symm
  · exact h j hji

end TuranUniversality.Structural.Roles
