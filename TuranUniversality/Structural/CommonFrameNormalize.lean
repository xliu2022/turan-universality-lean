module

public import TuranUniversality.Structural.CommonFrameCondition

@[expose] public section

/-! # Normalizing a sampled frame to the prescribed root roles

Sampling may return a frame with an allowed permutation of the root roles.
Precomposition by its inverse gives the prescribed roles while preserving
all replacements which match the sampled role. No conditional sampling
inside individual root classes is required.
-/

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem liftRoot_root (α : Equiv.Perm (Roots b t)) (r : Roots b t) :
    liftRoot (V := V) α (rootVertex V r) = rootVertex V (α r) := by
  simp [liftRoot, rootVertex]

theorem update_comp_equiv {A B : Type*} [DecidableEq A]
    (f : A → B) (π : Equiv.Perm A) (i : A) (y : B) :
    Function.update (f ∘ π) i y = Function.update f (π i) y ∘ π := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update_of_ne hj, Function.update_of_ne (π.injective.ne hj)]

def HasRoleMatchedFrame (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ : V → Option (Roots (CodePools.blockCount q) t)) (S : Finset V) : Prop :=
  ∃ f : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → V,
    (Frame.graph (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G f ∧
    ∀ y ∈ S, ∀ r, ρ y = ρ (f (rootVertex (Fin 5) r)) →
      (Frame.graph (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G
          (Function.update f (rootVertex (Fin 5) r) y)

theorem frame_roles_with_action (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ : V → Option (Roots (CodePools.blockCount q) t)) (R : RecordSystem V)
    (hh : G.IsHom (Compiled.graph t (CodePools.pool p q hpq) R) (place ρ))
    (f : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → V)
    (hf : (Frame.graph (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G f) :
    ∃ α : Equiv.Perm (Roots (CodePools.blockCount q) t),
      (Frame.graph (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
        (Frame.graph (CodePools.blockCount q) t
          (CodePools.pool p q hpq CodePools.neutralLabel)) (liftRoot α) ∧
      ∀ r, ρ (f (rootVertex (Fin 5) r)) = some (α r) := by
  obtain ⟨σ, π, τ, d, _, hmap, hact, _⟩ := Frame.rigidity p q hpq hq (hh.comp hf)
  refine ⟨blockRoot σ π τ, allowed_lift_hom p q hpq σ π τ hact Frame.neutralRecords, ?_⟩
  intro r
  apply (place_eq_root ρ _ _).mp
  cases r with
  | inl i => exact congrFun hmap (.inl i)
  | inr j => exact congrFun hmap (.inr (.inl j))

theorem HasRoleMatchedFrame.normalize (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    {G : RGraph V (t + (3 * CodePools.blockCount q + 4))}
    {ρ : V → Option (Roots (CodePools.blockCount q) t)} {S : Finset V}
    (hframe : HasRoleMatchedFrame p q hpq G ρ S)
    (R : RecordSystem V)
    (hh : G.IsHom (Compiled.graph t (CodePools.pool p q hpq) R) (place ρ)) :
    HasReplacementFrame p q hpq G ρ S := by
  obtain ⟨f, hf, hrepl⟩ := hframe
  obtain ⟨α, hα, hroot⟩ := frame_roles_with_action p q hpq hq G ρ R hh f hf
  have hinv : (Frame.graph (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Frame.graph (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)) (liftRoot α.symm) := by
    rw [liftRoot_symm]
    exact perm_hom_inverse _ _ hα
  refine ⟨f ∘ liftRoot α.symm, hf.comp hinv, ?_⟩
  intro y hy r hr
  have hmatch : ρ y = ρ (f (rootVertex (Fin 5) (α.symm r))) := by
    rw [hroot, Equiv.apply_symm_apply]
    exact hr
  rw [update_comp_equiv, liftRoot_root]
  exact (hrepl y hy (α.symm r) hmatch).comp hinv

end TuranUniversality.Structural.Roles
