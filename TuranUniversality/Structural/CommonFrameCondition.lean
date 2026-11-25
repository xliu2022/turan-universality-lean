module

public import TuranUniversality.Structural.FrameCanonicalRigidity

@[expose] public section

/-! # The finite common-frame condition used for vertex extension

Every replacement changes just the indicated formal root. Both the common
frame and all replacements are actual homomorphisms into the ordinary
graph, and pair coverage makes these maps ordinary embeddings.
-/

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem rootVertex_injective (V : Type*) {b t : ℕ} :
    Function.Injective (rootVertex V (b := b) (t := t)) :=
  (Equiv.sumAssoc (Fin t) (Support.Vertex b) V).injective.comp Sum.inl_injective

def HasReplacementFrame (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ : V → Option (Roots (CodePools.blockCount q) t)) (S : Finset V) : Prop :=
  ∃ f : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → V,
    (Frame.graph (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G f ∧
    ∀ y ∈ S, ∀ r, ρ y = some r →
      (Frame.graph (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G
          (Function.update f (rootVertex (Fin 5) r) y)

theorem HasReplacementFrame.roles (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    {G : RGraph V (t + (3 * CodePools.blockCount q + 4))}
    {ρ σ : V → Option (Roots (CodePools.blockCount q) t)} {S : Finset V}
    (hframe : HasReplacementFrame p q hpq G ρ S)
    (R : RecordSystem V)
    (hh : G.IsHom (Compiled.graph t (CodePools.pool p q hpq) R) (place σ)) :
    ∃ α : Equiv.Perm (Roots (CodePools.blockCount q) t),
      (∀ R : RecordSystem V, (Compiled.graph t (CodePools.pool p q hpq) R).IsHom
        (Compiled.graph t (CodePools.pool p q hpq) R) (liftRoot α)) ∧
      ∀ y ∈ S, ∀ r, ρ y = some r → σ y = some (α r) := by
  obtain ⟨f, hf, hrepl⟩ := hframe
  apply replacement_frames_roles p q hpq hq G ρ σ R hh S f hf
  intro y hy r hr
  refine ⟨Function.update f (rootVertex (Fin 5) r) y, hrepl y hy r hr,
    Function.update_self _ _ _, ?_⟩
  intro j hj
  exact Function.update_of_ne (fun h => hj (rootVertex_injective _ h)) _ _

end TuranUniversality.Structural.Roles
