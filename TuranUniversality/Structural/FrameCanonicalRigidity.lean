module

public import TuranUniversality.Structural.RoleActions

@[expose] public section

/-! # Common and replacement frames force the same actual root roles

The target graph may have arbitrarily large root classes. Rigidity is
applied after composing with its actual canonical quotient homomorphism.
Two frame permutations which agree away from one root agree everywhere.
-/

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def rootVertex (V : Type*) {b t : ℕ} (r : Roots b t) : Compiled.Vertex b t V :=
  (Equiv.sumAssoc (Fin t) (Support.Vertex b) V) (.inl r)

theorem place_eq_root (ρ : V → Option (Roots b t)) (v : V) (r : Roots b t) :
    place ρ v = rootVertex V r ↔ ρ v = some r := by
  cases h : ρ v with
  | none => cases r <;> simp [place, Selector.rootedVertex, h, rootVertex]
  | some k => cases k <;> cases r <;> simp [place, Selector.rootedVertex, h, rootVertex]

theorem frame_roles (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ : V → Option (Roots (CodePools.blockCount q) t)) (R : RecordSystem V)
    (hh : G.IsHom (Compiled.graph t (CodePools.pool p q hpq) R) (place ρ))
    (f : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → V)
    (hf : (Frame.graph (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G f) :
    ∃ α : Equiv.Perm (Roots (CodePools.blockCount q) t),
      (∀ R : RecordSystem V, (Compiled.graph t (CodePools.pool p q hpq) R).IsHom
        (Compiled.graph t (CodePools.pool p q hpq) R) (liftRoot α)) ∧
      (∀ r, ρ (f (rootVertex (Fin 5) r)) = some (α r)) ∧
      ∀ a : Fin 5, ρ (f (.inr (.inr a))) = none := by
  obtain ⟨σ, π, τ, d, _, hmap, hact, _⟩ := Frame.rigidity p q hpq hq (hh.comp hf)
  refine ⟨blockRoot σ π τ, allowed_lift_hom p q hpq σ π τ hact, ?_, ?_⟩
  · intro r
    apply (place_eq_root ρ _ _).mp
    cases r with
    | inl i =>
      have h := congrFun hmap (.inl i)
      exact h
    | inr j =>
      have h := congrFun hmap (.inr (.inl j))
      exact h
  · intro a
    have h := congrFun hmap (.inr (.inr a))
    exact ((Rooted.place_eq_data ρ _ (d a)).mp h).2

theorem replacement_frames_roles (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ σ : V → Option (Roots (CodePools.blockCount q) t)) (R : RecordSystem V)
    (hh : G.IsHom (Compiled.graph t (CodePools.pool p q hpq) R) (place σ))
    (S : Finset V)
    (f : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → V)
    (hf : (Frame.graph (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G f)
    (hrepl : ∀ y ∈ S, ∀ r, ρ y = some r →
      ∃ g : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → V,
        (Frame.graph (CodePools.blockCount q) t
          (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom G g ∧
        g (rootVertex (Fin 5) r) = y ∧
        ∀ j, j ≠ r → g (rootVertex (Fin 5) j) = f (rootVertex (Fin 5) j)) :
    ∃ α : Equiv.Perm (Roots (CodePools.blockCount q) t),
      (∀ R : RecordSystem V, (Compiled.graph t (CodePools.pool p q hpq) R).IsHom
        (Compiled.graph t (CodePools.pool p q hpq) R) (liftRoot α)) ∧
      ∀ y ∈ S, ∀ r, ρ y = some r → σ y = some (α r) := by
  obtain ⟨α, hα, hroot, _⟩ := frame_roles p q hpq hq G σ R hh f hf
  refine ⟨α, hα, ?_⟩
  intro y hy r hr
  obtain ⟨g, hg, hgr, hagree⟩ := hrepl y hy r hr
  obtain ⟨β, _, hroot', _⟩ := frame_roles p q hpq hq G σ R hh g hg
  have hβα : β = α := by
    apply permutations_eq_of_away β α r
    intro j hj
    apply Option.some.inj
    exact (hroot' j).symm.trans ((congrArg σ (hagree j hj)).trans (hroot j))
  simpa only [hgr, hβα] using hroot' r

theorem data_role_forced (Ω : Label → Finset (Cube.Word b))
    (ρ σ : V → Option (Roots b t)) (e : Finset V)
    (hρ : GoodEdge Ω ρ e) (hσ : GoodEdge Ω σ e)
    (hroots : ∀ w ∈ e, ∀ r, ρ w = some r → ∃ s, σ w = some s) :
    ∀ w ∈ e, ρ w = none → σ w = none := by
  have hsub : dataSet σ e ⊆ dataSet ρ e := by
    intro w hw
    obtain ⟨hwe, hσw⟩ := (mem_dataSet σ e w).mp hw
    apply (mem_dataSet ρ e w).mpr
    refine ⟨hwe, ?_⟩
    cases h : ρ w with
    | none => rfl
    | some r =>
      obtain ⟨s, hs⟩ := hroots w hwe r h
      simp [hσw] at hs
  have heq : dataSet σ e = dataSet ρ e :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hρ.1, hσ.1])
  intro w hw hnone
  have hmem : w ∈ dataSet σ e := by
    rw [heq]
    exact (mem_dataSet ρ e w).mpr ⟨hw, hnone⟩
  exact ((mem_dataSet σ e w).mp hmem).2

end TuranUniversality.Structural.Roles
