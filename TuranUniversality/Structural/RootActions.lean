module

public import TuranUniversality.Structural.FrameRigidity
public import Mathlib.GroupTheory.Perm.Finite

@[expose] public section

/-! # The concrete root permutations and their faithful parameters

The parameters are a reversal bit, a permutation of the suspension roots,
and one actual dihedral element in each five-point block. They act as
permutations of the ordinary frame carrier, fixing its data pointwise.
-/

namespace TuranUniversality.Structural.RootActions

open Cube Support TripleClasses Pentagon

def blockEquiv {b : ℕ} (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5)) :
    Equiv.Perm (Support.Vertex b) where
  toFun := blockMap π τ
  invFun v := ⟨π.symm v.1, (τ (π.symm v.1)).symm v.2⟩
  left_inv := by rintro ⟨i, a⟩; simp [blockMap]
  right_inv := by rintro ⟨i, a⟩; simp [blockMap]

def frameEquiv {b t : ℕ} (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) : Equiv.Perm (Compiled.Vertex b t (Fin 5)) :=
  Equiv.sumCongr σ (Equiv.sumCongr (blockEquiv π τ) (Equiv.refl _))

theorem frameEquiv_apply {b t : ℕ} (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (v : Compiled.Vertex b t (Fin 5)) :
    frameEquiv σ π τ v = Frame.vertexMap σ π τ id v := by
  cases v with
  | inl i => rfl
  | inr v => cases v <;> rfl

def phasePermutation (b : ℕ) (a : Bool) : Equiv.Perm (Fin b) :=
  if a then Fin.revPerm else Equiv.refl _

def localPermutation (a : Bool) (d : DihedralGroup 5) : Equiv.Perm (Fin 5) :=
  if a then doublePerm * dihedralPerm d else dihedralPerm d

theorem localPermutation_injective (a : Bool) : Function.Injective (localPermutation a) := by
  intro d e h
  cases a
  · exact dihedralPerm_injective h
  · exact dihedralPerm_injective (mul_left_cancel h)

abbrev Parameters (b t : ℕ) := Bool × (Equiv.Perm (Fin t) × (Fin b → DihedralGroup 5))

def action {b t : ℕ} (a : Parameters b t) : Equiv.Perm (Compiled.Vertex b t (Fin 5)) :=
  frameEquiv a.2.1 (phasePermutation b a.1) (fun i => localPermutation a.1 (a.2.2 i))

@[simp] theorem action_susp {b t : ℕ} (a : Parameters b t) (i : Fin t) :
    action a (.inl i) = .inl (a.2.1 i) := rfl

@[simp] theorem action_block {b t : ℕ} (a : Parameters b t) (i : Fin b) (j : Fin 5) :
    action a (.inr (.inl ⟨i, j⟩)) =
      .inr (.inl ⟨phasePermutation b a.1 i, localPermutation a.1 (a.2.2 i) j⟩) := rfl

@[simp] theorem action_data {b t : ℕ} (a : Parameters b t) (j : Fin 5) :
    action a (.inr (.inr j)) = .inr (.inr j) := rfl

theorem allowed (b t : ℕ) (a : Parameters b t) :
    Frame.AllowedBlockAction (phasePermutation b a.1) (fun i => localPermutation a.1 (a.2.2 i)) := by
  rcases a with ⟨a, σ, d⟩
  cases a
  · refine Or.inl ⟨rfl, ?_⟩
    intro i η
    exact preserving_both _ (dihedralPerm_mem (d i)) η
  · refine Or.inr ⟨rfl, ?_⟩
    intro i η
    apply exchanging_both
    exact (exchanging_iff_dihedral _).mpr ⟨d i, rfl⟩

theorem action_injective {b t : ℕ} (hb : 2 ≤ b) : Function.Injective (@action b t) := by
  intro a c hac
  have hphase : a.1 = c.1 := by
    let i : Fin b := ⟨0, by omega⟩
    let coordinate : Compiled.Vertex b t (Fin 5) → ℕ
      | .inr (.inl v) => v.1.val
      | _ => 0
    have h := congrArg (fun e : Equiv.Perm (Compiled.Vertex b t (Fin 5)) =>
      coordinate (e (.inr (.inl ⟨i, 0⟩)))) hac
    cases ha : a.1 <;> cases hc : c.1 <;>
      simp [action_block, coordinate, phasePermutation, ha, hc, i, Fin.rev] at h ⊢ <;> omega
  have hσ : a.2.1 = c.2.1 := by
    apply Equiv.ext
    intro i
    have h := congrArg (fun e : Equiv.Perm (Compiled.Vertex b t (Fin 5)) => e (.inl i)) hac
    exact Sum.inl.inj h
  have hd : a.2.2 = c.2.2 := by
    funext i
    apply localPermutation_injective a.1
    apply Equiv.ext
    intro j
    have h := congrArg (fun e : Equiv.Perm (Compiled.Vertex b t (Fin 5)) =>
      e (.inr (.inl ⟨i, j⟩))) hac
    rw [action_block, action_block, ← hphase] at h
    exact congrArg (fun v : Support.Vertex b => v.2) (Sum.inl.inj (Sum.inr.inj h))
  exact Prod.ext hphase (Prod.ext hσ hd)

theorem parameters_card (b t : ℕ) : Fintype.card (Parameters b t) = 2 * 10 ^ b * t.factorial := by
  simp only [Parameters, Fintype.card_prod, Fintype.card_bool, Fintype.card_perm,
    Fintype.card_fun, Fintype.card_fin, DihedralGroup.card]
  norm_num
  ring

theorem action_isHom (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (a : Parameters (CodePools.blockCount q) t) :
    (Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)) (action a) := by
  have h := Frame.frame_action p q hpq a.2.1 (phasePermutation _ a.1)
    (fun i => localPermutation a.1 (a.2.2 i)) (allowed _ _ a)
  have heq : (action a : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) → _) =
      Frame.vertexMap a.2.1 (phasePermutation _ a.1) (fun i => localPermutation a.1 (a.2.2 i)) id := by
    funext v; exact frameEquiv_apply _ _ _ v
  exact heq ▸ h

end TuranUniversality.Structural.RootActions
