module

public import TuranUniversality.Structural.TripleClasses
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

@[expose] public section

/-! # The actual pentagon automorphism group

The subgroup of five-point permutations preserving `P0` is explicitly
identified with `DihedralGroup 5`. The other triple-class bijections form
the coset obtained by multiplication by two. All finite classifications
use kernel-reduced decidability, not a native evaluation oracle.
-/

namespace TuranUniversality.Structural.Pentagon

open TripleClasses

def edgeAction (τ : Equiv.Perm (Fin 5)) (E : Finset (Finset (Fin 5))) :=
  E.image (fun e => e.image τ)

@[simp] theorem edgeAction_one (E : Finset (Finset (Fin 5))) : edgeAction 1 E = E := by
  simp [edgeAction]

theorem edgeAction_mul (σ τ : Equiv.Perm (Fin 5)) (E : Finset (Finset (Fin 5))) :
    edgeAction (σ * τ) E = edgeAction σ (edgeAction τ E) := by
  simp [edgeAction, Finset.image_image, Function.comp_def, Equiv.Perm.mul_apply]

/-- The actual stabilizer of the five cyclic triples. -/
def phasePreserving : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {τ | edgeAction τ P0.edges = P0.edges}
  one_mem' := edgeAction_one _
  mul_mem' := by
    intro σ τ hσ hτ
    change edgeAction (σ * τ) P0.edges = P0.edges
    rw [edgeAction_mul, hτ, hσ]
  inv_mem' := by
    intro τ hτ
    change edgeAction τ⁻¹ P0.edges = P0.edges
    have h := congrArg (edgeAction τ⁻¹) hτ
    rw [← edgeAction_mul, inv_mul_cancel, edgeAction_one] at h
    exact h.symm

@[simp] theorem mem_phasePreserving (τ : Equiv.Perm (Fin 5)) :
    τ ∈ phasePreserving ↔ imageEdges τ false = P0.edges := Iff.rfl

instance : DecidablePred (· ∈ phasePreserving) := fun τ =>
  inferInstanceAs (Decidable (edgeAction τ P0.edges = P0.edges))

def rotation (c : Fin 5) : Equiv.Perm (Fin 5) where
  toFun x := x + c
  invFun x := x - c
  left_inv x := add_sub_cancel_right x c
  right_inv x := sub_add_cancel x c

def reflection (c : Fin 5) : Equiv.Perm (Fin 5) where
  toFun x := -x - c
  invFun x := -x - c
  left_inv x := by simp
  right_inv x := by simp

/-- The standard dihedral action: `r c` translates by `c`, while `sr c`
acts by `x ↦ -x-c`, matching Mathlib's multiplication convention. -/
def dihedralPerm : DihedralGroup 5 → Equiv.Perm (Fin 5)
  | .r c => rotation c
  | .sr c => reflection c

set_option maxRecDepth 8000 in
theorem dihedralPerm_mul : ∀ d e : DihedralGroup 5,
    dihedralPerm (d * e) = dihedralPerm d * dihedralPerm e := by
  decide

def dihedralHom : DihedralGroup 5 →* Equiv.Perm (Fin 5) where
  toFun := dihedralPerm
  map_one' := by decide
  map_mul' := dihedralPerm_mul

set_option maxRecDepth 8000 in
theorem dihedralPerm_injective : Function.Injective dihedralPerm := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem preserving_iff_dihedral : ∀ τ : Equiv.Perm (Fin 5),
    τ ∈ phasePreserving ↔ ∃ d : DihedralGroup 5, dihedralPerm d = τ := by
  decide

theorem dihedralPerm_mem (d : DihedralGroup 5) : dihedralPerm d ∈ phasePreserving :=
  (preserving_iff_dihedral _).mpr ⟨d, rfl⟩

def dihedralInto : DihedralGroup 5 →* phasePreserving where
  toFun d := ⟨dihedralPerm d, dihedralPerm_mem d⟩
  map_one' := Subtype.ext dihedralHom.map_one
  map_mul' d e := Subtype.ext (dihedralPerm_mul d e)

theorem dihedralInto_bijective : Function.Bijective dihedralInto := by
  constructor
  · intro d e h
    exact dihedralPerm_injective (congrArg Subtype.val h)
  · rintro ⟨τ, hτ⟩
    obtain ⟨d, hd⟩ := (preserving_iff_dihedral τ).mp hτ
    exact ⟨d, Subtype.ext hd⟩

noncomputable def dihedralEquiv : DihedralGroup 5 ≃* phasePreserving :=
  MulEquiv.ofBijective dihedralInto dihedralInto_bijective

theorem phasePreserving_card : Fintype.card phasePreserving = 10 := by
  rw [← Fintype.card_congr dihedralEquiv.toEquiv]
  exact DihedralGroup.card

set_option maxRecDepth 8000 in
theorem preserving_both : ∀ τ : Equiv.Perm (Fin 5), τ ∈ phasePreserving →
    ∀ a : Bool, imageEdges τ a = (graph a).edges := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem exchanging_iff_dihedral : ∀ τ : Equiv.Perm (Fin 5),
    imageEdges τ false = P1.edges ↔
      ∃ d : DihedralGroup 5, doublePerm * dihedralPerm d = τ := by
  decide

set_option maxRecDepth 8000 in
theorem exchanging_both : ∀ τ : Equiv.Perm (Fin 5), imageEdges τ false = P1.edges →
    ∀ a : Bool, imageEdges τ a = (graph (!a)).edges := by
  decide

theorem doublePerm_square : doublePerm * doublePerm = reflection 0 := by
  decide

theorem doublePerm_not_mem : doublePerm ∉ phasePreserving := by
  decide

set_option maxRecDepth 8000 in
theorem doublePerm_normalizes : ∀ τ : Equiv.Perm (Fin 5), τ ∈ phasePreserving →
    doublePerm * τ * doublePerm⁻¹ ∈ phasePreserving := by
  decide

theorem exchanging_count :
    (Finset.univ.filter fun τ : Equiv.Perm (Fin 5) =>
      imageEdges τ false = P1.edges).card = 10 := by
  decide

end TuranUniversality.Structural.Pentagon
