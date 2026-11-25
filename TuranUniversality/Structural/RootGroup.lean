module

public import TuranUniversality.Structural.RootActions

@[expose] public section

/-! # The actual neutral-frame root group

This is a subgroup of permutations of the ordinary frame carrier: it fixes
data pointwise and preserves the actual edge set. Rigidity identifies all
of its elements with the faithful dihedral/reversal parameters, proving
the exact order used in the readback coefficient.
-/

namespace TuranUniversality.Structural.RootActions

open Cube Support TripleClasses Pentagon

def edgeSetAction {A : Type*} [DecidableEq A] (σ : Equiv.Perm A)
    (E : Finset (Finset A)) : Finset (Finset A) := E.image fun e => e.image σ

@[simp] theorem edgeSetAction_one {A : Type*} [DecidableEq A] (E : Finset (Finset A)) :
    edgeSetAction (1 : Equiv.Perm A) E = E := by simp [edgeSetAction]

theorem edgeSetAction_mul {A : Type*} [DecidableEq A] (σ τ : Equiv.Perm A)
    (E : Finset (Finset A)) :
    edgeSetAction (σ * τ) E = edgeSetAction σ (edgeSetAction τ E) := by
  simp [edgeSetAction, Finset.image_image, Function.comp_def]

theorem edgeSetAction_eq_of_hom {A : Type*} [DecidableEq A] {r : ℕ}
    (G : RGraph A r) (σ : Equiv.Perm A) (h : G.IsHom G σ) :
    edgeSetAction σ G.edges = G.edges := by
  have hinj : Function.Injective (fun e : Finset A => e.image σ) := by
    intro e f hef
    have h' := congrArg (fun e : Finset A => e.image σ.symm) hef
    simpa [Finset.image_image, Function.comp_def] using h'
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact h d hd
  · rw [edgeSetAction, Finset.card_image_of_injective _ hinj]

theorem isHom_of_edgeSetAction_eq {A : Type*} [DecidableEq A] {r : ℕ}
    (G : RGraph A r) (σ : Equiv.Perm A) (h : edgeSetAction σ G.edges = G.edges) :
    G.IsHom G σ := by
  intro e he
  rw [← h]
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

def group (b t : ℕ) (Ω : Finset (Word b)) :
    Subgroup (Equiv.Perm (Compiled.Vertex b t (Fin 5))) where
  carrier := {σ | edgeSetAction σ (Frame.graph b t Ω).edges = (Frame.graph b t Ω).edges ∧
    ∀ a : Fin 5, σ (.inr (.inr a)) = .inr (.inr a)}
  one_mem' := ⟨edgeSetAction_one _, fun _ => rfl⟩
  mul_mem' := by
    intro σ τ hσ hτ
    refine ⟨?_, ?_⟩
    · rw [edgeSetAction_mul, hτ.1, hσ.1]
    · intro a
      change σ (τ (.inr (.inr a))) = _
      rw [hτ.2 a, hσ.2 a]
  inv_mem' := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · have h := congrArg (edgeSetAction σ⁻¹) hσ.1
      rw [← edgeSetAction_mul, inv_mul_cancel, edgeSetAction_one] at h
      exact h.symm
    · intro a
      apply σ.injective
      change σ (σ.symm (.inr (.inr a))) = σ (.inr (.inr a))
      rw [Equiv.apply_symm_apply, hσ.2 a]

instance groupMembershipDecidable (b t : ℕ) (Ω : Finset (Word b)) :
    DecidablePred (· ∈ group b t Ω) := fun σ =>
  inferInstanceAs (Decidable (edgeSetAction σ (Frame.graph b t Ω).edges = (Frame.graph b t Ω).edges ∧
    ∀ a : Fin 5, σ (.inr (.inr a)) = .inr (.inr a)))

theorem action_mem (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (a : Parameters (CodePools.blockCount q) t) :
    action a ∈ group (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel) :=
  ⟨edgeSetAction_eq_of_hom _ _ (action_isHom p q hpq a), action_data a⟩

def intoGroup (p q : ℕ) (hpq : p ≤ q) (t : ℕ)
    (a : Parameters (CodePools.blockCount q) t) :
    group (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel) :=
  ⟨action a, action_mem p q hpq a⟩

theorem normal_form_represented {b t : ℕ} (σ : Equiv.Perm (Fin t))
    (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5))
    (hact : Frame.AllowedBlockAction π τ) :
    ∃ a : Parameters b t, action a = frameEquiv σ π τ := by
  classical
  rcases hact with ⟨rfl, hτ⟩ | ⟨rfl, hτ⟩
  · have hd (i : Fin b) : ∃ d : DihedralGroup 5, dihedralPerm d = τ i :=
      (preserving_iff_dihedral _).mp ((mem_phasePreserving _).mpr (hτ i false))
    choose d hd using hd
    refine ⟨⟨false, σ, d⟩, ?_⟩
    change frameEquiv σ (Equiv.refl _) (fun i => dihedralPerm (d i)) = _
    rw [funext hd]
  · have hd (i : Fin b) : ∃ d : DihedralGroup 5, doublePerm * dihedralPerm d = τ i :=
      (exchanging_iff_dihedral _).mp (hτ i false)
    choose d hd using hd
    refine ⟨⟨true, σ, d⟩, ?_⟩
    change frameEquiv σ Fin.revPerm (fun i => doublePerm * dihedralPerm (d i)) = _
    rw [funext hd]

theorem intoGroup_bijective (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    Function.Bijective (intoGroup p q hpq t) := by
  classical
  refine ⟨?_, ?_⟩
  · intro a c hac
    exact action_injective (le_trans (by decide : 2 ≤ 4) (CodePools.blockCount_ge_four q hq))
      (congrArg Subtype.val hac)
  · intro g
    have hg : (Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
        (Compiled.graph t (CodePools.pool p q hpq) Frame.neutralRecords) g.val :=
      isHom_of_edgeSetAction_eq _ _ g.property.1
    obtain ⟨σ, π, τ, d, hd, hmap, hact, hneutral⟩ := Frame.rigidity p q hpq hq hg
    have hdid : d = id := by
      funext a
      have h := congrFun hmap (.inr (.inr a))
      rw [g.property.2 a] at h
      exact (Sum.inr.inj (Sum.inr.inj h)).symm
    subst d
    obtain ⟨a, ha⟩ := normal_form_represented σ π τ hact
    refine ⟨a, Subtype.ext ?_⟩
    change action a = g.val
    rw [ha]
    apply Equiv.ext
    intro v
    rw [frameEquiv_apply, ← hmap]

/-- The exact root-group order, for the actual seven-pool construction. -/
theorem group_card (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    Fintype.card (group (CodePools.blockCount q) t
      (CodePools.pool p q hpq CodePools.neutralLabel)) =
        2 * 10 ^ CodePools.blockCount q * t.factorial := by
  rw [← Fintype.card_congr (Equiv.ofBijective (intoGroup p q hpq t)
    (intoGroup_bijective p q hpq hq t))]
  exact parameters_card _ _

/-- Reverse the blocks and double their cyclic coordinates, fixing suspension
and data vertices, exactly as in the paper. -/
def iota (b t : ℕ) : Equiv.Perm (Compiled.Vertex b t (Fin 5)) :=
  action (true, 1, fun _ => 1)

theorem dihedralPerm_one : dihedralPerm (1 : DihedralGroup 5) = 1 := dihedralHom.map_one

theorem action_true_factor {b t : ℕ} (σ : Equiv.Perm (Fin t)) (d : Fin b → DihedralGroup 5) :
    action (true, σ, d) = iota b t * action (false, σ, d) := by
  apply Equiv.ext
  intro v
  cases v with
  | inl i => rfl
  | inr v =>
    cases v with
    | inr a => rfl
    | inl v =>
      rcases v with ⟨i, a⟩
      simp [iota, Equiv.Perm.mul_apply, action_block, phasePermutation,
        localPermutation, dihedralPerm_one]

/-- Generators: the actual blockwise dihedral actions with arbitrary
suspension permutations, together with `iota`. -/
def generators (b t : ℕ) : Set (Equiv.Perm (Compiled.Vertex b t (Fin 5))) :=
  Set.range (fun a : Equiv.Perm (Fin t) × (Fin b → DihedralGroup 5) => action (false, a)) ∪
    {iota b t}

def generated (b t : ℕ) : Subgroup (Equiv.Perm (Compiled.Vertex b t (Fin 5))) :=
  Subgroup.closure (generators b t)

theorem action_mem_generated {b t : ℕ} (a : Parameters b t) : action a ∈ generated b t := by
  rcases a with ⟨a, σ, d⟩
  cases a
  · apply Subgroup.subset_closure
    exact Or.inl ⟨(σ, d), rfl⟩
  · rw [action_true_factor]
    apply (generated b t).mul_mem
    · apply Subgroup.subset_closure
      exact Or.inr rfl
    · apply Subgroup.subset_closure
      exact Or.inl ⟨(σ, d), rfl⟩

/-- The generated group in the paper is exactly the actual root subgroup
of neutral-frame automorphisms. -/
theorem generated_eq_group (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    generated (CodePools.blockCount q) t =
      group (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨a, rfl⟩ | hg
    · exact action_mem p q hpq (false, a)
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact action_mem p q hpq (true, 1, fun _ => 1)
  · intro g hg
    obtain ⟨a, ha⟩ := (intoGroup_bijective p q hpq hq t).2 ⟨g, hg⟩
    have heq : action a = g := congrArg Subtype.val ha
    rw [← heq]
    exact action_mem_generated a

end TuranUniversality.Structural.RootActions
