module

public import TuranUniversality.Structural.ReadbackRoles

@[expose] public section

/-! # The bijection underlying the readback coefficient

An ordinary test homomorphism is uniquely specified by an allowed root
permutation, an injective assignment of the five frame data vertices to
neutral vertices, and an arbitrary inner homomorphism in the chosen phase.
-/

namespace TuranUniversality.Structural.Readback

open Cube Support TripleClasses

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable {B : Finset (FiniteGraph 3)}

abbrev NeutralAssignment (O : LegalObject B V) :=
  {d : Fin 5 → V // Function.Injective d ∧ ∀ i, d i ∉ O.active}

abbrev InnerHom (F : RGraph U 3) (O : LegalObject B V) (phase : Bool) :=
  {g : U → V // F.IsHom (O.inner phase) g}

abbrev Parameters (b t : ℕ) (F : RGraph U 3) (O : LegalObject B V) (phase : Bool) :=
  RootActions.Parameters b t × (NeutralAssignment O × InnerHom F O phase)

def renameData {b t : ℕ} (d : Fin 5 → V) : FrameVertex b t → Compiled.Vertex b t V
  | .inl i => .inl i
  | .inr (.inl v) => .inr (.inl v)
  | .inr (.inr i) => dataVertex (d i)

def eraseData {b t : ℕ} : Compiled.Vertex b t V → FrameVertex b t
  | .inl i => .inl i
  | .inr (.inl v) => .inr (.inl v)
  | .inr (.inr _) => .inr (.inr 0)

def parameterMap {b t : ℕ} (a : RootActions.Parameters b t)
    (d : Fin 5 → V) (g : U → V) : Vertex b t U → Compiled.Vertex b t V :=
  Sum.elim (fun v => renameData d (RootActions.action a v)) (fun u => dataVertex (g u))

theorem parameterMap_eq_extend {b t : ℕ} (a : RootActions.Parameters b t)
    (d : Fin 5 → V) (g : U → V) :
    parameterMap a d g = extend a.2.1 (RootActions.phasePermutation b a.1)
      (fun i => RootActions.localPermutation a.1 (a.2.2 i)) d g := by
  funext v
  cases v with
  | inl v =>
    cases v with
    | inl i => rfl
    | inr v => cases v <;> rfl
  | inr u => rfl

theorem parameterMap_of_action_eq {b t : ℕ} (a : RootActions.Parameters b t)
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5))
    (ha : RootActions.action a = RootActions.frameEquiv σ π τ)
    (d : Fin 5 → V) (g : U → V) : parameterMap a d g = extend σ π τ d g := by
  funext v
  cases v with
  | inl v =>
    change renameData d (RootActions.action a v) = Frame.vertexMap σ π τ d v
    rw [ha, RootActions.frameEquiv_apply]
    cases v with
    | inl i => rfl
    | inr v => cases v <;> rfl
  | inr u => rfl

theorem parameterMap_injective {b t : ℕ} (hb : 2 ≤ b)
    (F : RGraph U 3) (O : LegalObject B V) (phase : Bool) :
    Function.Injective (fun p : Parameters b t F O phase =>
      parameterMap p.1 p.2.1.val p.2.2.val) := by
  rintro ⟨a, d, g⟩ ⟨c, e, h⟩ heq
  have ha : a = c := by
    apply RootActions.action_injective hb
    apply Equiv.ext
    intro v
    cases v with
    | inl i =>
      have hv := congrArg (eraseData (V := V)) (congrFun heq (.inl (.inl i)))
      simpa [parameterMap, renameData, eraseData] using hv
    | inr v =>
      cases v with
      | inl v =>
        rcases v with ⟨i, j⟩
        have hv := congrArg (eraseData (V := V)) (congrFun heq (.inl (.inr (.inl ⟨i, j⟩))))
        simpa [parameterMap, renameData, eraseData] using hv
      | inr i => simp
  have hd : d.val = e.val := by
    funext i
    have hv := congrFun heq (.inl (.inr (.inr i)))
    simpa [parameterMap, renameData, dataVertex] using hv
  have hg : g.val = h.val := by
    funext i
    have hv := congrFun heq (.inr i)
    simpa [parameterMap, dataVertex] using hv
  exact Prod.ext ha (Prod.ext (Subtype.ext hd) (Subtype.ext hg))

abbrev TestHom [Fintype V] (p q : ℕ) (hpq : p ≤ q) (t : ℕ)
    (F : RGraph U 3) (O : LegalObject B V) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges) :=
  {f : Vertex (CodePools.blockCount q) t U → Compiled.Vertex (CodePools.blockCount q) t V //
    (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) O.records) f}

def intoHoms [Fintype V] (p q : ℕ) (hpq : p ≤ q) (t : ℕ)
    (F : RGraph U 3) (O : LegalObject B V) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (a : Parameters (CodePools.blockCount q) t F O phase) : TestHom p q hpq t F O phase Z hZ :=
  ⟨parameterMap a.1 a.2.1.val a.2.2.val, by
    rw [parameterMap_eq_extend]
    exact extend_isHom p q hpq O F phase Z hZ a.1.2.1
      (RootActions.phasePermutation _ a.1.1)
      (fun i => RootActions.localPermutation a.1.1 (a.1.2.2 i))
      (RootActions.allowed _ _ a.1) a.2.1.val a.2.1.property.1 a.2.1.property.2
      a.2.2.val a.2.2.property⟩

theorem intoHoms_bijective [Fintype V] (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (F : RGraph U 3) (hno : Uniformity.NoIsolates F) (O : LegalObject B V) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges) :
    Function.Bijective (intoHoms p q hpq t F O phase Z hZ) := by
  constructor
  · intro a c hac
    exact parameterMap_injective
      (le_trans (by decide : 2 ≤ 4) (CodePools.blockCount_ge_four q hq)) F O phase
      (congrArg Subtype.val hac)
  · rintro ⟨f, hf⟩
    obtain ⟨σ, π, τ, d, g, hd, hdn, hact, hg, hfeq⟩ :=
      hom_normal_form p q hpq hq O F hno phase Z hZ f hf
    obtain ⟨a, ha⟩ := RootActions.normal_form_represented σ π τ hact
    refine ⟨⟨a, ⟨d, hd, hdn⟩, ⟨g, hg⟩⟩, Subtype.ext ?_⟩
    exact (parameterMap_of_action_eq a σ π τ ha d g).trans hfeq.symm

end TuranUniversality.Structural.Readback
