module

public import TuranUniversality.Hypergraph.Rooting

@[expose] public section

/-! # Inverting a finite partial root assignment -/

namespace TuranUniversality.Rooting

universe u v w
variable {M : Type u} {V : Type v} {W : Type w}

noncomputable def inverseFunction (mu : Rooting M V) (v : V) : Option M := by
  classical
  exact if h : ∃ a, mu.val a = some v then some h.choose else none

theorem inverseFunction_some_iff (mu : Rooting M V) (v : V) (a : M) :
    inverseFunction mu v = some a ↔ mu.val a = some v := by
  classical
  unfold inverseFunction
  split
  next h =>
    constructor
    · intro ha
      have heq := Option.some.inj ha
      simpa only [heq] using h.choose_spec
    · intro ha
      exact congrArg some (mu.property h.choose a v h.choose_spec ha)
  next h =>
    constructor
    · intro h'; cases h'
    · intro ha; exact False.elim (h ⟨a, ha⟩)

noncomputable def inverse (mu : Rooting M V) : Rooting V M :=
  ⟨inverseFunction mu, by
    intro v w a hv hw
    have h1 := (inverseFunction_some_iff mu v a).mp hv
    have h2 := (inverseFunction_some_iff mu w a).mp hw
    exact Option.some.inj (h1.symm.trans h2)⟩

@[simp] theorem inverse_some_iff (mu : Rooting M V) (v : V) (a : M) :
    mu.inverse.val v = some a ↔ mu.val a = some v := inverseFunction_some_iff mu v a

@[simp] theorem inverse_inverse (mu : Rooting M V) : mu.inverse.inverse = mu := by
  apply Subtype.ext
  funext a
  cases ha : mu.val a with
  | some v =>
    exact (inverse_some_iff mu.inverse a v).mpr ((inverse_some_iff mu v a).mpr ha)
  | none =>
    cases h : mu.inverse.inverse.val a with
    | none => rfl
    | some v =>
      have hv := (inverse_some_iff mu v a).mp ((inverse_some_iff mu.inverse a v).mp h)
      rw [ha] at hv
      cases hv

noncomputable def inverseEquiv : Rooting M V ≃ Rooting V M where
  toFun := inverse
  invFun := inverse
  left_inv := inverse_inverse
  right_inv := inverse_inverse

theorem inverse_extends {mu nu : Rooting M V} (h : Extends mu nu) :
    Extends mu.inverse nu.inverse := by
  intro v a ha
  exact (inverse_some_iff nu v a).mpr (h a v ((inverse_some_iff mu v a).mp ha))

/-- Restrict the domain of a partial assignment along an injection. -/
def precompose (mu : Rooting M V) (i : W ↪ M) : Rooting W V :=
  ⟨mu.val ∘ i, fun a b v ha hb => i.injective (mu.property _ _ v ha hb)⟩

/-- Transport assigned vertices along an injection. -/
def map (mu : Rooting M V) (i : V ↪ W) : Rooting M W :=
  ⟨fun a => (mu.val a).map i, by
    intro a b w ha hb
    cases hma : mu.val a with
    | none => simp [hma] at ha
    | some v =>
      cases hmb : mu.val b with
      | none => simp [hmb] at hb
      | some z =>
        have hv : i v = w := by simpa [hma] using ha
        have hz : i z = w := by simpa [hmb] using hb
        have hvz := i.injective (hv.trans hz.symm)
        subst z
        exact mu.property a b v hma hmb⟩

@[simp] theorem map_some_iff (mu : Rooting M V) (i : V ↪ W) (a : M) (v : V) :
    (mu.map i).val a = some (i v) ↔ mu.val a = some v := by
  cases h : mu.val a <;> simp [map, h, i.injective.eq_iff]

end TuranUniversality.Rooting
