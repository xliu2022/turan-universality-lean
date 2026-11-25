module

public import TuranUniversality.Weighted.PermutationBuilder

/-! # Three disjoint copies provide the three distinct marked endpoints -/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem.PermutationModel

open Turing

variable {Γ Λ X : Type*} [Inhabited Γ] [Inhabited Λ]
  {M : TM0.Machine Γ Λ} {input : List Γ}

def threePerm (f : Equiv.Perm X) : Equiv.Perm (Fin 3 × X) :=
  Equiv.prodCongr (Equiv.refl (Fin 3)) f

@[simp] theorem threePerm_apply (f : Equiv.Perm X) (x : Fin 3 × X) :
    threePerm f x = (x.1, f x.2) := rfl

@[simp] theorem threePerm_symm_apply (f : Equiv.Perm X) (x : Fin 3 × X) :
    (threePerm f).symm x = (x.1, f.symm x.2) := rfl

theorem threePerm_iterate_snd (f : Equiv.Perm X) (n : ℕ) (x : Fin 3 × X) :
    ((threePerm f : (Fin 3 × X) → (Fin 3 × X))^[n] x).2 = (f : X → X)^[n] x.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', threePerm_apply, ih]

def threeCopies (P : PermutationModel M input X) : PermutationModel M input (Fin 3 × X) where
  H := threePerm P.H
  V := threePerm P.V
  label x := P.label x.2
  commute := by
    intro x
    exact Prod.ext rfl (P.commute x.2)
  horizontal := fun x => P.horizontal x.2
  evolution := fun x => P.evolution x.2
  input_rule := by
    intro x hx j hj
    change staticPart (P.label (((threePerm P.H : (Fin 3 × X) → (Fin 3 × X))^[j] x).2)) = _
    rw [threePerm_iterate_snd]
    exact P.input_rule x.2 hx j hj

theorem threeCopies_marked (P : PermutationModel M input X) (x : X) (hx : P.MarkedAt x) (i : Fin 3) :
    P.threeCopies.MarkedAt (i, x) := hx

end TuranUniversality.Computation.LocalSystem.PermutationModel

namespace TuranUniversality.Weighted

variable {Kinds Index : Type*} [DecidableEq Kinds] [DecidableEq Index]

def tripleMarker (cell : Kinds) (a : Index) : Finset (Kinds × (Fin 3 × Index)) :=
  {(cell, (0, a)), (cell, (1, a)), (cell, (2, a))}

@[simp] theorem tripleMarker_card (cell : Kinds) (a : Index) : (tripleMarker cell a).card = 3 := by
  simp [tripleMarker]

theorem tripleMarker_first (cell : Kinds) (a : Index) (d : Kinds × (Fin 3 × Index))
    (hd : d ∈ tripleMarker cell a) : d.1 = cell := by
  simp only [tripleMarker, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl <;> rfl

theorem tripleMarker_index (cell : Kinds) (a : Index) (d : Kinds × (Fin 3 × Index))
    (hd : d ∈ tripleMarker cell a) : d.2.2 = a := by
  simp only [tripleMarker, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl <;> rfl

end TuranUniversality.Weighted
