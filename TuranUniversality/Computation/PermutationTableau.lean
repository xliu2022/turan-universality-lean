module

public import TuranUniversality.Computation.LocalSystem
public import TuranUniversality.Computation.ClosedComponents
public import TuranUniversality.Computation.GrammarChecks
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Extracting finite wall segments from commuting local permutations

The row width and temporal period are obtained from actual finite permutation
orbits.  The proof does not postulate a rectangular component or disjoint path
witnesses.  Only a finite wall segment and its temporal translates are needed.
-/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem

open Turing Cellular ResetProtocol

variable {Γ Λ X : Type*} [Inhabited Γ] [Inhabited Λ]

/-- The total local data supplied by a closed partial-matching component. -/
structure PermutationModel (M : TM0.Machine Γ Λ) (input : List Γ) (X : Type*) where
  H : Equiv.Perm X
  V : Equiv.Perm X
  label : X → Label Γ Λ
  commute : Function.Commute H V
  horizontal : ∀ x, Horizontal M (label x) (label (H x))
  evolution : ∀ x, Evolution M (label (H.symm x)) (label x) (label (H x)) (label (V x))
  input_rule : ∀ x, IsStart (label x) →
    ∀ j, j < (StaticInput.inputWord input ++ [StaticInput.Symbol.finish]).length →
      staticPart (label ((H : X → X)^[j] x)) =
        (StaticInput.inputWord input ++ [StaticInput.Symbol.finish])[j]?

namespace PermutationModel

variable {M : TM0.Machine Γ Λ} {input : List Γ} (P : PermutationModel M input X)

def MarkedAt (x : X) : Prop := P.label (P.H.symm x) = .leftWall ∧ IsInitial (P.label x)

theorem initial_successor {a b : Label Γ Λ} (h : Horizontal M a b) (hi : IsInitial a) :
    IsInitial b ∨ b = .rightWall := by
  cases a with
  | leftWall => exact hi.elim
  | rightWall => exact hi.elim
  | cell s d =>
    change d = initialSymbol at hi
    subst d
    cases b with
    | leftWall => exact h.2.2.elim
    | rightWall => exact Or.inr rfl
    | cell s' d' =>
      left
      have htag : d'.1 = .initial := by
        have hh := h.2.2.2
        cases ht : d'.1 <;> simp [initialSymbol, ResetGrammar.Adjacent, ht] at hh ⊢
      have hd : d'.2 = blankCell := by
        have hu := h.2.1
        simpa only [Unary, ValidSymbol, htag] using hu
      exact Prod.ext htag hd

theorem exists_positive_period [Fintype X] (f : Equiv.Perm X) :
    ∃ p : ℕ, 0 < p ∧ (f : X → X)^[p] = id :=
  ⟨(Fintype.card X).factorial, Nat.factorial_pos _,
    Function.injective_iff_iterate_factorial_card_eq_id.mp f.injective⟩

/-- Starting after a left wall in initial phase, a right wall must occur
before the finite horizontal orbit can return to that left predecessor. -/
theorem first_right_wall [Fintype X] (x : X) (hx : P.MarkedAt x) :
    ∃ W : ℕ, 0 < W ∧ P.label ((P.H : X → X)^[W] x) = .rightWall ∧
      ∀ i : ℕ, i < W → IsInitial (P.label ((P.H : X → X)^[i] x)) := by
  classical
  have hex : ∃ i : ℕ, P.label ((P.H : X → X)^[i] x) = .rightWall := by
    by_contra hnot
    have hall : ∀ i : ℕ, IsInitial (P.label ((P.H : X → X)^[i] x)) := by
      intro i
      induction i with
      | zero => exact hx.2
      | succ i ih =>
        rw [Function.iterate_succ_apply']
        rcases initial_successor (P.horizontal ((P.H : X → X)^[i] x)) ih with hi | hr
        · exact hi
        · exact (hnot ⟨i + 1, by simpa only [Function.iterate_succ_apply'] using hr⟩).elim
    obtain ⟨p, hp, hperiod⟩ := exists_positive_period P.H
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    have hpred : (P.H : X → X)^[k] x = P.H.symm x := by
      have hh := congrFun hperiod (P.H.symm x)
      simpa only [Function.iterate_succ_apply, Equiv.apply_symm_apply, id_eq] using hh
    have hh := hall k
    rw [hpred, hx.1] at hh
    exact hh
  let W := Nat.find hex
  have hW : P.label ((P.H : X → X)^[W] x) = .rightWall := Nat.find_spec hex
  have hmin : ∀ i : ℕ, i < W → P.label ((P.H : X → X)^[i] x) ≠ .rightWall :=
    fun i hi => Nat.find_min hex hi
  have hpos : 0 < W := by
    by_contra hn
    have hz : W = 0 := by omega
    rw [hz] at hW
    have hi := hx.2
    rw [show P.label x = .rightWall from hW] at hi
    exact hi
  refine ⟨W, hpos, hW, ?_⟩
  intro i
  induction i with
  | zero => intro _; exact hx.2
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    rw [Function.iterate_succ_apply']
    rcases initial_successor (P.horizontal ((P.H : X → X)^[i] x)) hprev with hh | hr
    · exact hh
    · exact (hmin (i + 1) hi (by simpa only [Function.iterate_succ_apply'] using hr)).elim

/-- Walls stay fixed along the entire temporal orbit. -/
theorem left_wall_time (x : X) (hx : P.label x = .leftWall) (t : ℕ) :
    P.label ((P.V : X → X)^[t] x) = .leftWall := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have h := P.evolution ((P.V : X → X)^[t] x)
    simpa only [ih, Evolution] using h

theorem right_wall_time (x : X) (hx : P.label x = .rightWall) (t : ℕ) :
    P.label ((P.V : X → X)^[t] x) = .rightWall := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have h := P.evolution ((P.V : X → X)^[t] x)
    simpa only [ih, Evolution] using h

/-- Interior cells preserve their exact static input symbol for every time. -/
theorem cell_time (x : X) (s : StaticInput.Symbol Γ) (d : ResetProtocol.Symbol Γ Λ)
    (hx : P.label x = .cell s d) (t : ℕ) :
    ∃ d', P.label ((P.V : X → X)^[t] x) = .cell s d' := by
  induction t with
  | zero => exact ⟨d, hx⟩
  | succ t ih =>
    obtain ⟨d', hd⟩ := ih
    have h := P.evolution ((P.V : X → X)^[t] x)
    rw [hd] at h
    obtain ⟨d'', hh, _⟩ := h
    exact ⟨d'', by simpa only [Function.iterate_succ_apply'] using hh⟩

end PermutationModel

end TuranUniversality.Computation.LocalSystem
