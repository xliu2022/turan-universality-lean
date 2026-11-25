module

public import TuranUniversality.Computation.PermutationTableau
public import TuranUniversality.Computation.RowFrame
public import TuranUniversality.Computation.RowInput

/-! # The actual temporal wall frames inside a finite permutation realization -/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem.PermutationModel

open Turing Cellular ResetProtocol

variable {Γ Λ X : Type*} [Inhabited Γ] [Inhabited Λ]
  {M : TM0.Machine Γ Λ} {input : List Γ} (P : PermutationModel M input X)

/-- Coordinates begin at the left-wall predecessor of the marked cell. -/
def baseSite (x : X) (i : ℕ) : X := (P.H : X → X)^[i] (P.H.symm x)

@[simp] theorem baseSite_succ (x : X) (i : ℕ) :
    P.baseSite x (i + 1) = (P.H : X → X)^[i] x := by
  simp [baseSite, Function.iterate_succ_apply]

def site (x : X) (t i : ℕ) : X := (P.V : X → X)^[t] (P.baseSite x i)

theorem site_horizontal (x : X) (t i : ℕ) :
    P.H (P.site x t i) = P.site x t (i + 1) := by
  rw [site, site, (P.commute.iterate_right t) (P.baseSite x i)]
  simp only [baseSite, Function.iterate_succ_apply']

theorem site_predecessor (x : X) (t i : ℕ) :
    P.H.symm (P.site x t (i + 1)) = P.site x t i := by
  rw [← P.site_horizontal x t i, Equiv.symm_apply_apply]

theorem site_vertical (x : X) (t i : ℕ) :
    P.V (P.site x t i) = P.site x (t + 1) i := by
  simp only [site, Function.iterate_succ_apply']

variable (x : X) (W : ℕ) (hx : P.MarkedAt x)
  (hW : P.label ((P.H : X → X)^[W] x) = .rightWall)
  (hini : ∀ i : ℕ, i < W → IsInitial (P.label ((P.H : X → X)^[i] x)))

/-- The finite row at time `t` is extracted from actual component vertices. -/
def wallFrame (t : ℕ) : Frame M W where
  label := fun i => P.label (P.site x t i.val)
  left_wall := by
    simpa [site, baseSite] using P.left_wall_time (P.H.symm x) hx.1 t
  right_wall := by
    simpa [site] using P.right_wall_time ((P.H : X → X)^[W] x) hW t
  interior := by
    intro i
    have hi := hini i.val i.isLt
    cases hl : P.label ((P.H : X → X)^[i.val] x) with
    | leftWall => simp [hl, IsInitial] at hi
    | rightWall => simp [hl, IsInitial] at hi
    | cell s d =>
      obtain ⟨d', hd⟩ := P.cell_time ((P.H : X → X)^[i.val] x) s d hl t
      exact ⟨s, d', by simpa [centerIndex, site] using hd⟩
  horizontal := by
    intro i
    have h := P.horizontal (P.site x t i.val)
    simpa only [Fin.val_castSucc, Fin.val_succ, P.site_horizontal] using h

theorem wallFrame_evolution (t : ℕ) (i : Fin W) :
    Evolution M ((P.wallFrame x W hx hW hini t).label (leftIndex i))
      ((P.wallFrame x W hx hW hini t).label (centerIndex i))
      ((P.wallFrame x W hx hW hini t).label (rightIndex i))
      ((P.wallFrame x W hx hW hini (t + 1)).label (centerIndex i)) := by
  have h := P.evolution (P.site x t (i.val + 1))
  simpa only [wallFrame, leftIndex, centerIndex, rightIndex,
    P.site_predecessor, P.site_horizontal, P.site_vertical, Nat.add_assoc] using h

theorem wallFrame_static_time (t : ℕ) :
    (P.wallFrame x W hx hW hini t).static = (P.wallFrame x W hx hW hini 0).static := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact ((P.wallFrame x W hx hW hini t).static_eq_of_evolution _
      (P.wallFrame_evolution x W hx hW hini t)).trans ih

theorem wallFrame_step (t : ℕ) :
    Step M (fun i => StaticInput.frozen ((P.wallFrame x W hx hW hini 0).static i))
      (P.wallFrame x W hx hW hini t).dynamic (P.wallFrame x W hx hW hini (t + 1)).dynamic := by
  have h := (P.wallFrame x W hx hW hini t).step _ (P.wallFrame_evolution x W hx hW hini t)
  rw [P.wallFrame_static_time x W hx hW hini t] at h
  exact h

theorem wallFrame_initial : (P.wallFrame x W hx hW hini 0).dynamic = initialRow W := by
  funext i
  have h := hini i.val i.isLt
  cases hl : P.label ((P.H : X → X)^[i.val] x) with
  | leftWall => simp [hl, IsInitial] at h
  | rightWall => simp [hl, IsInitial] at h
  | cell s d =>
    have hd : d = initialSymbol := by simpa only [hl, IsInitial] using h
    simpa [Frame.dynamic, wallFrame, centerIndex, site, hl, dynamicPart, initialRow] using hd

theorem wallFrame_period (p : ℕ) (hp : (P.V : X → X)^[p] = id) :
    (P.wallFrame x W hx hW hini p).dynamic = (P.wallFrame x W hx hW hini 0).dynamic := by
  funext i
  simp only [Frame.dynamic, wallFrame, site, hp, id_eq, Function.iterate_zero_apply]

/-- A positive temporal permutation period gives a genuine local reset return. -/
theorem wallFrame_returns [Fintype X] :
    Returns M (fun i => StaticInput.frozen ((P.wallFrame x W hx hW hini 0).static i)) := by
  obtain ⟨p, hp, hperiod⟩ := exists_positive_period P.V
  have hpath : ∀ k : ℕ, 0 < k →
      Relation.TransGen
        (Step M (fun i => StaticInput.frozen ((P.wallFrame x W hx hW hini 0).static i)))
        (P.wallFrame x W hx hW hini 0).dynamic (P.wallFrame x W hx hW hini k).dynamic := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro _
      cases k with
      | zero => exact .single (P.wallFrame_step x W hx hW hini 0)
      | succ k => exact (ih (by omega)).tail (P.wallFrame_step x W hx hW hini (k + 1))
  have h := hpath p hp
  rw [P.wallFrame_period x W hx hW hini p hperiod,
    P.wallFrame_initial x W hx hW hini] at h
  exact h

/-- The Start-triggered positive path constraints force the exact input
inside the extracted initial wall segment.  Crossing the right wall during
the prescribed prefix would contradict its required interior label. -/
theorem wallFrame_input_valid :
    StaticInput.Valid input (List.ofFn (P.wallFrame x W hx hW hini 0).static) := by
  let F := P.wallFrame x W hx hW hini 0
  refine ⟨F.static_accepted, ?_⟩
  have hcell : ∀ i : Fin W, P.label ((P.H : X → X)^[i.val] x) =
      .cell (F.static i) (F.dynamic i) := by
    intro i
    have h := F.cell_at i
    have hs : F.label (centerIndex i) = P.label ((P.H : X → X)^[i.val] x) := by
      simp [F, wallFrame, centerIndex, site]
    rw [hs] at h
    exact h
  apply (StaticInput.prefixCheck_positions input _).mpr
  intro i a hstart
  have hi : i < W := by
    by_contra hnot
    have hnone : (List.ofFn F.static)[i]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hnot)
    rw [hnone] at hstart
    cases hstart
  have hsi : F.static ⟨i, hi⟩ = .start a := by
    have hli : i < (List.ofFn F.static).length := by simpa using hi
    rw [List.getElem?_eq_getElem hli] at hstart
    simpa only [List.getElem_ofFn, Option.some.injEq] using hstart
  have htrigger : IsStart (P.label ((P.H : X → X)^[i] x)) := by
    rw [hcell ⟨i, hi⟩, hsi]
    trivial
  let word := StaticInput.inputWord input ++ [StaticInput.Symbol.finish]
  have hpf : ∀ j : ℕ, j < word.length →
      staticPart (P.label ((P.H : X → X)^[i + j] x)) = word[j]? := by
    intro j hj
    have h := P.input_rule ((P.H : X → X)^[i] x) htrigger j hj
    simpa only [← Function.iterate_add_apply, Nat.add_comm] using h
  have hfit : i + word.length ≤ W := by
    by_contra hnot
    have hj : W - i < word.length := by omega
    have hh := hpf (W - i) hj
    have hij : i + (W - i) = W := by omega
    rw [hij, hW] at hh
    simp only [staticPart, List.getElem?_eq_getElem hj] at hh
    cases hh
  apply List.prefix_iff_getElem?.mpr
  intro j hj
  have hj' : j < word.length := hj
  have hij : i + j < W := by omega
  have hh := hpf j hj'
  rw [hcell ⟨i + j, hij⟩] at hh
  simp only [staticPart, List.getElem?_eq_getElem hj', Option.some.injEq] at hh
  rw [List.getElem?_drop]
  have hli : i + j < (List.ofFn F.static).length := by simpa using hij
  rw [List.getElem?_eq_getElem hli]
  simpa only [List.getElem_ofFn] using congrArg some hh

omit x W hx hW hini in
/-- A finite commuting local realization with a marked initial cell forces
the actual ordinary tape-machine input to halt. -/
theorem halts_of_marked [Fintype X] (x : X) (hx : P.MarkedAt x) :
    (TM0.eval M input).Dom := by
  obtain ⟨W, _, hW, hini⟩ := P.first_right_wall x hx
  exact StaticInput.finite_valid_return_halts M input
    (P.wallFrame x W hx hW hini 0).static
    (P.wallFrame_input_valid x W hx hW hini)
    (P.wallFrame_returns x W hx hW hini)

end TuranUniversality.Computation.LocalSystem.PermutationModel
