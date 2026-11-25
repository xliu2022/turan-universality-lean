module

public import TuranUniversality.Computation.FiniteWindow

/-!
# A synchronous radius-one simulation of an ordinary tape machine

A cell records a tape letter and an optional head state.  The rule reads only
the left, middle, and right old cells.  On the encoded rows, exactly one head
is present.  Its write, left-move, and right-move instructions are simulated
in one simultaneous update.  No locality of a global single-head predicate
is asserted here; that is a separate requirement for a finite tableau grammar.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Turing

namespace Cellular

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- One cell of the simulation alphabet.  It is finite when both machine
alphabets are finite. -/
abbrev Cell (Γ Λ : Type*) := Γ × Option Λ

/-- A full, absolute-coordinate row. -/
abbrev Row (Γ Λ : Type*) := ℤ → Cell Γ Λ

/-- The state sent by a neighboring head moving in the specified direction. -/
def incoming (M : TM0.Machine Γ Λ) (d : Dir) (a : Cell Γ Λ) : Option Λ :=
  a.2.bind fun q =>
    (M q a.1).bind fun (q', s) =>
      match s, d with
      | .move .left, .left => some q'
      | .move .right, .right => some q'
      | _, _ => none

/-- The local synchronous rule.  A genuinely halting head stays in place.
The arbitrary left priority on an invalid two-head neighborhood is never used
in the simulation theorem, which proves preservation of a unique head. -/
def localRule (M : TM0.Machine Γ Λ) (l a r : Cell Γ Λ) : Cell Γ Λ :=
  match a.2 with
  | some q =>
    match M q a.1 with
    | none => a
    | some (q', .write b) => (b, some q')
    | some (_, .move _) => (a.1, none)
  | none => (a.1, (incoming M .right l).or (incoming M .left r))

/-- All cells update at once from radius-one old neighborhoods. -/
def update (M : TM0.Machine Γ Λ) (r : Row Γ Λ) : Row Γ Λ :=
  fun i => localRule M (r (i - 1)) (r i) (r (i + 1))

/-- Encode a machine configuration with its head at absolute position `p`.
The tape representation itself is relative to the head. -/
def row (p : ℤ) (c : TM0.Cfg Γ Λ) : Row Γ Λ :=
  fun i => (c.Tape.nth (i - p), if i = p then some c.q else none)

/-- A legitimate row is an ordinary tape configuration with one head. -/
def Legitimate (r : Row Γ Λ) : Prop := ∃ p c, r = row p c

omit [Inhabited Λ] in
@[simp] theorem row_head (p : ℤ) (c : TM0.Cfg Γ Λ) :
    (row p c p).2 = some c.q := by simp [row]

omit [Inhabited Λ] in
theorem row_head_iff (p i : ℤ) (c : TM0.Cfg Γ Λ) :
    (row p c i).2 ≠ none ↔ i = p := by simp [row]

omit [Inhabited Λ] in
theorem row_legitimate (p : ℤ) (c : TM0.Cfg Γ Λ) :
    Legitimate (row p c) := ⟨p, c, rfl⟩

theorem update_write (M : TM0.Machine Γ Λ) (p : ℤ) (c : TM0.Cfg Γ Λ)
    {q : Λ} {b : Γ} (hm : M c.q c.Tape.head = some (q, .write b)) :
    update M (row p c) = row p ⟨q, c.Tape.write b⟩ := by
  funext i
  by_cases hi : i = p
  · subst i
    simp [update, row, localRule, hm, Tape.write]
  · by_cases hl : i - 1 = p <;> by_cases hr : i + 1 = p <;>
      simp [update, row, localRule, incoming, hm, hi, hl, hr,
        Tape.write_nth, sub_ne_zero.mpr hi]

theorem update_move_left (M : TM0.Machine Γ Λ) (p : ℤ) (c : TM0.Cfg Γ Λ)
    {q : Λ} (hm : M c.q c.Tape.head = some (q, .move .left)) :
    update M (row p c) = row (p - 1) ⟨q, c.Tape.move .left⟩ := by
  funext i
  have hs : i - (p - 1) - 1 = i - p := by omega
  by_cases hi : i = p
  · subst i
    have hp : p ≠ p - 1 := by omega
    simp [update, row, localRule, hm, Tape.move_left_nth, hp]
  · by_cases hl : i - 1 = p <;> by_cases hr : i + 1 = p
    all_goals
      have ht : (i = p - 1) ↔ i + 1 = p := by omega
      simp [update, row, localRule, incoming, hm, hi, hl, hr,
        Tape.move_left_nth, hs, ht]

theorem update_move_right (M : TM0.Machine Γ Λ) (p : ℤ) (c : TM0.Cfg Γ Λ)
    {q : Λ} (hm : M c.q c.Tape.head = some (q, .move .right)) :
    update M (row p c) = row (p + 1) ⟨q, c.Tape.move .right⟩ := by
  funext i
  have hs : i - (p + 1) + 1 = i - p := by omega
  by_cases hi : i = p
  · subst i
    simp [update, row, localRule, hm, Tape.move_right_nth]
  · by_cases hl : i - 1 = p <;> by_cases hr : i + 1 = p
    all_goals
      have ht : (i = p + 1) ↔ i - 1 = p := by omega
      simp [update, row, localRule, incoming, hm, hi, hl, hr,
        Tape.move_right_nth, hs, ht]

/-- Halting configurations are fixed by the raw running rule.  A reset phase
must separately require this actual undefined machine instruction. -/
theorem update_halt (M : TM0.Machine Γ Λ) (p : ℤ) (c : TM0.Cfg Γ Λ)
    (hm : M c.q c.Tape.head = none) : update M (row p c) = row p c := by
  funext i
  by_cases hi : i = p
  · subst i
    simp [update, row, localRule, hm]
  · by_cases hl : i - 1 = p <;> by_cases hr : i + 1 = p <;>
      simp [update, row, localRule, incoming, hm, hi, hl, hr]

/-- A genuine machine step is one synchronous cellular step at the appropriate
new absolute head position. -/
theorem update_of_machine_step (M : TM0.Machine Γ Λ) (p : ℤ)
    {c c' : TM0.Cfg Γ Λ} (h : TM0.step M c = some c') :
    ∃ p', update M (row p c) = row p' c' := by
  cases hm : M c.q c.Tape.head with
  | none => simp [TM0.step, hm] at h
  | some a =>
    rcases a with ⟨q, s⟩
    cases s with
    | write b =>
      simp [TM0.step, hm] at h
      subst c'
      exact ⟨p, update_write M p c hm⟩
    | move d =>
      cases d with
      | left =>
        simp [TM0.step, hm] at h
        subst c'
        exact ⟨p - 1, update_move_left M p c hm⟩
      | right =>
        simp [TM0.step, hm] at h
        subst c'
        exact ⟨p + 1, update_move_right M p c hm⟩

/-- The running rule cannot create a second head or lose the unique head of a
legitimate row.  This also covers genuine halting rows. -/
theorem update_legitimate (M : TM0.Machine Γ Λ) {r : Row Γ Λ}
    (h : Legitimate r) : Legitimate (update M r) := by
  obtain ⟨p, c, rfl⟩ := h
  cases hs : TM0.step M c with
  | none =>
    have hm : M c.q c.Tape.head = none := by
      simpa [TM0.step] using hs
    rw [update_halt M p c hm]
    exact row_legitimate p c
  | some c' =>
    obtain ⟨p', heq⟩ := update_of_machine_step M p hs
    exact ⟨p', c', heq⟩

/-- The absolute coordinates of a finite window start at its left boundary. -/
def windowRow (w : WindowConfig Γ Λ) : Row Γ Λ := row w.left.length w.toCfg

/-- The finite-window transition is exactly the synchronous local transition,
with the same absolute left boundary throughout the run. -/
theorem update_window_step (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : WindowConfig.step M w = some w') :
    update M (windowRow w) = windowRow w' := by
  rcases w with ⟨q, l, a, r⟩
  cases hm : M q a with
  | none => simp [WindowConfig.step, hm] at h
  | some p =>
    rcases p with ⟨q', s⟩
    cases s with
    | write b =>
      simp [WindowConfig.step, hm] at h
      subst w'
      simpa [windowRow, WindowConfig.toCfg, Tape.write] using
        update_write M (l.length : ℤ) (WindowConfig.toCfg ⟨q, l, a, r⟩) hm
    | move d =>
      cases d with
      | left =>
        cases l with
        | nil => simp [WindowConfig.step, hm] at h
        | cons b l =>
          simp [WindowConfig.step, hm] at h
          subst w'
          simpa [windowRow, WindowConfig.toCfg, Tape.move, ListBlank.cons_mk] using
            update_move_left M ((b :: l).length : ℤ)
              (WindowConfig.toCfg ⟨q, b :: l, a, r⟩) hm
      | right =>
        cases r with
        | nil => simp [WindowConfig.step, hm] at h
        | cons b r =>
          simp [WindowConfig.step, hm] at h
          subst w'
          simpa [windowRow, WindowConfig.toCfg, Tape.move, ListBlank.cons_mk] using
            update_move_right M (l.length : ℤ)
              (WindowConfig.toCfg ⟨q, l, a, b :: r⟩) hm

/-- Every finite-window run is an actual finite sequence of simultaneous
radius-one updates. -/
theorem iterate_of_window_reaches (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : StateTransition.Reaches (WindowConfig.step M) w w') :
    ∃ n : ℕ, (update M)^[n] (windowRow w) = windowRow w' := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ h ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', hn]
    exact update_window_step M h

end Cellular

end TuranUniversality.Computation
