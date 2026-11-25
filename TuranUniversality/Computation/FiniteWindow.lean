module

public import TuranUniversality.Computation.FiniteMachine

/-!
# Exact finite-window witnesses for ordinary machine halting

The lists in a window are actual finite buffers; reaching an empty boundary is
not counted as halting.  A terminal window is required to have an actual
undefined machine instruction.  A finite halting computation can always be
given enough blank padding on each side to avoid its window boundary.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Turing

/-- A finite tape window, with the left buffer listed nearest-cell first. -/
structure WindowConfig (Γ Λ : Type*) where
  state : Λ
  left : List Γ
  head : Γ
  right : List Γ

namespace WindowConfig

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Forget the finite boundary by continuing both buffers with blanks. -/
def toCfg (w : WindowConfig Γ Λ) : TM0.Cfg Γ Λ :=
  ⟨w.state, ⟨w.head, ListBlank.mk w.left, ListBlank.mk w.right⟩⟩

/-- At least `k` cells remain in each direction. -/
def Buffered (k : ℕ) (w : WindowConfig Γ Λ) : Prop :=
  k ≤ w.left.length ∧ k ≤ w.right.length

/-- The bounded transition refuses a move beyond the available finite window.
An undefined result can mean overflow; `Terminal` separately tests true halting. -/
def step (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ) : Option (WindowConfig Γ Λ) := do
  let (q, s) ← M w.state w.head
  match s with
  | .write a => pure {w with state := q, head := a}
  | .move .left =>
    match w.left with
    | [] => none
    | a :: l => pure ⟨q, l, a, w.head :: w.right⟩
  | .move .right =>
    match w.right with
    | [] => none
    | a :: r => pure ⟨q, w.head :: w.left, a, r⟩

/-- Genuine halting, rather than exhaustion of the finite window. -/
def Terminal (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ) : Prop :=
  M w.state w.head = none

theorem terminal_iff_step_none (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ) :
    Terminal M w ↔ TM0.step M w.toCfg = none := by
  simp [Terminal, TM0.step, toCfg]

set_option backward.isDefEq.respectTransparency false in
/-- Every actual bounded transition is an actual ordinary-machine transition. -/
theorem step_sound (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : step M w = some w') : TM0.step M w.toCfg = some w'.toCfg := by
  rcases w with ⟨q, l, a, r⟩
  cases hm : M q a with
  | none => simp [step, hm] at h
  | some p =>
    rcases p with ⟨q', s⟩
    cases s with
    | write b =>
      simp [step, hm] at h
      subst w'
      simp [TM0.step, toCfg, hm, Tape.write]
    | move d =>
      cases d with
      | left =>
        cases l with
        | nil => simp [step, hm] at h
        | cons b l =>
          simp [step, hm] at h
          subst w'
          simp [TM0.step, toCfg, hm, Tape.move, ListBlank.cons_mk]
      | right =>
        cases r with
        | nil => simp [step, hm] at h
        | cons b r =>
          simp [step, hm] at h
          subst w'
          simp [TM0.step, toCfg, hm, Tape.move, ListBlank.cons_mk]

set_option backward.isDefEq.respectTransparency false in
/-- With a spare cell on both sides, the bounded and ordinary updates agree. -/
theorem step_commutes (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ)
    (h : Buffered 1 w) : (step M w).map toCfg = TM0.step M w.toCfg := by
  rcases w with ⟨q, l, a, r⟩
  cases l with
  | nil => simp [Buffered] at h
  | cons b l =>
    cases r with
    | nil => simp [Buffered] at h
    | cons c r =>
      cases hm : M q a with
      | none => simp [step, TM0.step, toCfg, hm]
      | some p =>
        rcases p with ⟨q', s⟩
        cases s with
        | write d => simp [step, TM0.step, toCfg, hm, Tape.write]
        | move d =>
          cases d <;> simp [step, TM0.step, toCfg, hm, Tape.move, ListBlank.cons_mk]

omit [Inhabited Γ] in
/-- One step consumes at most one cell of either buffer. -/
theorem buffered_step (M : TM0.Machine Γ Λ) {k : ℕ} {w w' : WindowConfig Γ Λ}
    (hb : Buffered (k + 1) w) (h : step M w = some w') : Buffered k w' := by
  rcases w with ⟨q, l, a, r⟩
  cases hm : M q a with
  | none => simp [step, hm] at h
  | some p =>
    rcases p with ⟨q', s⟩
    cases s with
    | write b =>
      simp [step, hm] at h
      subst w'
      simp only [Buffered] at hb ⊢
      omega
    | move d =>
      cases d with
      | left =>
        cases l with
        | nil => simp [step, hm] at h
        | cons b l =>
          simp [step, hm] at h
          subst w'
          simp only [Buffered, List.length_cons] at hb ⊢
          omega
      | right =>
        cases r with
        | nil => simp [step, hm] at h
        | cons b r =>
          simp [step, hm] at h
          subst w'
          simp only [Buffered, List.length_cons] at hb ⊢
          omega

/-- Every finite run in a bounded window is a run of the ordinary machine. -/
theorem reaches_sound (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : StateTransition.Reaches (step M) w w') :
    StateTransition.Reaches (TM0.step M) w.toCfg w'.toCfg := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (step_sound M h)

/-- The halting evaluation of any ordinary configuration has a finite buffered
realization.  Its chosen bound works for every representation with that padding. -/
theorem eval_lifts (M : TM0.Machine Γ Λ) {a z : TM0.Cfg Γ Λ}
    (hz : z ∈ StateTransition.eval (TM0.step M) a) :
    ∃ k, ∀ w : WindowConfig Γ Λ, w.toCfg = a → Buffered k w →
      ∃ w', StateTransition.Reaches (step M) w w' ∧ Terminal M w' := by
  refine StateTransition.evalInduction hz ?_
  intro a ha ih
  cases hs : TM0.step M a with
  | none =>
    refine ⟨0, fun w hw _ => ⟨w, .refl, ?_⟩⟩
    apply (terminal_iff_step_none M w).mpr
    simpa [hw] using hs
  | some b =>
    obtain ⟨k, hk⟩ := ih b hs
    refine ⟨k + 1, fun w hw hb => ?_⟩
    have hb1 : Buffered 1 w := by
      simp only [Buffered] at hb ⊢
      omega
    have heq := step_commutes M w hb1
    rw [hw, hs] at heq
    obtain ⟨w₁, hstep, hw₁⟩ := Option.map_eq_some_iff.mp heq
    obtain ⟨w', hreach, hterm⟩ := hk w₁ hw₁ (buffered_step M hb hstep)
    exact ⟨w', hreach.head hstep, hterm⟩

/-- Adding finitely many terminal blanks changes no infinite tape cells. -/
theorem listBlank_append_padding (l : List Γ) (k : ℕ) :
    ListBlank.mk (l ++ List.replicate k default) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨k, rfl⟩)

/-- A concrete padded initial window for a finite machine input. -/
def initial (k : ℕ) (l : List Γ) : WindowConfig Γ Λ :=
  ⟨default, List.replicate k default, l.headI, l.tail ++ List.replicate k default⟩

@[simp] theorem initial_buffered (k : ℕ) (l : List Γ) :
    Buffered k (initial (Λ := Λ) k l) := by
  simp [Buffered, initial]

@[simp] theorem initial_toCfg (k : ℕ) (l : List Γ) :
    (initial (Λ := Λ) k l).toCfg = TM0.init l := by
  have hleft : ListBlank.mk (List.replicate k (default : Γ)) = ListBlank.mk [] := by
    simpa using listBlank_append_padding ([] : List Γ) k
  simp [initial, toCfg, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk',
    hleft, listBlank_append_padding]

/-- An ordinary machine halts exactly when some finite padded window has a
finite run ending at a genuine halting instruction. -/
theorem halts_iff_finite_window (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔
      ∃ k w, StateTransition.Reaches (step M) (initial k l) w ∧ Terminal M w := by
  constructor
  · intro h
    change (StateTransition.eval (TM0.step M) (TM0.init l)).Dom at h
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := eval_lifts M hz
    obtain ⟨w, hreach, hterm⟩ := hk (initial k l) (initial_toCfg k l) (initial_buffered k l)
    exact ⟨k, w, hreach, hterm⟩
  · rintro ⟨k, w, hreach, hterm⟩
    change (StateTransition.eval (TM0.step M) (TM0.init l)).Dom
    apply Part.dom_iff_mem.mpr
    refine ⟨w.toCfg, StateTransition.mem_eval.mpr ⟨?_, ?_⟩⟩
    · simpa only [initial_toCfg] using reaches_sound M hreach
    · exact (terminal_iff_step_none M w).mp hterm

end WindowConfig

end TuranUniversality.Computation
