module

public import TuranUniversality.Computation.ResetProtocol

/-!
# Static local input grammar

Before/Start/Input/End/After symbols force one initial head, blank cells before
and after the input, and a single contiguous input word.  Every Start symbol
is also checked against the finite prescribed input prefix, including its End
symbol.  Thus the frozen input track cannot be chosen as an arbitrary machine
configuration.  The prefix test has the finite radius `input.length + 1`.
-/

@[expose] public section

namespace TuranUniversality.Computation.StaticInput

open Turing Cellular

/-- Static symbols encode blank padding by constructors with no free letter. -/
inductive Symbol (Γ : Type*)
  | before
  | start (a : Γ)
  | input (a : Γ)
  | finish
  | after
  deriving DecidableEq

noncomputable instance {Γ : Type*} [Fintype Γ] : Fintype (Symbol Γ) := by
  classical
  exact
    { elems := {.before, .finish, .after} ∪ Finset.univ.image .start ∪ Finset.univ.image .input
      complete := by intro s; cases s <;> simp }

variable {Γ Λ : Type*}

def Adjacent : Symbol Γ → Symbol Γ → Prop
  | .before, .before => True
  | .before, .start _ => True
  | .start _, .input _ => True
  | .start _, .finish => True
  | .input _, .input _ => True
  | .input _, .finish => True
  | .finish, .after => True
  | .after, .after => True
  | _, _ => False

def Starts : Symbol Γ → Prop
  | .before | .start _ => True
  | _ => False

def Ends : Symbol Γ → Prop
  | .finish | .after => True
  | _ => False

def Tail : Symbol Γ → List (Symbol Γ) → Prop
  | p, [] => Ends p
  | p, q :: s => Adjacent p q ∧ Tail q s

def Accepted : List (Symbol Γ) → Prop
  | [] => False
  | p :: s => Starts p ∧ Tail p s

theorem tail_after (s : List (Symbol Γ)) :
    Tail .after s ↔ s = List.replicate s.length .after := by
  induction s with
  | nil => simp [Tail, Ends]
  | cons q s ih => cases q <;> simp [Tail, Adjacent, ih, List.replicate_succ]

theorem tail_end (s : List (Symbol Γ)) :
    Tail .finish s ↔ s = List.replicate s.length .after := by
  cases s with
  | nil => simp [Tail, Ends]
  | cons q s => cases q <;> simp [Tail, Adjacent, tail_after, List.replicate_succ]

theorem tail_input_form {a : Γ} {s : List (Symbol Γ)} (h : Tail (.input a) s) :
    ∃ w : List Γ, ∃ c : ℕ, s = w.map .input ++ .finish :: List.replicate c .after := by
  induction s generalizing a with
  | nil => simp [Tail, Ends] at h
  | cons q s ih =>
    cases q with
    | before => simp [Tail, Adjacent] at h
    | start b => simp [Tail, Adjacent] at h
    | after => simp [Tail, Adjacent] at h
    | input b =>
      obtain ⟨w, c, hs⟩ := ih h.2
      exact ⟨b :: w, c, by simp [hs]⟩
    | finish =>
      refine ⟨[], s.length, ?_⟩
      simpa only [List.map_nil, List.nil_append] using
        congrArg (List.cons (Symbol.finish : Symbol Γ)) ((tail_end s).mp h.2)

theorem tail_start_input (a : Γ) (s : List (Symbol Γ)) :
    Tail (.start a) s ↔ Tail (.input a) s := by
  cases s with
  | nil => rfl
  | cons q s => cases q <;> rfl

theorem tail_before_form {s : List (Symbol Γ)} (h : Tail .before s) :
    ∃ k : ℕ, ∃ a : Γ, ∃ w : List Γ, ∃ c : ℕ,
      s = List.replicate k .before ++ .start a :: w.map .input ++ .finish :: List.replicate c .after := by
  induction s with
  | nil => simp [Tail, Ends] at h
  | cons q s ih =>
    cases q with
    | input a => simp [Tail, Adjacent] at h
    | finish => simp [Tail, Adjacent] at h
    | after => simp [Tail, Adjacent] at h
    | before =>
      obtain ⟨k, a, w, c, hs⟩ := ih h.2
      exact ⟨k + 1, a, w, c, by simp [List.replicate_succ, hs]⟩
    | start a =>
      obtain ⟨w, c, hs⟩ := tail_input_form ((tail_start_input a s).mp h.2)
      exact ⟨0, a, w, c, by simp [hs]⟩

theorem tail_input_word (a : Γ) (w : List Γ) (c : ℕ) :
    Tail (.input a) (w.map .input ++ .finish :: List.replicate c .after) := by
  induction w generalizing a with
  | nil => simp [Tail, Adjacent, tail_end]
  | cons b w ih => simpa [Tail, Adjacent] using ih b

theorem tail_before_word (k : ℕ) (a : Γ) (w : List Γ) (c : ℕ) :
    Tail .before
      (List.replicate k .before ++ .start a :: w.map .input ++ .finish :: List.replicate c .after) := by
  induction k with
  | zero =>
    simpa [Tail, Adjacent, tail_start_input] using tail_input_word a w c
  | succ k ih => simpa [List.replicate_succ, Tail, Adjacent] using ih

theorem accepted_word (k : ℕ) (a : Γ) (w : List Γ) (c : ℕ) :
    Accepted
      (List.replicate k .before ++ .start a :: w.map .input ++ .finish :: List.replicate c .after) := by
  cases k with
  | zero =>
    simpa [Accepted, Starts, tail_start_input] using tail_input_word a w c
  | succ k => simpa [List.replicate_succ, Accepted, Starts] using tail_before_word k a w c

/-- Adjacent-pair and wall checks force exactly one Start and exactly one End. -/
theorem accepted_iff (s : List (Symbol Γ)) :
    Accepted s ↔ ∃ k : ℕ, ∃ a : Γ, ∃ w : List Γ, ∃ c : ℕ,
      s = List.replicate k .before ++ .start a :: w.map .input ++ .finish :: List.replicate c .after := by
  constructor
  · intro h
    cases s with
    | nil => exact h.elim
    | cons q s =>
      cases q with
      | input a => exact h.1.elim
      | finish => exact h.1.elim
      | after => exact h.1.elim
      | before =>
        obtain ⟨k, a, w, c, hs⟩ := tail_before_form h.2
        exact ⟨k + 1, a, w, c, by simp [List.replicate_succ, hs]⟩
      | start a =>
        obtain ⟨w, c, hs⟩ := tail_input_form ((tail_start_input a s).mp h.2)
        exact ⟨0, a, w, c, by simp [hs]⟩
  · rintro ⟨k, a, w, c, rfl⟩
    exact accepted_word k a w c

/-- The prescribed nonempty input prefix, with the first symbol marked Start. -/
def inputWord : List Γ → List (Symbol Γ)
  | [] => []
  | a :: w => .start a :: w.map .input

/-- Check the finite prescribed prefix at every Start occurrence.  Each check
looks at only `w.length + 1` consecutive symbols, including the End marker. -/
def PrefixCheck (w : List Γ) : List (Symbol Γ) → Prop
  | [] => True
  | .start a :: s => (inputWord w ++ [.finish] <+: .start a :: s) ∧ PrefixCheck w s
  | _ :: s => PrefixCheck w s

theorem prefixCheck_before (w : List Γ) (k : ℕ) (s : List (Symbol Γ)) :
    PrefixCheck w (List.replicate k .before ++ s) ↔ PrefixCheck w s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, PrefixCheck] using ih

theorem prefixCheck_input (w v : List Γ) (s : List (Symbol Γ)) :
    PrefixCheck w (v.map .input ++ s) ↔ PrefixCheck w s := by
  induction v with
  | nil => rfl
  | cons a v ih => simpa [PrefixCheck] using ih

theorem prefixCheck_after (w : List Γ) (c : ℕ) :
    PrefixCheck w (List.replicate c .after) := by
  induction c with
  | zero => trivial
  | succ c ih => simpa [List.replicate_succ, PrefixCheck] using ih

theorem input_tail_prefix (w v : List Γ) (s : List (Symbol Γ)) :
    (w.map .input ++ [.finish] <+: v.map .input ++ .finish :: s) ↔ w = v := by
  induction w generalizing v with
  | nil => cases v <;> simp
  | cons a w ih => cases v <;> simp [ih]

theorem input_word_prefix (w : List Γ) (a : Γ) (v : List Γ) (s : List (Symbol Γ)) :
    (inputWord w ++ [.finish] <+: .start a :: v.map .input ++ .finish :: s) ↔ w = a :: v := by
  cases w with
  | nil => simp [inputWord]
  | cons b w => simp [inputWord, input_tail_prefix]

/-- The bounded Start-prefix checks force the exact specified input word. -/
theorem prefixCheck_word (w : List Γ) (k : ℕ) (a : Γ) (v : List Γ) (c : ℕ) :
    PrefixCheck w
      (List.replicate k .before ++ .start a :: v.map .input ++ .finish :: List.replicate c .after) ↔
      w = a :: v := by
  rw [List.append_assoc, prefixCheck_before]
  simp only [List.cons_append, PrefixCheck, prefixCheck_input,
    prefixCheck_after, and_true]
  simpa only [List.cons_append] using input_word_prefix w a v (List.replicate c .after)

/-- Local static constraints: wall/pair grammar plus the bounded Start prefix. -/
def Valid (w : List Γ) (s : List (Symbol Γ)) : Prop := Accepted s ∧ PrefixCheck w s

/-- This is the static input correctness theorem: legal frozen tracks are
exactly the prescribed input with arbitrary blank padding on both sides. -/
theorem valid_iff (w : List Γ) (s : List (Symbol Γ)) :
    Valid w s ↔ ∃ k c : ℕ, w ≠ [] ∧
      s = List.replicate k .before ++ inputWord w ++ .finish :: List.replicate c .after := by
  constructor
  · rintro ⟨ha, hp⟩
    obtain ⟨k, a, v, c, rfl⟩ := (accepted_iff _).mp ha
    have hw := (prefixCheck_word w k a v c).mp hp
    subst w
    exact ⟨k, c, List.cons_ne_nil _ _, rfl⟩
  · rintro ⟨k, c, hw, rfl⟩
    cases w with
    | nil => exact (hw rfl).elim
    | cons a v => exact ⟨accepted_word k a v c, (prefixCheck_word _ k a v c).mpr rfl⟩

/-- The local static-to-frozen-cell interpretation. -/
def frozen [Inhabited Γ] [Inhabited Λ] : Symbol Γ → Cell Γ Λ
  | .before | .finish | .after => blankCell
  | .start a => (a, some default)
  | .input a => (a, none)

/-- Every valid static row freezes precisely the stated input and one initial
head, with blank padding; its data cannot describe an arbitrary configuration. -/
theorem frozen_valid [Inhabited Γ] [Inhabited Λ] {w : List Γ} {s : List (Symbol Γ)}
    (h : Valid w s) : ∃ k c : ℕ, ∃ a : Γ, ∃ v : List Γ,
      w = a :: v ∧ s.map (frozen (Λ := Λ)) =
        List.replicate k blankCell ++ (a, some (default : Λ)) ::
          v.map (fun b => (b, none)) ++ List.replicate (c + 1) blankCell := by
  obtain ⟨k, c, hw, rfl⟩ := (valid_iff w s).mp h
  cases w with
  | nil => exact (hw rfl).elim
  | cons a v =>
    refine ⟨k, c, a, v, rfl, ?_⟩
    simp [inputWord, frozen, List.map_map, Function.comp_def, List.replicate_succ]

end TuranUniversality.Computation.StaticInput
