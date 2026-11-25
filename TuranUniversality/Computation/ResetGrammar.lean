module

public import TuranUniversality.Computation.BoundedCellular

/-!
# The finite local prefix--halting-head--suffix reset grammar

Only neighboring phase tags and the two wall tags are checked.  The proved
language characterization shows that a legal wall segment is entirely
initial, entirely running, or has exactly one halting-head decoration between
a prefix of `pre` decorations and a suffix of `post` decorations.
-/

@[expose] public section

namespace TuranUniversality.Computation.ResetGrammar

open Turing Cellular

/-- Interior phase tags; the two walls are handled by endpoint predicates. -/
inductive Tag
  | initial
  | running
  | pre
  | halt
  | post
  deriving DecidableEq

instance : Fintype Tag where
  elems := {.initial, .running, .pre, .halt, .post}
  complete t := by cases t <;> simp

/-- Allowed neighbors inside one wall segment. -/
def Adjacent : Tag → Tag → Prop
  | .initial, .initial => True
  | .running, .running => True
  | .pre, .pre => True
  | .pre, .halt => True
  | .halt, .post => True
  | .post, .post => True
  | _, _ => False

/-- Allowed successors of the left wall. -/
def Starts : Tag → Prop
  | .post => False
  | _ => True

/-- Allowed predecessors of the right wall. -/
def Ends : Tag → Prop
  | .pre => False
  | _ => True

/-- Check only successive adjacent pairs and the final wall edge. -/
def Tail : Tag → List Tag → Prop
  | p, [] => Ends p
  | p, q :: s => Adjacent p q ∧ Tail q s

/-- Check both walls and every neighboring pair of a nonempty segment. -/
def Accepted : List Tag → Prop
  | [] => False
  | p :: s => Starts p ∧ Tail p s

instance (p q : Tag) : Decidable (Adjacent p q) := by
  cases p <;> cases q <;> simp only [Adjacent] <;> infer_instance

instance (p : Tag) : Decidable (Starts p) := by
  cases p <;> simp only [Starts] <;> infer_instance

instance (p : Tag) : Decidable (Ends p) := by
  cases p <;> simp only [Ends] <;> infer_instance

instance (p : Tag) (s : List Tag) : Decidable (Tail p s) := by
  induction s generalizing p with
  | nil => exact inferInstanceAs (Decidable (Ends p))
  | cons q s ih => exact @instDecidableAnd _ _ inferInstance (ih q)

instance (s : List Tag) : Decidable (Accepted s) := by
  cases s with
  | nil => exact isFalse id
  | cons p s => exact inferInstanceAs (Decidable (Starts p ∧ Tail p s))

theorem tail_initial (s : List Tag) :
    Tail .initial s ↔ s = List.replicate s.length .initial := by
  induction s with
  | nil => simp [Tail, Ends]
  | cons q s ih => cases q <;> simp [Tail, Adjacent, ih, List.replicate_succ]

theorem tail_running (s : List Tag) :
    Tail .running s ↔ s = List.replicate s.length .running := by
  induction s with
  | nil => simp [Tail, Ends]
  | cons q s ih => cases q <;> simp [Tail, Adjacent, ih, List.replicate_succ]

theorem tail_post (s : List Tag) :
    Tail .post s ↔ s = List.replicate s.length .post := by
  induction s with
  | nil => simp [Tail, Ends]
  | cons q s ih => cases q <;> simp [Tail, Adjacent, ih, List.replicate_succ]

theorem tail_halt (s : List Tag) :
    Tail .halt s ↔ s = List.replicate s.length .post := by
  cases s with
  | nil => simp [Tail, Ends]
  | cons q s => cases q <;> simp [Tail, Adjacent, tail_post, List.replicate_succ]

theorem tail_pre_form {s : List Tag} (h : Tail .pre s) :
    ∃ a b : ℕ, s = List.replicate a .pre ++ .halt :: List.replicate b .post := by
  induction s with
  | nil => simp [Tail, Ends] at h
  | cons q s ih =>
    cases q with
    | initial => simp [Tail, Adjacent] at h
    | running => simp [Tail, Adjacent] at h
    | post => simp [Tail, Adjacent] at h
    | pre =>
      obtain ⟨a, b, hs⟩ := ih h.2
      exact ⟨a + 1, b, by simp [List.replicate_succ, hs]⟩
    | halt =>
      refine ⟨0, s.length, ?_⟩
      simpa only [List.replicate_zero, List.nil_append] using
        congrArg (List.cons Tag.halt) ((tail_halt s).mp h.2)

theorem tail_pre_reset (a b : ℕ) :
    Tail .pre (List.replicate a .pre ++ .halt :: List.replicate b .post) := by
  induction a with
  | zero => simp [Tail, Adjacent, tail_halt]
  | succ a ih => simpa [List.replicate_succ, Tail, Adjacent] using ih

theorem accepted_reset (a b : ℕ) :
    Accepted (List.replicate a .pre ++ .halt :: List.replicate b .post) := by
  cases a with
  | zero => simp [Accepted, Starts, tail_halt]
  | succ a => simpa [List.replicate_succ, Accepted, Starts] using tail_pre_reset a b

/-- The adjacency checks enforce a uniform phase or exactly one reset head. -/
theorem accepted_iff (s : List Tag) :
    Accepted s ↔
      (∃ n : ℕ, 0 < n ∧ s = List.replicate n .initial) ∨
      (∃ n : ℕ, 0 < n ∧ s = List.replicate n .running) ∨
      (∃ a b : ℕ, s = List.replicate a .pre ++ .halt :: List.replicate b .post) := by
  constructor
  · intro h
    cases s with
    | nil => exact h.elim
    | cons q s =>
      cases q with
      | initial =>
        exact Or.inl ⟨s.length + 1, by omega,
          by simpa only [List.replicate_succ] using
            congrArg (List.cons Tag.initial) ((tail_initial s).mp h.2)⟩
      | running =>
        exact Or.inr (Or.inl ⟨s.length + 1, by omega,
          by simpa only [List.replicate_succ] using
            congrArg (List.cons Tag.running) ((tail_running s).mp h.2)⟩)
      | pre =>
        obtain ⟨a, b, hs⟩ := tail_pre_form h.2
        exact Or.inr (Or.inr ⟨a + 1, b, by simp [List.replicate_succ, hs]⟩)
      | halt =>
        exact Or.inr (Or.inr ⟨0, s.length,
          by simpa only [List.replicate_zero, List.nil_append] using
            congrArg (List.cons Tag.halt) ((tail_halt s).mp h.2)⟩)
      | post => exact h.1.elim
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨a, b, rfl⟩)
    · cases n with
      | zero => omega
      | succ n => simp [List.replicate_succ, Accepted, Starts, tail_initial]
    · cases n with
      | zero => omega
      | succ n => simp [List.replicate_succ, Accepted, Starts, tail_running]
    · exact accepted_reset a b

/-- In every reset segment, the locally certified head occurs once. -/
theorem reset_halt_count (a b : ℕ) :
    (List.replicate a Tag.pre ++ Tag.halt :: List.replicate b Tag.post).count Tag.halt = 1 := by
  simp [List.count_replicate]

/-- The local reset tag determined by the unique head position. -/
def resetTag {n : ℕ} (j i : Fin n) : Tag :=
  if i.val < j.val then .pre else if i.val = j.val then .halt else .post

theorem resetTag_word {n : ℕ} (j : Fin n) :
    List.ofFn (resetTag j) =
      List.replicate j.val .pre ++ .halt :: List.replicate (n - j.val - 1) .post := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [List.ofFn_succ, resetTag]
    · have hh := ih j
      unfold resetTag at hh
      simpa [List.ofFn_succ, resetTag, List.replicate_succ] using
        congrArg (List.cons Tag.pre) hh

theorem accepted_resetTag {n : ℕ} (j : Fin n) : Accepted (List.ofFn (resetTag j)) := by
  rw [resetTag_word]
  exact accepted_reset j.val (n - j.val - 1)

end TuranUniversality.Computation.ResetGrammar
