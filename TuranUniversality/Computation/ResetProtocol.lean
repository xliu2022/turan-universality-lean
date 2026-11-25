module

public import TuranUniversality.Computation.ResetGrammar

/-!
# Locally certified reset and finite return

The frozen initial-cell track is an explicit parameter.  It is preserved by
the transition rule; a later static input grammar must force it to encode the
specified input and blank padding.  This file does not treat arbitrary frozen
tracks as valid initial inputs.
-/

@[expose] public section

namespace TuranUniversality.Computation.ResetProtocol

open Turing Cellular ResetGrammar

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- A finite alphabet of dynamic phase tags and underlying machine cells. -/
abbrev Symbol (Γ Λ : Type*) := Tag × Cell Γ Λ

abbrev Segment (n : ℕ) (Γ Λ : Type*) := Fin n → Symbol Γ Λ

/-- The canonical initial-phase symbol. -/
def initialSymbol : Symbol Γ Λ := (.initial, blankCell)

/-- A complete initial-phase segment. -/
def initialRow (n : ℕ) : Segment n Γ Λ := fun _ => initialSymbol

/-- A running segment carrying a finite machine row. -/
def runningRow {n : ℕ} (r : FiniteRow n Γ Λ) : Segment n Γ Λ := fun i => (.running, r i)

/-- Forget the dynamic decoration. -/
def data {n : ℕ} (s : Segment n Γ Λ) : FiniteRow n Γ Λ := fun i => (s i).2

/-- The phase word checked by the horizontal local grammar. -/
def tags {n : ℕ} (s : Segment n Γ Λ) : List Tag := List.ofFn fun i => (s i).1

/-- Local well-formedness of a decorated cell.  A halt decoration contains an
actual undefined machine instruction; pre/post decorations contain no head. -/
def ValidSymbol (M : TM0.Machine Γ Λ) (s : Symbol Γ Λ) : Prop :=
  match s.1 with
  | .initial => s.2 = blankCell
  | .running => True
  | .pre | .post => s.2.2 = none
  | .halt => ∃ q, s.2.2 = some q ∧ M q s.2.1 = none

/-- The finite row satisfies the horizontal pair grammar and every unary check. -/
def Admissible {n : ℕ} (M : TM0.Machine Γ Λ) (s : Segment n Γ Λ) : Prop :=
  Accepted (tags s) ∧ ∀ i, ValidSymbol M (s i)

/-- The exact prefix--head--suffix reset phase. -/
def IsReset {n : ℕ} (s : Segment n Γ Λ) : Prop :=
  ∃ a b : ℕ, tags s = List.replicate a .pre ++ .halt :: List.replicate b .post

omit [Inhabited Γ] [Inhabited Λ] in
@[simp] theorem data_running {n : ℕ} (r : FiniteRow n Γ Λ) : data (runningRow r) = r := rfl

theorem initial_admissible (M : TM0.Machine Γ Λ) {n : ℕ} (hn : 0 < n) :
    Admissible M (initialRow n) := by
  constructor
  · apply (accepted_iff _).mpr
    exact Or.inl ⟨n, hn, by simp [tags, initialRow, initialSymbol]⟩
  · intro i
    rfl

theorem running_admissible (M : TM0.Machine Γ Λ) {n : ℕ} (hn : 0 < n)
    (r : FiniteRow n Γ Λ) : Admissible M (runningRow r) := by
  constructor
  · apply (accepted_iff _).mpr
    exact Or.inr (Or.inl ⟨n, hn, by simp [tags, runningRow]⟩)
  · intro i
    trivial

omit [Inhabited Γ] [Inhabited Λ] in
theorem tag_mem {n : ℕ} (s : Segment n Γ Λ) (i : Fin n) : (s i).1 ∈ tags s :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

theorem admissible_cases {n : ℕ} (M : TM0.Machine Γ Λ) {s : Segment n Γ Λ}
    (h : Admissible M s) :
    s = initialRow n ∨ (∃ r : FiniteRow n Γ Λ, s = runningRow r) ∨ IsReset s := by
  rcases (accepted_iff _).mp h.1 with ⟨m, _, hs⟩ | ⟨m, _, hs⟩ | hr
  · left
    funext i
    have hi : (s i).1 = .initial := List.eq_of_mem_replicate (hs ▸ tag_mem s i)
    have hv := h.2 i
    simp only [ValidSymbol, hi] at hv
    exact Prod.ext hi hv
  · right; left
    refine ⟨data s, ?_⟩
    funext i
    have hi : (s i).1 = .running := List.eq_of_mem_replicate (hs ▸ tag_mem s i)
    exact Prod.ext hi rfl
  · exact Or.inr (Or.inr hr)

omit [Inhabited Γ] [Inhabited Λ] in
theorem reset_tags {n : ℕ} {s : Segment n Γ Λ} (h : IsReset s) (i : Fin n) :
    (s i).1 = .pre ∨ (s i).1 = .halt ∨ (s i).1 = .post := by
  obtain ⟨a, b, hs⟩ := h
  have hi := tag_mem s i
  rw [hs] at hi
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hi
  rcases hi with ⟨_, heq⟩ | heq | ⟨_, heq⟩
  · exact Or.inl heq
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr heq)

omit [Inhabited Γ] [Inhabited Λ] in
theorem reset_not_initial {n : ℕ} {s : Segment n Γ Λ} (h : IsReset s) (i : Fin n) :
    (s i).1 ≠ .initial := by
  rcases reset_tags h i with h | h | h <;> simp [h]

theorem reset_haltingHead {n : ℕ} (M : TM0.Machine Γ Λ) {s : Segment n Γ Λ}
    (ha : Admissible M s) (hr : IsReset s) : FiniteHaltingHead M (data s) := by
  obtain ⟨a, b, hs⟩ := hr
  have hmem : Tag.halt ∈ tags s := by rw [hs]; simp
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  have hv := ha.2 i
  rw [ValidSymbol, hi] at hv
  obtain ⟨q, hq, hhalt⟩ := hv
  exact ⟨i, (s i).2.1, q, Prod.ext rfl hq, hhalt⟩

/-- Extend a decorated segment by running blank boundary cells. -/
def extendSymbol {n : ℕ} (s : Segment n Γ Λ) (i : ℤ) : Symbol Γ Λ :=
  if h : InBounds n i then s ⟨i.toNat, by obtain ⟨_, _⟩ := h; omega⟩
  else (.running, blankCell)

omit [Inhabited Λ] in
theorem extendSymbol_data {n : ℕ} (s : Segment n Γ Λ) (i : ℤ) :
    (extendSymbol s i).2 = extend (data s) i := by
  by_cases hi : InBounds n i <;> simp [extendSymbol, extend, data, hi]

/-- A four-cell transition relation: old left/middle/right cells and the new
middle cell.  The extra `frozen` field is the old and new immutable input track. -/
def LocalStep (M : TM0.Machine Γ Λ) (frozen : Cell Γ Λ)
    (l a r b : Symbol Γ Λ) : Prop :=
  match a.1 with
  | .initial => b = (.running, frozen)
  | .running => b.1 ≠ .initial ∧ b.2 = localRule M l.2 a.2 r.2
  | .pre | .halt | .post => b = initialSymbol

/-- A transition checks a fixed local relation at every interior cell. -/
def Step {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ)
    (s t : Segment n Γ Λ) : Prop :=
  Admissible M s ∧ Admissible M t ∧ ∀ i : Fin n,
    LocalStep M (frozen i) (extendSymbol s (i - 1)) (s i)
      (extendSymbol s (i + 1)) (t i)

theorem step_initial {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ)
    (hn : 0 < n) : Step M frozen (initialRow n) (runningRow frozen) := by
  refine ⟨initial_admissible M hn, running_admissible M hn frozen, ?_⟩
  intro i
  rfl

theorem step_from_initial {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ)
    {t : Segment n Γ Λ} (h : Step M frozen (initialRow n) t) :
    t = runningRow frozen := by
  funext i
  exact h.2.2 i

theorem step_from_running {n : ℕ} (M : TM0.Machine Γ Λ) (frozen r : FiniteRow n Γ Λ)
    {t : Segment n Γ Λ} (h : Step M frozen (runningRow r) t) :
    (∀ i, (t i).1 ≠ .initial) ∧ data t = finiteUpdate M r := by
  constructor
  · intro i
    exact (h.2.2 i).1
  · funext i
    have hi := (h.2.2 i).2
    simpa only [extendSymbol_data, data_running, finiteUpdate, restrict, update,
      runningRow, data, extend_at] using hi

theorem step_running {n : ℕ} (M : TM0.Machine Γ Λ) (frozen r : FiniteRow n Γ Λ)
    (hn : 0 < n) : Step M frozen (runningRow r) (runningRow (finiteUpdate M r)) := by
  refine ⟨running_admissible M hn r, running_admissible M hn _, ?_⟩
  intro i
  refine ⟨by simp [runningRow], ?_⟩
  simp only [extendSymbol_data, data_running, finiteUpdate, restrict, update, runningRow, extend_at]

theorem step_reset {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ)
    (hn : 0 < n) {s : Segment n Γ Λ} (ha : Admissible M s) (hr : IsReset s) :
    Step M frozen s (initialRow n) := by
  refine ⟨ha, initial_admissible M hn, ?_⟩
  intro i
  rcases reset_tags hr i with h | h | h <;>
    simp only [LocalStep, h, initialRow]

theorem step_to_reset {n : ℕ} (M : TM0.Machine Γ Λ) (frozen r : FiniteRow n Γ Λ)
    (hn : 0 < n) {s : Segment n Γ Λ} (ha : Admissible M s) (hr : IsReset s)
    (hd : data s = finiteUpdate M r) : Step M frozen (runningRow r) s := by
  refine ⟨running_admissible M hn r, ha, ?_⟩
  intro i
  refine ⟨reset_not_initial hr i, ?_⟩
  have hi := congrFun hd i
  simpa only [extendSymbol_data, data_running, finiteUpdate, restrict, update,
    runningRow, data, extend_at] using hi

/-- A genuine finite computation detects an actual terminal head. -/
def EventuallyHalts {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ) : Prop :=
  ∃ t : ℕ, FiniteHaltingHead M ((finiteUpdate M)^[t] frozen)

/-- A positive finite return, excluding the vacuous zero-step loop. -/
def Returns {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ) : Prop :=
  Relation.TransGen (Step M frozen) (initialRow n) (initialRow n)

/-- Before a certified halt, every nonempty initial path is still the actual
running cellular trajectory.  Arbitrary periodic running configurations do
not satisfy a return to the initial phase. -/
theorem positive_reach_invariant {n : ℕ} (M : TM0.Machine Γ Λ)
    (frozen : FiniteRow n Γ Λ) (hn : 0 < n) {s : Segment n Γ Λ}
    (h : Relation.TransGen (Step M frozen) (initialRow n) s) :
    EventuallyHalts M frozen ∨
      ∃ t : ℕ, s = runningRow ((finiteUpdate M)^[t] frozen) := by
  induction h with
  | single hs => exact Or.inr ⟨0, step_from_initial M frozen hs⟩
  | tail _ hs ih =>
    rcases ih with hh | ⟨t, heq⟩
    · exact Or.inl hh
    · rw [heq] at hs
      have hrun := step_from_running M frozen _ hs
      rcases admissible_cases M hs.2.1 with hini | ⟨r, hr⟩ | hreset
      · have hc := hrun.1 ⟨0, hn⟩
        simp [hini, initialRow, initialSymbol] at hc
      · right
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply', hr]
        congr 1
        simpa only [hr, data_running] using hrun.2
      · left
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply', ← hrun.2]
        exact reset_haltingHead M hs.2.1 hreset

/-- Every positive reset return certifies actual finite cellular halting. -/
theorem returns_sound {n : ℕ} (M : TM0.Machine Γ Λ) (frozen : FiniteRow n Γ Λ)
    (hn : 0 < n) (h : Returns M frozen) : EventuallyHalts M frozen := by
  rcases positive_reach_invariant M frozen hn h with hh | ⟨t, ht⟩
  · exact hh
  · have hc := congrArg (fun s : Segment n Γ Λ => (s ⟨0, hn⟩).1) ht
    cases hc

/-- All existing heads in this finite row have genuinely halted. -/
def AllHeadsTerminal {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) : Prop :=
  ∀ i q, (r i).2 = some q → M q (r i).1 = none

theorem finiteUpdate_fixed_of_terminal {n : ℕ} (M : TM0.Machine Γ Λ)
    (r : FiniteRow n Γ Λ) (h : AllHeadsTerminal M r) : finiteUpdate M r = r := by
  have hext : ∀ i q, (extend r i).2 = some q → M q (extend r i).1 = none := by
    intro i q hq
    by_cases hi : InBounds n i
    · simp only [extend, hi, dite_true] at hq ⊢
      exact h _ q hq
    · simp [extend, hi, blankCell] at hq
  have hin : ∀ i d, incoming M d (extend r i) = none := by
    intro i d
    cases hq : (extend r i).2 with
    | none => simp [incoming, hq]
    | some q => simp [incoming, hq, hext i q hq]
  funext i
  simp only [finiteUpdate, restrict, update, extend_at, localRule]
  cases hq : (r i).2 with
  | none =>
    simp only [hin, Option.or_none]
    exact Prod.ext rfl hq.symm
  | some q => simp [h i q hq]

/-- Exactly one head, and that head has a genuine halting instruction. -/
def UniqueHaltingHead {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) : Prop :=
  ∃ j : Fin n, ∃ q : Λ, (r j).2 = some q ∧ M q (r j).1 = none ∧
    ∀ i : Fin n, i ≠ j → (r i).2 = none

omit [Inhabited Γ] in
theorem uniqueHaltingHead_allTerminal {n : ℕ} (M : TM0.Machine Γ Λ)
    {r : FiniteRow n Γ Λ} (h : UniqueHaltingHead M r) : AllHeadsTerminal M r := by
  obtain ⟨j, q, hq, hm, hother⟩ := h
  intro i q' hi
  by_cases hij : i = j
  · subst i
    have hqq : q = q' := Option.some.inj (hq.symm.trans hi)
    simpa only [← hqq] using hm
  · rw [hother i hij] at hi
    cases hi

/-- Canonically decorate a unique terminal head by local prefix/suffix tags. -/
def decorate {n : ℕ} (j : Fin n) (r : FiniteRow n Γ Λ) : Segment n Γ Λ :=
  fun i => (resetTag j i, r i)

omit [Inhabited Γ] [Inhabited Λ] in
theorem decorate_reset {n : ℕ} (j : Fin n) (r : FiniteRow n Γ Λ) :
    IsReset (decorate j r) :=
  ⟨j.val, n - j.val - 1, resetTag_word j⟩

theorem decorate_admissible {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ)
    (j : Fin n) (q : Λ) (hq : (r j).2 = some q) (hm : M q (r j).1 = none)
    (hother : ∀ i : Fin n, i ≠ j → (r i).2 = none) : Admissible M (decorate j r) := by
  refine ⟨accepted_resetTag j, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    simp only [ValidSymbol, decorate, resetTag, lt_self_iff_false, ite_false, ite_true]
    exact ⟨q, hq, hm⟩
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hlt : i.val < j.val
    · simpa [ValidSymbol, decorate, resetTag, hlt] using hother i hij
    · simpa [ValidSymbol, decorate, resetTag, hlt, hv] using hother i hij

theorem running_iterations {n : ℕ} (M : TM0.Machine Γ Λ)
    (frozen : FiniteRow n Γ Λ) (hn : 0 < n) (t : ℕ) :
    Relation.ReflTransGen (Step M frozen) (runningRow frozen)
      (runningRow ((finiteUpdate M)^[t] frozen)) := by
  induction t with
  | zero => exact .refl
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail (step_running M frozen _ hn)

/-- A single terminal head supplies an actual locally admissible reset row
and a positive return to the initial phase. -/
theorem returns_of_unique_halting {n : ℕ} (M : TM0.Machine Γ Λ)
    (frozen : FiniteRow n Γ Λ) (hn : 0 < n) (t : ℕ)
    (h : UniqueHaltingHead M ((finiteUpdate M)^[t] frozen)) : Returns M frozen := by
  have hfix := finiteUpdate_fixed_of_terminal M _ (uniqueHaltingHead_allTerminal M h)
  obtain ⟨j, q, hq, hm, hother⟩ := h
  let d := decorate j ((finiteUpdate M)^[t] frozen)
  have ha : Admissible M d := decorate_admissible M _ j q hq hm hother
  have hr : IsReset d := decorate_reset j _
  have hstep : Step M frozen (runningRow ((finiteUpdate M)^[t] frozen)) d :=
    step_to_reset M frozen _ hn ha hr hfix.symm
  exact ((Relation.TransGen.head' (step_initial M frozen hn)
    (running_iterations M frozen hn t)).tail hstep).tail (step_reset M frozen hn ha hr)

/-- A finite tuple representing an actual terminal window has exactly the
single terminal head required by the reset grammar. -/
theorem uniqueHaltingHead_of_window {n : ℕ} (M : TM0.Machine Γ Λ)
    {r : FiniteRow n Γ Λ} (w : WindowConfig Γ Λ) (hw : w.width = n)
    (hr : extend r = windowRow w) (ht : WindowConfig.Terminal M w) :
    UniqueHaltingHead M r := by
  let j : Fin n := ⟨w.left.length, by rw [← hw]; simp [WindowConfig.width]; omega⟩
  have heq : ∀ i : Fin n, r i = windowRow w (i : ℤ) := by
    intro i
    simpa only [extend_at] using congrFun hr (i : ℤ)
  refine ⟨j, w.state, ?_, ?_, ?_⟩
  · rw [heq j]
    simp [windowRow, row, WindowConfig.toCfg, j]
  · rw [heq j]
    simpa only [WindowConfig.Terminal, windowRow, row, WindowConfig.toCfg,
      j, sub_self, Tape.nth_zero] using ht
  · intro i hij
    have hi : (i : ℤ) ≠ (w.left.length : ℤ) := by
      intro hc
      apply hij
      apply Fin.ext
      exact_mod_cast hc
    rw [heq i]
    simp [windowRow, row, hi]

/-- The frozen track is the exact specified finite input, with blank padding
on both sides and its unique initial head. -/
def inputFrozen (k : ℕ) (l : List Γ) :
    FiniteRow (WindowConfig.initial (Λ := Λ) k l).width Γ Λ :=
  restrict (WindowConfig.initial (Λ := Λ) k l).width
    (windowRow (WindowConfig.initial k l))

/-- The proved reset equivalence for an actual ordinary machine input.
All row constraints are finite unary, adjacent-pair, or radius-one constraints;
the frozen track in this theorem is fixed to `inputFrozen`, not arbitrary. -/
theorem halts_iff_reset_return (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ ∃ k : ℕ, Returns M (inputFrozen (Λ := Λ) k l) := by
  constructor
  · intro h
    obtain ⟨k, w, hreach, ht⟩ := (WindowConfig.halts_iff_finite_window M l).mp h
    obtain ⟨t, hiter⟩ := bounded_iterate_of_reaches M hreach
    have hext0 : extend (inputFrozen (Λ := Λ) k l) =
        windowRow (WindowConfig.initial k l) :=
      extend_restrict (windowRow_supported _)
    have hext : extend ((finiteUpdate M)^[t] (inputFrozen (Λ := Λ) k l)) = windowRow w := by
      rw [extend_finite_iterate, hext0]
      exact hiter
    refine ⟨k, returns_of_unique_halting M _ (WindowConfig.width_pos _) t ?_⟩
    exact uniqueHaltingHead_of_window M w (WindowConfig.width_reaches M hreach) hext ht
  · rintro ⟨k, hr⟩
    obtain ⟨t, ht⟩ := returns_sound M (inputFrozen (Λ := Λ) k l) (WindowConfig.width_pos _) hr
    exact (halts_iff_finite_cellular M l).mpr ⟨k, t, ht⟩

/-- A fixed finite-state ordinary interpreter and a fixed finite local reset
alphabet realize the exact universal binary-word halting predicate. -/
theorem exists_finite_reset_interpreter :
    ∃ (c : ToPartrec.Code)
      (initial : Inhabited {q // q ∈ tapeStateSupport c})
      (M : @TM0.Machine TapeAlphabet {q // q ∈ tapeStateSupport c} initial),
      ∀ β : BinaryWord,
        WordHalts β ↔ ∃ k : ℕ,
          @Returns TapeAlphabet {q // q ∈ tapeStateSupport c} inferInstance initial
            _ M (@inputFrozen TapeAlphabet {q // q ∈ tapeStateSupport c} inferInstance
              initial k (tapeInput (encodeWord β))) := by
  obtain ⟨c, initial, M, hM⟩ := exists_finite_word_tapeMachine
  let _ := initial
  refine ⟨c, initial, M, fun β => ?_⟩
  exact (hM β).symm.trans (halts_iff_reset_return M (tapeInput (encodeWord β)))

end TuranUniversality.Computation.ResetProtocol
