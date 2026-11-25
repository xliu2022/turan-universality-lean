module

public import TuranUniversality.Computation.Cellular

/-!
# Finite intervals, disappearing boundary heads, and exact halting detection

The finite cellular update fixes a blank, headless exterior.  A head moving
across a boundary is lost and can never reappear.  In particular, an eventual
halting-head certificate cannot be caused by a finite-window boundary.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Turing

namespace WindowConfig

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- The fixed number of tape cells in a window. -/
def width (w : WindowConfig Γ Λ) : ℕ := w.left.length + 1 + w.right.length

omit [Inhabited Γ] [Inhabited Λ] in
theorem width_pos (w : WindowConfig Γ Λ) : 0 < w.width := by
  simp [width]

omit [Inhabited Γ] in
theorem width_step (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : step M w = some w') : w'.width = w.width := by
  rcases w with ⟨q, l, a, r⟩
  cases hm : M q a with
  | none => simp [step, hm] at h
  | some p =>
    rcases p with ⟨q', s⟩
    cases s with
    | write b =>
      simp [step, hm] at h
      subst w'
      rfl
    | move d =>
      cases d with
      | left =>
        cases l with
        | nil => simp [step, hm] at h
        | cons b l =>
          simp [step, hm] at h
          subst w'
          simp only [width, List.length_cons]
          omega
      | right =>
        cases r with
        | nil => simp [step, hm] at h
        | cons b r =>
          simp [step, hm] at h
          subst w'
          simp only [width, List.length_cons]
          omega

omit [Inhabited Γ] in
theorem width_reaches (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : StateTransition.Reaches (step M) w w') : w'.width = w.width := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact (width_step M h).trans ih

end WindowConfig

namespace Cellular

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Coordinates belonging to a finite interval of `n` cells. -/
def InBounds (n : ℕ) (i : ℤ) : Prop := 0 ≤ i ∧ i < n

instance (n : ℕ) (i : ℤ) : Decidable (InBounds n i) := inferInstanceAs (Decidable (_ ∧ _))

/-- The fixed exterior has blank letters and no head. -/
def blankCell : Cell Γ Λ := (default, none)

/-- A row has no machine head at any position. -/
def Headless (r : Row Γ Λ) : Prop := ∀ i, (r i).2 = none

/-- A finite interval agrees with the fixed blank exterior. -/
def Supported (n : ℕ) (r : Row Γ Λ) : Prop :=
  ∀ i, ¬InBounds n i → r i = blankCell

/-- Forget every cell outside the interval. -/
def truncate (n : ℕ) (r : Row Γ Λ) : Row Γ Λ :=
  fun i => if InBounds n i then r i else blankCell

/-- The local synchronous update on a finite interval with blank exterior. -/
def boundedUpdate (n : ℕ) (M : TM0.Machine Γ Λ) (r : Row Γ Λ) : Row Γ Λ :=
  truncate n (update M r)

omit [Inhabited Λ] in
theorem truncate_supported (n : ℕ) (r : Row Γ Λ) : Supported n (truncate n r) := by
  intro i hi
  simp [truncate, hi]

omit [Inhabited Λ] in
theorem truncate_eq {n : ℕ} {r : Row Γ Λ} (h : Supported n r) : truncate n r = r := by
  funext i
  by_cases hi : InBounds n i
  · simp [truncate, hi]
  · simp [truncate, hi, h i hi]

omit [Inhabited Λ] in
theorem truncate_headless (n : ℕ) {r : Row Γ Λ} (h : Headless r) :
    Headless (truncate n r) := by
  intro i
  by_cases hi : InBounds n i <;> simp [truncate, hi, h i, blankCell]

omit [Inhabited Γ] in
theorem update_headless (M : TM0.Machine Γ Λ) {r : Row Γ Λ} (h : Headless r) :
    Headless (update M r) := by
  intro i
  simp [update, localRule, incoming, h i, h (i - 1), h (i + 1)]

theorem boundedUpdate_headless (n : ℕ) (M : TM0.Machine Γ Λ) {r : Row Γ Λ}
    (h : Headless r) : Headless (boundedUpdate n M r) :=
  truncate_headless n (update_headless M h)

omit [Inhabited Λ] in
theorem windowRow_outside (w : WindowConfig Γ Λ) (i : ℤ)
    (h : ¬InBounds w.width i) : windowRow w i = blankCell := by
  have hi : i ≠ (w.left.length : ℤ) := by
    simp only [InBounds, WindowConfig.width] at h
    omega
  simp only [windowRow, row, WindowConfig.toCfg, hi, ite_false, blankCell,
    Prod.mk.injEq, and_true]
  rcases lt_or_ge i 0 with hneg | hpos
  · have heq : i - (w.left.length : ℤ) = -((w.left.length - i - 1).toNat + 1 : ℕ) := by
      omega
    rw [heq]
    change w.left.getI (w.left.length - i - 1).toNat = default
    exact List.getI_eq_default w.left (by omega)
  · have hi' : (w.width : ℤ) ≤ i := by
      simp only [InBounds, not_and_or, not_le, not_lt] at h
      omega
    have heq : i - (w.left.length : ℤ) = ((i - w.left.length - 1).toNat + 1 : ℕ) := by
      simp only [WindowConfig.width] at hi'
      omega
    rw [heq]
    change w.right.getI (i - w.left.length - 1).toNat = default
    exact List.getI_eq_default w.right (by simp only [WindowConfig.width] at hi'; omega)

omit [Inhabited Λ] in
theorem windowRow_supported (w : WindowConfig Γ Λ) : Supported w.width (windowRow w) :=
  windowRow_outside w

theorem boundedUpdate_window_step (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : WindowConfig.step M w = some w') :
    boundedUpdate w.width M (windowRow w) = windowRow w' := by
  rw [boundedUpdate, update_window_step M h, ← WindowConfig.width_step M h]
  exact truncate_eq (windowRow_supported w')

theorem boundedUpdate_window_halt (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ)
    (h : WindowConfig.Terminal M w) :
    boundedUpdate w.width M (windowRow w) = windowRow w := by
  have hu : update M (windowRow w) = windowRow w :=
    update_halt M w.left.length w.toCfg h
  rw [boundedUpdate, hu]
  exact truncate_eq (windowRow_supported w)

omit [Inhabited Λ] in
theorem truncate_row_headless (n : ℕ) (p : ℤ) (c : TM0.Cfg Γ Λ)
    (hp : ¬InBounds n p) : Headless (truncate n (row p c)) := by
  intro i
  by_cases hi : InBounds n i
  · have hip : i ≠ p := by intro heq; exact hp (heq ▸ hi)
    simp [truncate, hi, row, hip]
  · simp [truncate, hi, blankCell]

/-- Boundary overflow removes the unique head.  It cannot manufacture a
halting state, and subsequent updates remain headless. -/
theorem boundedUpdate_overflow_headless (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ)
    (hs : WindowConfig.step M w = none) (ht : ¬WindowConfig.Terminal M w) :
    Headless (boundedUpdate w.width M (windowRow w)) := by
  rcases w with ⟨q, l, a, r⟩
  cases hm : M q a with
  | none => exact (ht hm).elim
  | some p =>
    rcases p with ⟨q', s⟩
    cases s with
    | write b => simp [WindowConfig.step, hm] at hs
    | move d =>
      cases d with
      | left =>
        cases l with
        | nil =>
          unfold boundedUpdate windowRow
          simp only [List.length_nil, Nat.cast_zero]
          rw [update_move_left M 0 (WindowConfig.toCfg ⟨q, [], a, r⟩) hm]
          apply truncate_row_headless
          simp [InBounds]
        | cons b l => simp [WindowConfig.step, hm] at hs
      | right =>
        cases r with
        | nil =>
          unfold boundedUpdate windowRow
          rw [update_move_right M (l.length : ℤ) (WindowConfig.toCfg ⟨q, l, a, []⟩) hm]
          apply truncate_row_headless
          simp [InBounds, WindowConfig.width]
        | cons b r => simp [WindowConfig.step, hm] at hs

/-- Every reachable bounded cellular row is either a genuine finite-window
configuration or has permanently lost its head at the boundary. -/
theorem bounded_iterate_cases (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ) (n : ℕ) :
    Headless ((boundedUpdate w.width M)^[n] (windowRow w)) ∨
      ∃ w', StateTransition.Reaches (WindowConfig.step M) w w' ∧
        (boundedUpdate w.width M)^[n] (windowRow w) = windowRow w' := by
  induction n with
  | zero => exact Or.inr ⟨w, .refl, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hnone | ⟨w', hreach, hr⟩
    · exact Or.inl (boundedUpdate_headless w.width M hnone)
    · rw [hr, ← WindowConfig.width_reaches M hreach]
      cases hs : WindowConfig.step M w' with
      | some w'' =>
        exact Or.inr ⟨w'', hreach.tail hs, boundedUpdate_window_step M hs⟩
      | none =>
        by_cases ht : WindowConfig.Terminal M w'
        · exact Or.inr ⟨w', hreach, boundedUpdate_window_halt M w' ht⟩
        · exact Or.inl (boundedUpdate_overflow_headless M w' hs ht)

/-- A finite row contains a head with a genuinely undefined instruction. -/
def HasHaltingHead (M : TM0.Machine Γ Λ) (r : Row Γ Λ) : Prop :=
  ∃ i a q, r i = (a, some q) ∧ M q a = none

omit [Inhabited Γ] in
theorem headless_no_haltingHead (M : TM0.Machine Γ Λ) {r : Row Γ Λ}
    (h : Headless r) : ¬HasHaltingHead M r := by
  rintro ⟨i, a, q, hr, _⟩
  have hc := h i
  rw [hr] at hc
  cases hc

theorem haltingHead_windowRow_iff (M : TM0.Machine Γ Λ) (w : WindowConfig Γ Λ) :
    HasHaltingHead M (windowRow w) ↔ WindowConfig.Terminal M w := by
  constructor
  · rintro ⟨i, a, q, hr, hm⟩
    have hi : i = (w.left.length : ℤ) := by
      by_contra hne
      have h := congrArg Prod.snd hr
      simp [windowRow, row, hne] at h
    subst i
    have h : w.head = a ∧ w.state = q := by
      simpa [windowRow, row, WindowConfig.toCfg] using hr
    simpa only [WindowConfig.Terminal, h.1, h.2] using hm
  · intro h
    exact ⟨w.left.length, w.head, w.state,
      by simp [windowRow, row, WindowConfig.toCfg], h⟩

/-- A bounded machine run is realized by finite cellular iterations. -/
theorem bounded_iterate_of_reaches (M : TM0.Machine Γ Λ) {w w' : WindowConfig Γ Λ}
    (h : StateTransition.Reaches (WindowConfig.step M) w w') :
    ∃ n : ℕ, (boundedUpdate w.width M)^[n] (windowRow w) = windowRow w' := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', hn, ← WindowConfig.width_reaches M hreach]
    exact boundedUpdate_window_step M hstep

/-- Genuine machine halting is exactly detection of a terminal head by a
finite synchronous radius-one system of sufficiently large width. -/
theorem halts_iff_bounded_cellular (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ ∃ k n : ℕ,
      HasHaltingHead M
        ((boundedUpdate (WindowConfig.initial (Λ := Λ) k l).width M)^[n]
          (windowRow (WindowConfig.initial k l))) := by
  rw [WindowConfig.halts_iff_finite_window]
  constructor
  · rintro ⟨k, w, hreach, ht⟩
    obtain ⟨n, hn⟩ := bounded_iterate_of_reaches M hreach
    refine ⟨k, n, ?_⟩
    rw [hn]
    exact (haltingHead_windowRow_iff M w).mpr ht
  · rintro ⟨k, n, hh⟩
    rcases bounded_iterate_cases M (WindowConfig.initial k l) n with hnone | ⟨w, hr, heq⟩
    · exact (headless_no_haltingHead M hnone hh).elim
    · rw [heq] at hh
      exact ⟨k, w, hr, (haltingHead_windowRow_iff M w).mp hh⟩

/-- A finite row has exactly `n` entries of the fixed finite cell alphabet. -/
abbrev FiniteRow (n : ℕ) (Γ Λ : Type*) := Fin n → Cell Γ Λ

/-- Extend a finite row by the headless blank exterior. -/
def extend {n : ℕ} (r : FiniteRow n Γ Λ) : Row Γ Λ :=
  fun i => if h : InBounds n i then r ⟨i.toNat, by obtain ⟨_, _⟩ := h; omega⟩ else blankCell

/-- Restrict an absolute-coordinate row to its finite interval. -/
def restrict (n : ℕ) (r : Row Γ Λ) : FiniteRow n Γ Λ := fun i => r i

omit [Inhabited Λ] in
@[simp] theorem extend_at {n : ℕ} (r : FiniteRow n Γ Λ) (i : Fin n) :
    extend r (i : ℤ) = r i := by
  have hi : InBounds n (i : ℤ) := by
    simp only [InBounds]
    exact ⟨by omega, by exact_mod_cast i.isLt⟩
  simp [extend, hi]

omit [Inhabited Λ] in
theorem extend_restrict {n : ℕ} {r : Row Γ Λ} (h : Supported n r) :
    extend (restrict n r) = r := by
  funext i
  by_cases hi : InBounds n i
  · have hz : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi.1
    simp [extend, restrict, hi, hz]
  · simp [extend, hi, h i hi]

omit [Inhabited Λ] in
theorem extend_supported {n : ℕ} (r : FiniteRow n Γ Λ) : Supported n (extend r) := by
  intro i hi
  simp [extend, hi]

/-- A genuinely finite synchronous rule, whose value at `i` reads only the
three old cells at `i-1`, `i`, and `i+1`, with blank boundary conditions. -/
def finiteUpdate {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) : FiniteRow n Γ Λ :=
  restrict n (update M (extend r))

theorem extend_finiteUpdate {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) :
    extend (finiteUpdate M r) = boundedUpdate n M (extend r) := by
  funext i
  by_cases hi : InBounds n i
  · have hz : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi.1
    simp [extend, finiteUpdate, restrict, boundedUpdate, truncate, hi, hz]
  · simp [extend, boundedUpdate, truncate, hi]

theorem extend_finite_iterate {n : ℕ} (M : TM0.Machine Γ Λ)
    (r : FiniteRow n Γ Λ) (t : ℕ) :
    extend ((finiteUpdate M)^[t] r) = (boundedUpdate n M)^[t] (extend r) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', extend_finiteUpdate, ih]

/-- Terminal-head detection on a finite tuple. -/
def FiniteHaltingHead {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) : Prop :=
  ∃ i : Fin n, ∃ a q, r i = (a, some q) ∧ M q a = none

theorem finiteHaltingHead_iff {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) :
    FiniteHaltingHead M r ↔ HasHaltingHead M (extend r) := by
  constructor
  · rintro ⟨i, a, q, hr, hm⟩
    exact ⟨i, a, q, (extend_at r i).trans hr, hm⟩
  · rintro ⟨i, a, q, hr, hm⟩
    by_cases hi : InBounds n i
    · refine ⟨⟨i.toNat, by obtain ⟨_, _⟩ := hi; omega⟩, a, q, ?_, hm⟩
      simpa [extend, hi] using hr
    · simp [extend, hi, blankCell] at hr

/-- The fully finite form of the halting equivalence, suitable for a finite
alphabet local tableau construction. -/
theorem halts_iff_finite_cellular (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ ∃ k t : ℕ,
      FiniteHaltingHead M
        ((finiteUpdate M)^[t]
          (restrict (WindowConfig.initial (Λ := Λ) k l).width
            (windowRow (WindowConfig.initial k l)))) := by
  rw [halts_iff_bounded_cellular]
  apply exists_congr
  intro k
  apply exists_congr
  intro t
  rw [finiteHaltingHead_iff, extend_finite_iterate,
    extend_restrict (windowRow_supported (WindowConfig.initial k l))]

end Cellular

end TuranUniversality.Computation
