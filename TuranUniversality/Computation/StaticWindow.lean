module

public import TuranUniversality.Computation.StaticInput

/-!
# Exact static-input rows and the reset theorem

This connects the finite local static grammar to actual finite-window machine
initializations.  Both arbitrary padding lengths are allowed.  The final
theorem eliminates an arbitrary frozen-track assumption entirely.
-/

@[expose] public section

namespace TuranUniversality.Computation.StaticInput

open Turing Cellular ResetProtocol

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- An ordinary input window with independently chosen left/right padding. -/
def paddedWindow (k m : ℕ) (a : Γ) (v : List Γ) : WindowConfig Γ Λ :=
  ⟨default, List.replicate k default, a, v ++ List.replicate m default⟩

/-- The concrete frozen finite cell list of that initialization. -/
def frozenCells (k m : ℕ) (a : Γ) (v : List Γ) : List (Cell Γ Λ) :=
  List.replicate k blankCell ++
    (a, some default) :: (v ++ List.replicate m default).map (fun b => (b, none))

theorem frozenCells_length (k m : ℕ) (a : Γ) (v : List Γ) :
    (frozenCells (Λ := Λ) k m a v).length = (paddedWindow (Λ := Λ) k m a v).width := by
  simp [frozenCells, paddedWindow, WindowConfig.width]
  omega

omit [Inhabited Λ] in
theorem getI_replicate_blank (k i : ℕ) :
    (List.replicate k (default : Γ)).getI i = default := by
  simpa only [List.getI_eq_getElem?_getD] using
    List.getElem?_getD_replicate_default_eq (d := (default : Γ)) k i

omit [Inhabited Λ] in
theorem getI_map_plain (v : List Γ) (i : ℕ) :
    (v.map (fun a => (a, (none : Option Λ)))).getI i = (v.getI i, none) :=
  List.getD_map v default (fun a => (a, (none : Option Λ)))

/-- The ordinary tape and the explicit frozen cell list agree at every
nonnegative absolute position, including the blank exterior. -/
theorem paddedWindow_at (k m : ℕ) (a : Γ) (v : List Γ) (i : ℕ) :
    windowRow (paddedWindow (Λ := Λ) k m a v) (i : ℤ) =
      (frozenCells (Λ := Λ) k m a v).getI i := by
  by_cases hik : i < k
  · have hi : (i : ℤ) ≠ (k : ℤ) := by omega
    have hd : (i : ℤ) - k = Int.negSucc (k - i - 1) := by omega
    rw [frozenCells, List.getI_append _ _ i (by simpa using hik)]
    simp only [windowRow, row, paddedWindow, WindowConfig.toCfg, List.length_replicate,
      hi, ite_false, hd, Tape.nth, ListBlank.nth_mk]
    rw [getI_replicate_blank]
    exact (getI_replicate_blank (Γ := Cell Γ Λ) k i).symm
  · have hki : k ≤ i := by omega
    rw [frozenCells, List.getI_append_right _ _ i (by simpa using hki)]
    by_cases hi : i = k
    · subst i
      simp [windowRow, row, paddedWindow, WindowConfig.toCfg]
    · have hi' : (i : ℤ) ≠ (k : ℤ) := by omega
      have hd : (i : ℤ) - k = ((i - k - 1 : ℕ) + 1 : ℕ) := by omega
      have hn : i - k = (i - k - 1) + 1 := by omega
      simp only [List.length_replicate]
      conv_rhs => rw [hn, List.getI_cons_succ, getI_map_plain]
      simp only [windowRow, row, paddedWindow, WindowConfig.toCfg, List.length_replicate,
        hi', ite_false, hd, Tape.nth, ListBlank.nth_mk]

/-- View a literal cell list as a finite tuple. -/
def asFinite (l : List (Cell Γ Λ)) : FiniteRow l.length Γ Λ := fun i => l[i]

omit [Inhabited Λ] in
theorem extend_asFinite_nonneg (l : List (Cell Γ Λ)) (i : ℤ) (hi : 0 ≤ i) :
    extend (asFinite l) i = l.getI i.toNat := by
  by_cases hb : InBounds l.length i
  · have hlt : i.toNat < l.length := by obtain ⟨_, _⟩ := hb; omega
    simp only [extend, hb, dite_true, asFinite, List.getI_eq_getElem _ hlt, Fin.getElem_fin]
  · have hle : l.length ≤ i.toNat := by simp only [InBounds] at hb; omega
    simp only [extend, hb, dite_false, List.getI_eq_default _ hle]
    rfl

/-- The explicit finite static cell list is exactly the tape-window row. -/
theorem extend_frozenCells (k m : ℕ) (a : Γ) (v : List Γ) :
    extend (asFinite (frozenCells (Λ := Λ) k m a v)) =
      windowRow (paddedWindow (Λ := Λ) k m a v) := by
  funext i
  by_cases hi : 0 ≤ i
  · rw [extend_asFinite_nonneg _ i hi]
    have heq : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi
    simpa only [heq] using (paddedWindow_at (Λ := Λ) k m a v i.toNat).symm
  · have hb : ¬InBounds (frozenCells (Λ := Λ) k m a v).length i := by
      simp only [InBounds]; omega
    have hw : ¬InBounds (paddedWindow (Λ := Λ) k m a v).width i := by
      simp only [InBounds]; omega
    rw [windowRow_outside _ i hw]
    simp [extend, hb]

/-- Padding changes no actual infinite-tape initialization. -/
theorem paddedWindow_toCfg (k m : ℕ) (a : Γ) (v : List Γ) :
    (paddedWindow (Λ := Λ) k m a v).toCfg = TM0.init (a :: v) := by
  have hleft : ListBlank.mk (List.replicate k (default : Γ)) = ListBlank.mk [] := by
    simpa using WindowConfig.listBlank_append_padding ([] : List Γ) k
  simp [paddedWindow, WindowConfig.toCfg, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk',
    hleft, WindowConfig.listBlank_append_padding]

/-- A reset return whose frozen row is an ordinary window witnesses a genuine
halting run from that window; boundary disappearance cannot cause this. -/
theorem returns_window_sound {n : ℕ} (M : TM0.Machine Γ Λ)
    (r : FiniteRow n Γ Λ) (w : WindowConfig Γ Λ) (hw : w.width = n)
    (hext : extend r = windowRow w) (hr : Returns M r) :
    (StateTransition.eval (TM0.step M) w.toCfg).Dom := by
  have hn : 0 < n := hw ▸ w.width_pos
  obtain ⟨t, ht⟩ := returns_sound M r hn hr
  have hh := (finiteHaltingHead_iff M _).mp ht
  rw [extend_finite_iterate, hext, ← hw] at hh
  rcases bounded_iterate_cases M w t with hnone | ⟨z, hz, heq⟩
  · exact (headless_no_haltingHead M hnone hh).elim
  · rw [heq] at hh
    have ht := (haltingHead_windowRow_iff M z).mp hh
    apply Part.dom_iff_mem.mpr
    exact ⟨z.toCfg, StateTransition.mem_eval.mpr
      ⟨WindowConfig.reaches_sound M hz, (WindowConfig.terminal_iff_step_none M z).mp ht⟩⟩

/-- Every actual finite halting window run yields a locally certified return
for its precise finite frozen row. -/
theorem returns_of_window_run {n : ℕ} (M : TM0.Machine Γ Λ)
    (r : FiniteRow n Γ Λ) (w z : WindowConfig Γ Λ) (hw : w.width = n)
    (hext : extend r = windowRow w)
    (hr : StateTransition.Reaches (WindowConfig.step M) w z)
    (ht : WindowConfig.Terminal M z) : Returns M r := by
  obtain ⟨t, hiter⟩ := bounded_iterate_of_reaches M hr
  have hext' : extend ((finiteUpdate M)^[t] r) = windowRow z := by
    rw [extend_finite_iterate, hext, ← hw]
    exact hiter
  apply returns_of_unique_halting M r (hw ▸ w.width_pos) t
  exact uniqueHaltingHead_of_window M z ((WindowConfig.width_reaches M hr).trans hw) hext' ht

/-- Soundness includes the actual static input constraints, not a freely
chosen immutable initial configuration. -/
theorem valid_return_halts (M : TM0.Machine Γ Λ) (l : List Γ)
    (s : List (Symbol Γ)) (hv : Valid l s)
    (hr : Returns M (asFinite (s.map (frozen (Λ := Λ))))) : (TM0.eval M l).Dom := by
  obtain ⟨k, c, a, v, hl, hs⟩ := frozen_valid (Λ := Λ) hv
  have hcells : s.map (frozen (Λ := Λ)) = frozenCells (Λ := Λ) k (c + 1) a v := by
    simpa [frozenCells, List.map_append, List.map_map, Function.comp_def, blankCell] using hs
  rw [hcells] at hr
  have hh := returns_window_sound M _ (paddedWindow (Λ := Λ) k (c + 1) a v)
    (frozenCells_length k (c + 1) a v).symm (extend_frozenCells k (c + 1) a v) hr
  rw [paddedWindow_toCfg, ← hl] at hh
  exact hh

/-- Exact local static-input and dynamic-reset equivalence for every nonempty
ordinary tape input.  No arbitrary frozen-track premise remains. -/
theorem halts_iff_valid_return (M : TM0.Machine Γ Λ) (l : List Γ) (hl : l ≠ []) :
    (TM0.eval M l).Dom ↔ ∃ s : List (Symbol Γ), Valid l s ∧
      Returns M (asFinite (s.map (frozen (Λ := Λ)))) := by
  constructor
  · intro h
    cases l with
    | nil => exact (hl rfl).elim
    | cons a v =>
      change (StateTransition.eval (TM0.step M) (TM0.init (a :: v))).Dom at h
      obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp h
      obtain ⟨k, hk⟩ := WindowConfig.eval_lifts M hz
      have hb : WindowConfig.Buffered k (WindowConfig.initial (Λ := Λ) (k + 1) (a :: v)) := by
        have hh := WindowConfig.initial_buffered (Λ := Λ) (k + 1) (a :: v)
        simp only [WindowConfig.Buffered] at hh ⊢
        omega
      obtain ⟨z', hreach, ht⟩ := hk (WindowConfig.initial (k + 1) (a :: v))
        (WindowConfig.initial_toCfg _ _) hb
      let s : List (Symbol Γ) := List.replicate (k + 1) .before ++ inputWord (a :: v) ++
        .finish :: List.replicate k .after
      have hv : Valid (a :: v) s := (valid_iff _ _).mpr
        ⟨k + 1, k, List.cons_ne_nil _ _, rfl⟩
      refine ⟨s, hv, ?_⟩
      have hs : s.map (frozen (Λ := Λ)) = frozenCells (Λ := Λ) (k + 1) (k + 1) a v := by
        simp [s, frozenCells, inputWord, frozen, List.map_map, Function.comp_def,
          List.replicate_succ, blankCell]
      rw [hs]
      exact returns_of_window_run M _ (paddedWindow (Λ := Λ) (k + 1) (k + 1) a v) z'
        (frozenCells_length (k + 1) (k + 1) a v).symm
        (extend_frozenCells (k + 1) (k + 1) a v) hreach ht
  · rintro ⟨s, hv, hr⟩
    exact valid_return_halts M l s hv hr

end TuranUniversality.Computation.StaticInput
