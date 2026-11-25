module

public import TuranUniversality.Computation.StaticWindow

/-! # Finite tuple forms of the exact static input and return theorem -/

@[expose] public section

namespace TuranUniversality.Computation.StaticInput

open Turing Cellular ResetProtocol

variable {Γ Λ : Type*}

/-- The recursive checker is exactly the conjunction of the bounded prefix
checks at every Start position. -/
theorem prefixCheck_positions (w : List Γ) (s : List (Symbol Γ)) :
    PrefixCheck w s ↔ ∀ i a, s[i]? = some (.start a) →
      inputWord w ++ [.finish] <+: s.drop i := by
  induction s with
  | nil => simp [PrefixCheck]
  | cons b s ih =>
    have htail :
        (∀ i a, s[i]? = some (.start a) → inputWord w ++ [.finish] <+: s.drop i) ↔
        (∀ i a, (b :: s)[i + 1]? = some (.start a) →
          inputWord w ++ [.finish] <+: (b :: s).drop (i + 1)) := by simp
    constructor
    · intro h i a hi
      cases i with
      | zero =>
        have hb : b = .start a := by simpa using hi
        subst b
        exact h.1
      | succ i =>
        have hs : PrefixCheck w s := by cases b <;> simp only [PrefixCheck] at h <;> tauto
        exact htail.mp (ih.mp hs) i a hi
    · intro h
      have hs : PrefixCheck w s := ih.mpr (htail.mpr (fun i a hi => h (i + 1) a hi))
      cases b with
      | start a => exact ⟨h 0 a rfl, hs⟩
      | before => exact hs
      | input a => exact hs
      | finish => exact hs
      | after => exact hs

variable [Inhabited Γ] [Inhabited Λ]

def castFiniteRow {m n : ℕ} (h : m = n) (r : FiniteRow m Γ Λ) : FiniteRow n Γ Λ :=
  fun i => r (Fin.cast h.symm i)

theorem returns_cast {m n : ℕ} (M : TM0.Machine Γ Λ) (h : m = n) (r : FiniteRow m Γ Λ) :
    Returns M (castFiniteRow h r) ↔ Returns M r := by
  subst n
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem returns_asFinite_ofFn {n : ℕ} (M : TM0.Machine Γ Λ) (r : FiniteRow n Γ Λ) :
    Returns M (asFinite (List.ofFn r)) ↔ Returns M r := by
  have heq : asFinite (List.ofFn r) = castFiniteRow (List.length_ofFn (f := r)).symm r := by
    funext i
    simp only [asFinite, castFiniteRow, Fin.getElem_fin, List.getElem_ofFn]
    exact congrArg r (Fin.ext rfl)
  rw [heq]
  exact returns_cast M _ r

/-- The fully local static-input soundness theorem in finite-array form. -/
theorem finite_valid_return_halts {n : ℕ} (M : TM0.Machine Γ Λ) (input : List Γ)
    (s : Fin n → Symbol Γ) (hv : Valid input (List.ofFn s))
    (hr : Returns M (fun i => frozen (Λ := Λ) (s i))) : (TM0.eval M input).Dom := by
  apply valid_return_halts M input (List.ofFn s) hv
  rw [List.map_ofFn]
  exact (returns_asFinite_ofFn M _).mpr hr

/-- Every genuine halt gives a nonempty finite tuple satisfying the exact
static input constraints and admitting a positive reset return. -/
theorem exists_finite_valid_return (M : TM0.Machine Γ Λ) (input : List Γ)
    (hi : input ≠ []) (hh : (TM0.eval M input).Dom) :
    ∃ (m : ℕ) (s : Fin (m + 1) → Symbol Γ), Valid input (List.ofFn s) ∧
      Returns M (fun i => frozen (Λ := Λ) (s i)) := by
  suffices ∃ (n : ℕ), 0 < n ∧ ∃ s : Fin n → Symbol Γ,
      Valid input (List.ofFn s) ∧ Returns M (fun i => frozen (Λ := Λ) (s i)) by
    obtain ⟨n, hn, s, hv, hr⟩ := this
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact ⟨m, s, hv, hr⟩
  obtain ⟨s, hv, hr⟩ := (halts_iff_valid_return M input hi).mp hh
  have hs : s ≠ [] := by intro he; subst s; exact hv.1
  have hlen : 0 < s.length := List.length_pos_iff.mpr hs
  let f : Fin s.length → Symbol Γ := s.get
  have hf : List.ofFn f = s := List.ofFn_get s
  have hv' : Valid input (List.ofFn f) := by simpa only [hf] using hv
  have hr' : Returns M (fun i => frozen (Λ := Λ) (f i)) := by
    apply (returns_asFinite_ofFn M _).mp
    change Returns M (asFinite (List.ofFn (frozen (Λ := Λ) ∘ f)))
    rw [← List.map_ofFn, hf]
    exact hr
  exact ⟨s.length, hlen, f, hv', hr'⟩

end TuranUniversality.Computation.StaticInput
