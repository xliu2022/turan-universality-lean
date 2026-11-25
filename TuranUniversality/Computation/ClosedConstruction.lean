module

public import TuranUniversality.Computation.FramePrefix
public import TuranUniversality.Computation.PermutationTableau

/-!
# A genuine halting computation gives a finite closed marked local model

The carrier is an explicit product of two positive finite cycles.  Its rows
are the actual reset history, framed by persistent walls and the certified
static input word.  The horizontal seam joins a right wall to a left wall;
the temporal seam is the last genuine step of the positive reset return.
-/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem

open Turing Cellular ResetProtocol

def horizontalPerm (T W : ℕ) : Equiv.Perm (Fin T × Fin W) :=
  Equiv.prodCongr (Equiv.refl _) (finRotate W)

def verticalPerm (T W : ℕ) : Equiv.Perm (Fin T × Fin W) :=
  Equiv.prodCongr (finRotate T) (Equiv.refl _)

@[simp] theorem horizontalPerm_apply (T W : ℕ) (x : Fin T × Fin W) :
    horizontalPerm T W x = (x.1, finRotate W x.2) := rfl

@[simp] theorem verticalPerm_apply (T W : ℕ) (x : Fin T × Fin W) :
    verticalPerm T W x = (finRotate T x.1, x.2) := rfl

@[simp] theorem horizontalPerm_symm_apply (T W : ℕ) (x : Fin T × Fin W) :
    (horizontalPerm T W).symm x = (x.1, (finRotate W).symm x.2) := rfl

theorem horizontalPerm_iterate (T W : ℕ) (x : Fin T × Fin W) (j : ℕ) :
    (horizontalPerm T W)^[j] x = (x.1, (finRotate W)^[j] x.2) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, horizontalPerm_apply]

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- The actual finite product model associated to a cyclic reset history. -/
def torusModel {p m : ℕ} (M : TM0.Machine Γ Λ) (input : List Γ)
    (s : Fin (m + 1) → StaticInput.Symbol Γ)
    (hv : StaticInput.Valid input (List.ofFn s))
    (rows : Fin (p + 1) → Segment (m + 1) Γ Λ)
    (hrows : ∀ t, Step M (fun i => StaticInput.frozen (s i))
      (rows t) (rows (finRotate (p + 1) t))) :
    PermutationModel M input (Fin (p + 1) × Fin (m + 3)) where
  H := horizontalPerm _ _
  V := verticalPerm _ _
  label := fun x => framedLabel s (rows x.1) x.2
  commute := fun _ => rfl
  horizontal := fun x => (frameOfRows M s (rows x.1) hv.1 (hrows x.1).1).horizontal_cyclic x.2
  evolution := fun x => frameOfRows_evolution M s _ _ hv.1 (hrows x.1) x.2
  input_rule := by
    intro x hx j hj
    rw [horizontalPerm_iterate]
    exact framedLabel_prefix input s (rows x.1) hv x.2 hx j hj

theorem torusModel_marked {p m : ℕ} (M : TM0.Machine Γ Λ) (input : List Γ)
    (s : Fin (m + 1) → StaticInput.Symbol Γ)
    (hv : StaticInput.Valid input (List.ofFn s))
    (rows : Fin (p + 1) → Segment (m + 1) Γ Λ)
    (hrows : ∀ t, Step M (fun i => StaticInput.frozen (s i))
      (rows t) (rows (finRotate (p + 1) t)))
    (h0 : rows 0 = initialRow (m + 1)) :
    (torusModel M input s hv rows hrows).MarkedAt (0, centerIndex 0) := by
  change framedLabel s (rows 0) ((finRotate (m + 3)).symm (centerIndex 0)) = .leftWall ∧
    IsInitial (framedLabel s (rows 0) (centerIndex 0))
  rw [rotate_symm_center, framedLabel_center, h0]
  exact ⟨framedLabel_zero s _, rfl⟩

/-- The constructive closed-model direction: ordinary halting supplies the
finite carrier, its commuting permutations, all actual local checks, and a
marked initial cell. -/
theorem exists_marked_permutationModel (M : TM0.Machine Γ Λ) (input : List Γ)
    (hi : input ≠ []) (hh : (TM0.eval M input).Dom) :
    ∃ (p m : ℕ) (P : PermutationModel M input (Fin (p + 1) × Fin (m + 3)))
      (x : Fin (p + 1) × Fin (m + 3)), P.MarkedAt x := by
  obtain ⟨m, s, hv, hr⟩ := StaticInput.exists_finite_valid_return M input hi hh
  obtain ⟨T, hT, rows, h0, hrows⟩ := finite_cycle_of_return hr
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  exact ⟨p, m, torusModel M input s hv rows hrows, (0, centerIndex 0),
    torusModel_marked M input s hv rows hrows h0⟩

end TuranUniversality.Computation.LocalSystem
