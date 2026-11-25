module

public import TuranUniversality.Construction.Parameters
public import TuranUniversality.Weighted.Incidence

@[expose] public section

/-! # A concrete compiler signature with all parameter inequalities proved -/

namespace TuranUniversality.Construction

open Weighted
open scoped BigOperators

instance codeCount_neZero (A : ℕ) : NeZero (codeCount A) := ⟨Nat.ne_of_gt (codeCount_pos A)⟩

def copyCount (A : ℕ) : ℕ := 2048 * (Nat.sqrt (rootNumber (chosenParameter A)) + 1)

theorem copyCount_pos (A : ℕ) : 0 < copyCount A := by unfold copyCount; positivity

theorem rootSqrt_large (A : ℕ) : 100000 ≤ Real.sqrt (rootNumber (chosenParameter A)) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  have hroot : 4 * (physicalCount (chosenParameter A) : ℝ) ≤ rootNumber (chosenParameter A) := by
    exact_mod_cast rootNumber_large (chosenParameter A)
  have hm : (10000000000000000 : ℝ) ≤ physicalCount (chosenParameter A) := by
    unfold physicalCount chosenParameter
    push_cast
    linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  nlinarith

theorem copyCount_bounds (A : ℕ) :
    2048 * Real.sqrt (rootNumber (chosenParameter A)) ≤ (copyCount A : ℝ) ∧
      (copyCount A : ℝ) ≤ 2049 * Real.sqrt (rootNumber (chosenParameter A)) := by
  have hlo := Real.real_sqrt_le_nat_sqrt_succ (a := rootNumber (chosenParameter A))
  have hhi := Real.nat_sqrt_le_real_sqrt (a := rootNumber (chosenParameter A))
  have hlarge := rootSqrt_large A
  unfold copyCount
  push_cast
  constructor <;> linarith

theorem copies_fit (A : ℕ) : 3 * copyCount A ≤ rootNumber (chosenParameter A) := by
  have hL := (copyCount_bounds A).2
  have hu := rootSqrt_large A
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ rootNumber (chosenParameter A) from Nat.cast_nonneg _)
  have hmul := mul_nonneg (show 0 ≤ Real.sqrt (rootNumber (chosenParameter A)) by positivity)
    (show 0 ≤ Real.sqrt (rootNumber (chosenParameter A)) - 6147 by linarith)
  have h : 3 * (copyCount A : ℝ) ≤ rootNumber (chosenParameter A) := by nlinarith
  exact_mod_cast h

abbrev RootLabels (A : ℕ) := BlockRoots (chosenBlocks A).half
abbrev PhysicalKinds (A : ℕ) := Fin (physicalCount (chosenParameter A) - 2) ⊕ Bool
abbrev LabelCodes (Alphabet : Type*) [Fintype Alphabet] :=
  Fin (physicalCount (chosenParameter (Fintype.card Alphabet)) - 2) ⊕ (Unit ⊕ Alphabet)

theorem rootLabels_card (A : ℕ) : Fintype.card (RootLabels A) = rootNumber (chosenParameter A) :=
  (chosenBlocks A).roots_card

theorem physicalKinds_card (A : ℕ) : Fintype.card (PhysicalKinds A) =
    physicalCount (chosenParameter A) := by
  have hm := physicalCount_ge (chosenParameter A)
  simp only [PhysicalKinds, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
  omega

theorem labelCodes_card (Alphabet : Type*) [Fintype Alphabet] :
    Fintype.card (LabelCodes Alphabet) = codeCount (Fintype.card Alphabet) := by
  have hm := physicalCount_ge (chosenParameter (Fintype.card Alphabet))
  simp only [LabelCodes, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique, codeCount]
  omega

noncomputable def labelCodeEquiv (Alphabet : Type*) [Fintype Alphabet] :
    LabelCodes Alphabet ≃ Fin (codeCount (Fintype.card Alphabet)) :=
  Fintype.equivOfCardEq (by rw [labelCodes_card, Fintype.card_fin])

def physicalLabel {Alphabet : Type*} [Fintype Alphabet] :
    LabelCodes Alphabet → PhysicalKinds (Fintype.card Alphabet)
  | .inl k => .inl k
  | .inr (.inl _) => .inr false
  | .inr (.inr _) => .inr true

def colorLabel {Alphabet : Type*} [Fintype Alphabet] (background : Alphabet) :
    LabelCodes Alphabet → Alphabet
  | .inr (.inr a) => a
  | _ => background

def backgroundCode {Alphabet : Type*} [Fintype Alphabet] (background : Alphabet) :
    PhysicalKinds (Fintype.card Alphabet) → LabelCodes Alphabet
  | .inl k => .inl k
  | .inr false => .inr (.inl ())
  | .inr true => .inr (.inr background)

@[simp] theorem physicalLabel_backgroundCode {Alphabet : Type*} [Fintype Alphabet]
    (background : Alphabet) (k : PhysicalKinds (Fintype.card Alphabet)) :
    physicalLabel (backgroundCode background k) = k := by
  cases k with
  | inl k => rfl
  | inr b => cases b <;> rfl

noncomputable def compilerSignature (Alphabet : Type*) [Fintype Alphabet] :
    CompilerSignature (RootLabels (Fintype.card Alphabet)) (LabelCodes Alphabet)
      (PhysicalKinds (Fintype.card Alphabet)) (copyCount (Fintype.card Alphabet)) where
  codes :=
    { missing := fun c => ((chosenBlocks (Fintype.card Alphabet)).codes.missing (labelCodeEquiv Alphabet c))
      disjoint := fun c d hcd => (chosenBlocks (Fintype.card Alphabet)).codes.disjoint _ _
        (fun h => hcd ((labelCodeEquiv Alphabet).injective h)) }
  physical := physicalLabel
  cellKind := .inr false
  colorKind := .inr true
  kinds_ne := by simp
  copyRoot := Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, rootLabels_card]
    exact copies_fit (Fintype.card Alphabet)))

theorem compilerSignature_pair_inside (Alphabet : Type*) [Fintype Alphabet]
    (c : LabelCodes Alphabet) (p : Finset (RootLabels (Fintype.card Alphabet)))
    (hp : p ∈ ((compilerSignature Alphabet).codes.missing c).pairs)
    {x y : RootLabels (Fintype.card Alphabet)} (hx : x ∈ p) (hy : y ∈ p) :
    blockLabel (chosenBlocks (Fintype.card Alphabet)).half x =
      blockLabel (chosenBlocks (Fintype.card Alphabet)).half y :=
  (chosenBlocks (Fintype.card Alphabet)).pair_inside _ p hp hx hy

end TuranUniversality.Construction
