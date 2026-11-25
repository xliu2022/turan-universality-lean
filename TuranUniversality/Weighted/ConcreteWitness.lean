module

public import TuranUniversality.Weighted.ThreeCopies
public import TuranUniversality.Weighted.Nonhalting
public import TuranUniversality.Construction.Signature
public import TuranUniversality.Computation.ClosedConstruction

/-! # Concrete legal baseline and halting witnesses for the fixed signature -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace TuranUniversality.Weighted.ConcreteWitness

open scoped BigOperators
open Turing
open TuranUniversality.Computation
open TuranUniversality.Computation.MatchingSystem
open TuranUniversality.Construction

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
  [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

abbrev Alphabet := LocalSystem.Label Γ Λ
abbrev alphabetCard := Fintype.card (Alphabet (Γ := Γ) (Λ := Λ))
noncomputable abbrev Signature := compilerSignature (Alphabet (Γ := Γ) (Λ := Λ))
abbrev Roots := RootLabels (alphabetCard (Γ := Γ) (Λ := Λ))
abbrev Kinds := PhysicalKinds (alphabetCard (Γ := Γ) (Λ := Λ))

def color : LabelCodes (Alphabet (Γ := Γ) (Λ := Λ)) → Alphabet (Γ := Γ) (Λ := Λ) :=
  colorLabel LocalSystem.background

omit [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ] in
theorem roots_pos : 0 < Fintype.card (Roots (Γ := Γ) (Λ := Λ)) := by
  rw [rootLabels_card]
  have h := rootNumber_large (chosenParameter (alphabetCard (Γ := Γ) (Λ := Λ)))
  have hm := physicalCount_ge (chosenParameter (alphabetCard (Γ := Γ) (Λ := Λ)))
  omega

omit [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ] in
theorem kinds_large : 30 ≤ Fintype.card (Kinds (Γ := Γ) (Λ := Λ)) := by
  rw [physicalKinds_card]
  exact physicalCount_ge _

omit [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ] in
theorem kinds_at_least_three : 3 ≤ Fintype.card (Kinds (Γ := Γ) (Λ := Λ)) :=
  le_trans (by norm_num) kinds_large

/-- The fixed, fully instantiated signature gives the actual rational
weighted threshold for every nonhalting legal rooted model. -/
theorem nonhalting_bound {Data : Type*} [DecidableEq Data] [Fintype Data]
    (M : TM0.Machine Γ Λ) (input : List Γ)
    (G : RootedModel (Roots (Γ := Γ) (Λ := Λ)) Data)
    (hlegal : RootedLegal Signature G color (LocalSystem.specification M input))
    (hn : ¬ (TM0.eval M input).Dom) (z : Roots (Γ := Γ) (Λ := Λ) → ℝ) (x : Data → ℝ)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1) :
    6 * G.toRGraph.edgePolynomial (Sum.elim z x) ≤
      (threshold (alphabetCard (Γ := Γ) (Λ := Λ)) : ℝ) := by
  let A := alphabetCard (Γ := Γ) (Λ := Λ)
  have hq : (Fintype.card (Roots (Γ := Γ) (Λ := Λ)) : ℝ) =
      rootCount (Fintype.card (Kinds (Γ := Γ) (Λ := Λ)) : ℝ) := by
    rw [rootLabels_card, physicalKinds_card, rootNumber_cast]
  have hqu : (Fintype.card (Roots (Γ := Γ) (Λ := Λ)) : ℝ) =
      (Real.sqrt (rootNumber (chosenParameter A))) ^ 2 := by
    rw [rootLabels_card]
    exact (Real.sq_sqrt (Nat.cast_nonneg _)).symm
  have h := Signature.nonhalting_edgePolynomial_le_baseline G color M input hlegal hn z x
    (Real.sqrt (rootNumber (chosenParameter A))) kinds_large (rootSqrt_large A) hq hqu
    (copyCount_bounds A).1 (copyCount_bounds A).2 hz hx hnorm
  rw [physicalKinds_card, rootLabels_card] at h
  rw [threshold_cast]
  linarith

def backgroundPermutationModel (M : TM0.Machine Γ Λ) (input : List Γ) :
    LocalSystem.PermutationModel M input Unit where
  H := Equiv.refl Unit
  V := Equiv.refl Unit
  label _ := LocalSystem.background
  commute := fun _ => rfl
  horizontal := fun _ => LocalSystem.background_horizontal M
  evolution := fun _ => LocalSystem.background_evolution M
  input_rule := by
    intro x hx
    exact False.elim hx

def backgroundSeed : PermutationSeed (Signature (Γ := Γ) (Λ := Λ)) Unit where
  code d := backgroundCode (LocalSystem.background (Γ := Γ) (Λ := Λ)) d.1
  physical_code := fun d => physicalLabel_backgroundCode _ d.1
  H := Equiv.refl Unit
  V := Equiv.refl Unit
  markers := ∅
  marker_uniform := by simp
  one_marker := by simp
  marker_cell := by simp

noncomputable def baselineCompletion : Completion (Signature (Γ := Γ) (Λ := Λ))
    (Kinds (Γ := Γ) (Λ := Λ) × Unit) := backgroundSeed.completion

theorem baselineCompletion_legal (M : TM0.Machine Γ Λ) (input : List Γ) :
    RootedLegal Signature baselineCompletion.model color (LocalSystem.specification M input) := by
  apply backgroundSeed.rootedLegal_of_permutationModel color roots_pos (copyCount_pos _)
    M input (backgroundPermutationModel M input) rfl rfl
  · intro i
    rfl
  · intro p hp
    exact False.elim (Finset.notMem_empty p hp)

theorem baselineCompletion_declared (d : Kinds (Γ := Γ) (Λ := Λ) × Unit) :
    ∃ c, Signature.codes.Declared baselineCompletion.model d c :=
  ⟨baselineCompletion.code d, baselineCompletion.model_declared roots_pos d⟩

omit [Inhabited Λ] in
theorem baselineCompletion_balanced (k : Kinds (Γ := Γ) (Λ := Λ)) :
    (baselineCompletion.partition.block k).card = 1 := by
  simpa only [baselineCompletion, Fintype.card_unique] using (backgroundSeed (Γ := Γ) (Λ := Λ)).completion_balanced k

omit [Inhabited Λ] in
theorem baselineCompletion_full (e : Fin 3) :
    (baselineCompletion (Γ := Γ) (Λ := Λ)).matching e |>.Full := backgroundSeed.completion_full e

def baselineSizes : Roots (Γ := Γ) (Λ := Λ) ⊕ (Kinds (Γ := Γ) (Λ := Λ) × Unit) → ℕ :=
  Completion.cloneSizes (Kinds := Kinds (Γ := Γ) (Λ := Λ)) 1

theorem baselineSizes_pos : 0 < ∑ v, baselineSizes (Γ := Γ) (Λ := Λ) v :=
  baselineCompletion.cloneSizes_total_pos 1 baselineCompletion_balanced roots_pos (kinds_at_least_three (Γ := Γ) (Λ := Λ)) (by omega)

theorem baselineCompletion_value :
    6 * (baselineCompletion (Γ := Γ) (Λ := Λ)).model.toRGraph.edgePolynomial
      (fun v => (baselineSizes v : ℝ) / ((∑ w, baselineSizes (Γ := Γ) (Λ := Λ) w : ℕ) : ℝ)) =
      (threshold (alphabetCard (Γ := Γ) (Λ := Λ)) : ℝ) := by
  have hv := (baselineCompletion (Γ := Γ) (Λ := Λ)).balanced_integer_value 1
    baselineCompletion_balanced baselineCompletion_full roots_pos (kinds_at_least_three (Γ := Γ) (Λ := Λ)) (by omega)
  change (baselineCompletion (Γ := Γ) (Λ := Λ)).model.toRGraph.edgePolynomial
    (fun v => (baselineSizes v : ℝ) / ((∑ w, baselineSizes (Γ := Γ) (Λ := Λ) w : ℕ) : ℝ)) = _ at hv
  have hmarkers : (baselineCompletion (Γ := Γ) (Λ := Λ)).markers = ∅ := rfl
  rw [hmarkers, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero] at hv
  calc
    _ = 6 * baselineMax (Fintype.card (Kinds (Γ := Γ) (Λ := Λ)))
        (Fintype.card (Roots (Γ := Γ) (Λ := Λ))) := congrArg (fun x : ℝ => 6 * x) hv
    _ = _ := by rw [threshold_cast, physicalKinds_card, rootLabels_card]

variable {X : Type*} [DecidableEq X] [Fintype X]
  {M : TM0.Machine Γ Λ} {input : List Γ}

def markedSeed (P : LocalSystem.PermutationModel M input X) (a : X) :
    PermutationSeed (Signature (Γ := Γ) (Λ := Λ)) (Fin 3 × X) where
  code d := backgroundCode (P.threeCopies.label d.2) d.1
  physical_code := fun d => physicalLabel_backgroundCode _ d.1
  H := P.threeCopies.H
  V := P.threeCopies.V
  markers := {tripleMarker Signature.cellKind a}
  marker_uniform := by
    intro p hp
    have hp' := Finset.mem_singleton.mp hp
    rw [hp']
    exact tripleMarker_card _ _
  one_marker := by simp
  marker_cell := by
    intro p hp d hd
    have hp' := Finset.mem_singleton.mp hp
    rw [hp'] at hd
    exact tripleMarker_first _ _ d hd

noncomputable def markedCompletion (P : LocalSystem.PermutationModel M input X) (a : X) :
    Completion (Signature (Γ := Γ) (Λ := Λ)) (Kinds (Γ := Γ) (Λ := Λ) × (Fin 3 × X)) :=
  (markedSeed P a).completion

theorem markedCompletion_legal (P : LocalSystem.PermutationModel M input X) (a : X) (ha : P.MarkedAt a) :
    RootedLegal Signature (markedCompletion P a).model color (LocalSystem.specification M input) := by
  apply (markedSeed P a).rootedLegal_of_permutationModel color roots_pos (copyCount_pos _)
    M input P.threeCopies rfl rfl
  · intro i
    rfl
  · intro p hp d hd
    change p ∈ ({tripleMarker Signature.cellKind a} : Finset (Finset (Kinds × (Fin 3 × X)))) at hp
    have hp' := Finset.mem_singleton.mp hp
    rw [hp'] at hd
    change P.MarkedAt d.2.2
    rw [tripleMarker_index _ _ d hd]
    exact ha

theorem markedCompletion_declared (P : LocalSystem.PermutationModel M input X) (a : X)
    (d : Kinds (Γ := Γ) (Λ := Λ) × (Fin 3 × X)) :
    ∃ c, Signature.codes.Declared (markedCompletion P a).model d c :=
  ⟨(markedCompletion P a).code d, (markedCompletion P a).model_declared roots_pos d⟩

theorem markedCompletion_balanced (P : LocalSystem.PermutationModel M input X) (a : X)
    (k : Kinds (Γ := Γ) (Λ := Λ)) :
    ((markedCompletion P a).partition.block k).card = Fintype.card (Fin 3 × X) :=
  (markedSeed P a).completion_balanced k

theorem markedCompletion_full (P : LocalSystem.PermutationModel M input X) (a : X) (e : Fin 3) :
    ((markedCompletion P a).matching e).Full := (markedSeed P a).completion_full e

def markedSizes : Roots (Γ := Γ) (Λ := Λ) ⊕ (Kinds (Γ := Γ) (Λ := Λ) × (Fin 3 × X)) → ℕ :=
  Completion.cloneSizes (Kinds := Kinds (Γ := Γ) (Λ := Λ)) (Fintype.card (Fin 3 × X))

theorem markedSizes_pos (P : LocalSystem.PermutationModel M input X) (a : X) :
    0 < ∑ v, markedSizes (Γ := Γ) (Λ := Λ) (X := X) v := by
  have hN : 0 < Fintype.card (Fin 3 × X) := Fintype.card_pos_iff.mpr ⟨(0, a)⟩
  exact (markedCompletion P a).cloneSizes_total_pos _ (markedCompletion_balanced P a) roots_pos
    (kinds_at_least_three (Γ := Γ) (Λ := Λ)) hN

theorem markedCompletion_strict (P : LocalSystem.PermutationModel M input X) (a : X) :
    (threshold (alphabetCard (Γ := Γ) (Λ := Λ)) : ℝ) <
      6 * (markedCompletion P a).model.toRGraph.edgePolynomial
        (fun v => (markedSizes v : ℝ) / ((∑ w, markedSizes (Γ := Γ) (Λ := Λ) (X := X) w : ℕ) : ℝ)) := by
  have hN : 0 < Fintype.card (Fin 3 × X) := Fintype.card_pos_iff.mpr ⟨(0, a)⟩
  have hmarker : 0 < (markedCompletion P a).markers.card := by
    change 0 < ({tripleMarker Signature.cellKind a} : Finset (Finset (Kinds × (Fin 3 × X)))).card
    simp
  have hv := (markedCompletion P a).balanced_integer_strict _ (markedCompletion_balanced P a)
    (markedCompletion_full P a) roots_pos (kinds_at_least_three (Γ := Γ) (Λ := Λ)) hN hmarker
  change baselineMax (Fintype.card (Kinds (Γ := Γ) (Λ := Λ))) (Fintype.card (Roots (Γ := Γ) (Λ := Λ))) <
    (markedCompletion P a).model.toRGraph.edgePolynomial
      (fun v => (markedSizes v : ℝ) / ((∑ w, markedSizes (Γ := Γ) (Λ := Λ) (X := X) w : ℕ) : ℝ)) at hv
  rw [physicalKinds_card, rootLabels_card] at hv
  rw [threshold_cast]
  linarith

/-- Ordinary halting produces a specific finite legal rooted graph and
natural clone sizes with value strictly above the fixed rational threshold. -/
theorem halting_witness (M : TM0.Machine Γ Λ) (input : List Γ) (hi : input ≠ [])
    (hh : (TM0.eval M input).Dom) :
    ∃ (p m : ℕ) (G : RootedModel (Roots (Γ := Γ) (Λ := Λ))
        (Kinds (Γ := Γ) (Λ := Λ) × (Fin 3 × (Fin (p + 1) × Fin (m + 3)))))
      (sizes : Roots (Γ := Γ) (Λ := Λ) ⊕
        (Kinds (Γ := Γ) (Λ := Λ) × (Fin 3 × (Fin (p + 1) × Fin (m + 3)))) → ℕ),
      (∀ d, ∃ c, Signature.codes.Declared G d c) ∧
      RootedLegal Signature G color (LocalSystem.specification M input) ∧
      0 < ∑ v, sizes v ∧
      (threshold (alphabetCard (Γ := Γ) (Λ := Λ)) : ℝ) <
        6 * G.toRGraph.edgePolynomial (fun v => (sizes v : ℝ) / ((∑ w, sizes w : ℕ) : ℝ)) := by
  obtain ⟨p, m, P, a, ha⟩ := LocalSystem.exists_marked_permutationModel M input hi hh
  exact ⟨p, m, (markedCompletion P a).model, markedSizes,
    markedCompletion_declared P a, markedCompletion_legal P a ha,
    markedSizes_pos P a, markedCompletion_strict P a⟩

end TuranUniversality.Weighted.ConcreteWitness
