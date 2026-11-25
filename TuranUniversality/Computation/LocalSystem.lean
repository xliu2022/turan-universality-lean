module

public import TuranUniversality.Computation.MatchingSystem

/-!
# The fixed wall/static/reset alphabet and its explicit local tables

The only input-dependent table is the finite Start-prefix word.  Horizontal
and evolution tables are fixed once the ordinary finite machine is fixed.
Walls persist, and boundary neighbors are read as running headless blanks.
-/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem

open Turing Cellular ResetProtocol

inductive Label (Γ Λ : Type*)
  | leftWall
  | rightWall
  | cell (static : StaticInput.Symbol Γ) (dynamic : ResetProtocol.Symbol Γ Λ)
  deriving DecidableEq, Inhabited

noncomputable instance {Γ Λ : Type*} [Fintype Γ] [Fintype Λ] : Fintype (Label Γ Λ) := by
  classical
  exact
    { elems := {.leftWall, .rightWall} ∪
        (Finset.univ : Finset (StaticInput.Symbol Γ × ResetProtocol.Symbol Γ Λ)).image
          (fun p => .cell p.1 p.2)
      complete := by intro x; cases x <;> simp }

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def staticPart : Label Γ Λ → Option (StaticInput.Symbol Γ)
  | .cell s _ => some s
  | _ => none

def dynamicPart : Label Γ Λ → ResetProtocol.Symbol Γ Λ
  | .cell _ d => d
  | _ => (.running, blankCell)

def Unary (M : TM0.Machine Γ Λ) : Label Γ Λ → Prop
  | .cell _ d => ValidSymbol M d
  | _ => True

def HorizontalCore : Label Γ Λ → Label Γ Λ → Prop
  | .rightWall, .leftWall => True
  | .leftWall, .cell s d => StaticInput.Starts s ∧ ResetGrammar.Starts d.1
  | .cell s d, .rightWall => StaticInput.Ends s ∧ ResetGrammar.Ends d.1
  | .cell s d, .cell s' d' => StaticInput.Adjacent s s' ∧ ResetGrammar.Adjacent d.1 d'.1
  | _, _ => False

def Horizontal (M : TM0.Machine Γ Λ) (a b : Label Γ Λ) : Prop :=
  Unary M a ∧ Unary M b ∧ HorizontalCore a b

/-- The fixed local transition table.  A cell keeps its exact immutable
static symbol, while the dynamic symbol obeys the proved reset protocol. -/
def Evolution (M : TM0.Machine Γ Λ) (l a r b : Label Γ Λ) : Prop :=
  match a with
  | .leftWall => b = .leftWall
  | .rightWall => b = .rightWall
  | .cell s d => ∃ d', b = .cell s d' ∧
      LocalStep M (StaticInput.frozen s) (dynamicPart l) d (dynamicPart r) d'

def IsInitial : Label Γ Λ → Prop
  | .cell _ d => d = initialSymbol
  | _ => False

def IsStart : Label Γ Λ → Prop
  | .cell (.start _) _ => True
  | _ => False

/-- A fixed blank background satisfies both local tables for every input. -/
def background : Label Γ Λ := .cell .after (.running, blankCell)

theorem background_horizontal (M : TM0.Machine Γ Λ) :
    Horizontal M (background (Γ := Γ) (Λ := Λ)) background := by
  trivial

theorem background_evolution (M : TM0.Machine Γ Λ) :
    Evolution M (background (Γ := Γ) (Λ := Λ)) background background background := by
  refine ⟨(.running, blankCell), rfl, ?_⟩
  simp [background, dynamicPart, LocalStep, localRule, incoming, blankCell]

variable [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- The finite table read by the positive-witness matching conditions. -/
noncomputable def specification (M : TM0.Machine Γ Λ) (input : List Γ) :
    MatchingSystem.Specification (Label Γ Λ) := by
  classical
  exact
    { leftWall := .leftWall
      initial := Finset.univ.filter IsInitial
      horizontal := Finset.univ.filter fun p => Horizontal M p.1 p.2
      evolution := Finset.univ.filter fun p => Evolution M p.1 p.2.1 p.2.2.1 p.2.2.2
      prefixTrigger := Finset.univ.filter IsStart
      inputPrefix := (StaticInput.inputWord input ++ [StaticInput.Symbol.finish]).map fun s =>
        Finset.univ.filter fun a => staticPart a = some s }

@[simp] theorem mem_initial (M : TM0.Machine Γ Λ) (input : List Γ) (a : Label Γ Λ) :
    a ∈ (specification M input).initial ↔ IsInitial a := by
  simp [specification]

@[simp] theorem mem_horizontal (M : TM0.Machine Γ Λ) (input : List Γ) (a b : Label Γ Λ) :
    (a, b) ∈ (specification M input).horizontal ↔ Horizontal M a b := by
  simp [specification]

@[simp] theorem mem_evolution (M : TM0.Machine Γ Λ) (input : List Γ)
    (l a r b : Label Γ Λ) :
    (l, a, r, b) ∈ (specification M input).evolution ↔ Evolution M l a r b := by
  simp [specification]

@[simp] theorem mem_prefixTrigger (M : TM0.Machine Γ Λ) (input : List Γ) (a : Label Γ Λ) :
    a ∈ (specification M input).prefixTrigger ↔ IsStart a := by
  simp [specification]

@[simp] theorem inputPrefix_length (M : TM0.Machine Γ Λ) (input : List Γ) :
    (specification M input).inputPrefix.length = input.length + 1 := by
  cases input <;> simp [specification, StaticInput.inputWord]

set_option backward.isDefEq.respectTransparency false in
theorem mem_inputPrefix (M : TM0.Machine Γ Λ) (input : List Γ) (j : ℕ)
    (hj : j < (specification M input).inputPrefix.length) (a : Label Γ Λ) :
    a ∈ (specification M input).inputPrefix[j] ↔
      staticPart a = (StaticInput.inputWord input ++ [StaticInput.Symbol.finish])[j]? := by
  have hlen : j < (StaticInput.inputWord input ++ [StaticInput.Symbol.finish]).length := by
    simpa [specification] using hj
  classical
  change a ∈ ((StaticInput.inputWord input ++ [StaticInput.Symbol.finish]).map
    (fun s => Finset.univ.filter fun a : Label Γ Λ => staticPart a = some s))[j] ↔ _
  rw [List.getElem_map]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.getElem?_eq_getElem hlen]

end TuranUniversality.Computation.LocalSystem
