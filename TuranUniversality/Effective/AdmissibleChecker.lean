module

public import TuranUniversality.Effective.RootedChecker
public import TuranUniversality.Effective.MatchingDecision
public import TuranUniversality.Effective.WordEnumeration

/-! # Finite assignment enumeration deciding actual admissibility -/

@[expose] public section

namespace TuranUniversality.Effective

open Weighted Selector Computation.MatchingSystem

variable {Roots Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Primcodable Roots]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Fintype Alphabet] [DecidableEq Alphabet] [Inhabited Alphabet] [Primcodable Alphabet]

namespace RootedCode

def FullOK (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (P : Specification Alphabet) : Prop :=
  c.Valid ∧ IncidenceOK S c ∧ (matchingCode S color c).Legal P

noncomputable instance (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (P : Specification Alphabet) : Decidable (FullOK S color c P) := by
  unfold FullOK
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The code accepts exactly when its literal assignment yields a fully
legal rooted graph, including all five computational local conditions. -/
theorem fullOK_iff (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (P : Specification Alphabet) :
    FullOK S color c P ↔ ∃ h : c.Valid, RootedLegal S (c.model h) color P := by
  constructor
  · rintro ⟨hv, hi, hq⟩
    have hinc := (incidenceOK_iff S c hv).mp hi
    exact ⟨hv, hinc, ((matchingCode_represents S color c hv hinc.matching).legal_iff P).mp hq⟩
  · rintro ⟨hv, hinc, hq⟩
    exact ⟨hv, (incidenceOK_iff S c hv).mpr hinc,
      ((matchingCode_represents S color c hv hinc.matching).legal_iff P).mpr hq⟩

noncomputable def check (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (P : Specification Alphabet) : Bool := decide (FullOK S color c P)

@[simp] theorem check_eq_true (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (P : Specification Alphabet) :
    check S color c P = true ↔ FullOK S color c P := by simp [check]

theorem assignment_ofFn (g : GraphCode) (ρ : VertexRooting Roots (Fin g.1)) (x : Fin g.1) :
    assignment (g, List.ofFn ρ.val) x.val = ρ.val x := by
  unfold assignment
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using x.isLt), List.getElem_ofFn]

theorem valid_ofFn (g : GraphCode) (ρ : VertexRooting Roots (Fin g.1)) :
    Valid (g, List.ofFn ρ.val) := by
  intro x hx y hy r hxr hyr
  have hx' := (assignment_ofFn g ρ ⟨x, hx⟩).symm.trans hxr
  have hy' := (assignment_ofFn g ρ ⟨y, hy⟩).symm.trans hyr
  exact congrArg Fin.val (ρ.property ⟨x, hx⟩ ⟨y, hy⟩ r hx' hy')

theorem rooting_ofFn (g : GraphCode) (ρ : VertexRooting Roots (Fin g.1)) :
    rooting (g, List.ofFn ρ.val) (valid_ofFn g ρ) = ρ := by
  apply Subtype.ext
  funext x
  exact assignment_ofFn g ρ x

theorem model_ofFn (g : GraphCode) (ρ : VertexRooting Roots (Fin g.1)) :
    model (g, List.ofFn ρ.val) (valid_ofFn g ρ) =
      rootedImage (decodeGraph g) ρ.val ρ.property := by
  exact congrArg (fun ξ : VertexRooting Roots (Fin g.1) =>
    rootedImage (decodeGraph g) ξ.val ξ.property) (rooting_ofFn g ρ)

end RootedCode

/-- Enumerate all partial root labels on a graph of order `n`. -/
noncomputable def assignmentWords (Roots : Type*) [Fintype Roots] (n : ℕ) :
    List (List (Option Roots)) := allWords Finset.univ.toList n

theorem assignmentWords_primrec : Primrec (assignmentWords Roots) :=
  allWords_primrec.comp (Primrec.const Finset.univ.toList) Primrec.id

@[simp] theorem mem_assignmentWords (n : ℕ) (a : List (Option Roots)) :
    a ∈ assignmentWords Roots n ↔ a.length = n := by
  simp [assignmentWords, mem_allWords]

def AdmissibleOK (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (g : GraphCode) (P : Specification Alphabet) : Prop :=
  ∃ a ∈ assignmentWords Roots g.1, RootedCode.FullOK S color (g, a) P

noncomputable instance (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (g : GraphCode) (P : Specification Alphabet) : Decidable (AdmissibleOK S color g P) := by
  unfold AdmissibleOK
  infer_instance

/-- Finite code enumeration is equivalent to existence of an actual legal
partial rooting of the decoded graph. -/
theorem admissibleOK_iff (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (g : GraphCode) (P : Specification Alphabet) :
    AdmissibleOK S color g P ↔ Admissible S color P (decodeGraph g) := by
  constructor
  · rintro ⟨a, _, ha⟩
    obtain ⟨hv, hlegal⟩ := (RootedCode.fullOK_iff S color (g, a) P).mp ha
    exact ⟨RootedCode.rooting (g, a) hv, hlegal⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨List.ofFn ρ.val, (mem_assignmentWords _ _).mpr (by simp), ?_⟩
    apply (RootedCode.fullOK_iff S color (g, List.ofFn ρ.val) P).mpr
    exact ⟨RootedCode.valid_ofFn g ρ, by rw [RootedCode.model_ofFn]; exact hρ⟩

noncomputable def admissibleCheck (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (g : GraphCode) (P : Specification Alphabet) : Bool := decide (AdmissibleOK S color g P)

@[simp] theorem admissibleCheck_correct (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (g : GraphCode) (P : Specification Alphabet) :
    admissibleCheck S color g P = true ↔ Admissible S color P (decodeGraph g) := by
  simp only [admissibleCheck, decide_eq_true_eq, admissibleOK_iff S color g P]

end TuranUniversality.Effective
