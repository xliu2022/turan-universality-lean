module

public import TuranUniversality.Weighted.DeclaredTypes
public import TuranUniversality.Weighted.Matching

/-! # The rooted incidence rules H1--H4

This file encodes the root/type/matching part of legality. The computational
rules Q1--Q4 are imposed on the extracted J/R/S relations in the computation
module; they are deliberately not replaced here by an arbitrary proposition.
-/

@[expose] public section

namespace TuranUniversality.Weighted

universe u v w t

structure CompilerSignature (Roots : Type u) (Code : Type v) (Kinds : Type w)
    [DecidableEq Roots] [Fintype Roots] (L : ℕ) where
  codes : CodeSystem Roots Code
  physical : Code → Kinds
  cellKind : Kinds
  colorKind : Kinds
  kinds_ne : cellKind ≠ colorKind
  copyRoot : (Fin 3 × Fin L) ↪ Roots

namespace CompilerSignature

variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

def sourceKind (S : CompilerSignature Roots Code Kinds L) (e : Fin 3) : Kinds :=
  if e = 0 then S.cellKind else S.colorKind

def targetKind (S : CompilerSignature Roots Code Kinds L) (e : Fin 3) : Kinds :=
  if e = 0 then S.colorKind else S.cellKind

omit [DecidableEq Code] [Fintype Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem source_ne_target (S : CompilerSignature Roots Code Kinds L) (e : Fin 3) :
    S.sourceKind e ≠ S.targetKind e := by
  unfold sourceKind targetKind
  split_ifs
  · exact S.kinds_ne
  · exact S.kinds_ne.symm

def typeClass (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (kind : Kinds) : Finset Data := S.codes.typeVertices M S.physical kind

def relationCopy (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (e : Fin 3) (j : Fin L) : Finset (Data × Data) :=
  Finset.univ.filter fun p =>
    p.1 ∈ S.typeClass M (S.sourceKind e) ∧ p.2 ∈ S.typeClass M (S.targetKind e) ∧
      ({S.copyRoot (e, j)}, {p.1, p.2}) ∈ M.edges

def unionRelation (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (e : Fin 3) : Finset (Data × Data) :=
  Finset.univ.biUnion fun j => S.relationCopy M e j

omit [Fintype Kinds] in
@[simp] theorem mem_relationCopy (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (e : Fin 3) (j : Fin L) (p : Data × Data) :
    p ∈ S.relationCopy M e j ↔
      p.1 ∈ S.typeClass M (S.sourceKind e) ∧ p.2 ∈ S.typeClass M (S.targetKind e) ∧
        ({S.copyRoot (e, j)}, {p.1, p.2}) ∈ M.edges := by
  simp [relationCopy]

omit [Fintype Kinds] in
@[simp] theorem mem_unionRelation (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (e : Fin 3) (p : Data × Data) :
    p ∈ S.unionRelation M e ↔ ∃ j, p ∈ S.relationCopy M e j := by
  simp [unionRelation]

def IsMatching (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (e : Fin 3) : Prop :=
  Set.InjOn Prod.fst (S.unionRelation M e : Set (Data × Data)) ∧
    Set.InjOn Prod.snd (S.unionRelation M e : Set (Data × Data))

/-- Only the two incident physical types may have same-type pairs at a
relation root; additional roots have no permitted same-type declared pairs.
All distinct-type pairs are allowed by H2; the special cell/color pairs are
restricted by the matching condition on `unionRelation`.
-/
def OneRootRules (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) : Prop :=
  ∀ r p, p ∈ M.dataLink r → ∀ a ∈ p, ∀ b ∈ p, a ≠ b →
    ∀ c d, S.codes.Declared M a c → S.codes.Declared M b d → S.physical c = S.physical d →
      (∃ e j, S.copyRoot (e, j) = r) ∧ (S.physical c = S.cellKind ∨ S.physical c = S.colorKind)

def MarkerTypes (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) : Prop :=
  ∀ p ∈ M.dataTriples, ∀ d ∈ p, ∀ c, S.codes.Declared M d c → S.physical c = S.cellKind

def marks (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) : Finset Data :=
  Finset.univ.filter fun d => d ∈ S.typeClass M S.cellKind ∧ ∃ p ∈ M.dataTriples, d ∈ p

omit [Fintype Kinds] in
theorem marks_subset_cells (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) :
    S.marks M ⊆ S.typeClass M S.cellKind := by
  intro d hd
  exact (Finset.mem_filter.mp hd).2.1

/-- The incidence portion of H1--H4. Full legal rootings additionally satisfy
the actual computational Q1--Q4 rules on the extracted relations and marks. -/
structure IncidenceLegal (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) : Prop where
  candidates : S.codes.HasCandidates M
  oneRoot : S.OneRootRules M
  matching : ∀ e, S.IsMatching M e
  oneMarker : M.dataTriples.card ≤ 1
  markerTypes : S.MarkerTypes M

def unionMatching (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (e : Fin 3) (h : S.IsMatching M e) :
    PartialMatching (S.typeClass M (S.sourceKind e)) (S.typeClass M (S.targetKind e)) where
  pairs := S.unionRelation M e
  left_mem := by
    intro p hp
    obtain ⟨j, hj⟩ := (S.mem_unionRelation M e p).mp hp
    exact ((S.mem_relationCopy M e j p).mp hj).1
  right_mem := by
    intro p hp
    obtain ⟨j, hj⟩ := (S.mem_unionRelation M e p).mp hp
    exact ((S.mem_relationCopy M e j p).mp hj).2.1
  left_injective := h.1
  right_injective := h.2

def copyMatching (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (e : Fin 3) (j : Fin L) (h : S.IsMatching M e) :
    PartialMatching (S.typeClass M (S.sourceKind e)) (S.typeClass M (S.targetKind e)) where
  pairs := S.relationCopy M e j
  left_mem := fun p hp => ((S.mem_relationCopy M e j p).mp hp).1
  right_mem := fun p hp => ((S.mem_relationCopy M e j p).mp hp).2.1
  left_injective := by
    intro p hp q hq heq
    exact h.1 ((S.mem_unionRelation M e p).mpr ⟨j, hp⟩)
      ((S.mem_unionRelation M e q).mpr ⟨j, hq⟩) heq
  right_injective := by
    intro p hp q hq heq
    exact h.2 ((S.mem_unionRelation M e p).mpr ⟨j, hp⟩)
      ((S.mem_unionRelation M e q).mpr ⟨j, hq⟩) heq

omit [Fintype Kinds] in
theorem copy_defect_ge_union (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (e : Fin 3) (j : Fin L) (h : S.IsMatching M e)
    (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    (S.unionMatching M e h).defect x x ≤ (S.copyMatching M e j h).defect x x := by
  apply PartialMatching.defect_antitone
  · intro d hd
    exact hx d
  · intro d hd
    exact hx d
  · intro p hp
    exact (S.mem_unionRelation M e p).mpr ⟨j, hp⟩

end CompilerSignature

end TuranUniversality.Weighted
