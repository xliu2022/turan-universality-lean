module

public import TuranUniversality.Computation.MatchingSystem
public import TuranUniversality.Weighted.Incidence

/-!
# Reading the computational realization from actual root-link incidences

The three relations are exactly the unions of their indexed root copies.
Labels are decoded from the unique declared root-link code, and marks are the
declared cell endpoints of the actual data triple.  No second carrier or
independently assumed matching system is introduced.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

open TuranUniversality.Weighted

variable {Roots Code Kinds Data Alphabet : Type*} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]
  [Inhabited Alphabet]

noncomputable def decodedLabel (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (color : Code → Alphabet) (d : Data) : Alphabet :=
  if h : ∃ c, S.codes.Declared M d c then color h.choose else default

theorem decodedLabel_of_declared (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (color : Code → Alphabet) (d : Data) (c : Code)
    (hc : S.codes.Declared M d c) : decodedLabel S M color d = color c := by
  unfold decodedLabel
  rw [dite_eq_left ⟨c, hc⟩]
  congr 1
  exact S.codes.declared_unique M d _ c (Exists.choose_spec ⟨c, hc⟩) hc

theorem computationalTypes_disjoint (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) :
    Disjoint (S.typeClass M S.cellKind) (S.typeClass M S.colorKind) := by
  apply Finset.disjoint_left.mpr
  intro d hd hc
  obtain ⟨c, hcd, hp⟩ := (S.codes.mem_typeVertices M S.physical S.cellKind d).mp hd
  obtain ⟨c', hc'd, hp'⟩ := (S.codes.mem_typeVertices M S.physical S.colorKind d).mp hc
  have heq := S.codes.declared_unique M d c c' hcd hc'd
  subst c'
  exact S.kinds_ne (hp.symm.trans hp')

/-- The actual matching realization extracted from an incidence-legal rooted
3-graph.  Its only label interpretation parameter is the fixed code-color map. -/
noncomputable def rootedRealization (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (color : Code → Alphabet)
    (hm : ∀ e, S.IsMatching M e) : Realization Data Alphabet where
  cells := S.typeClass M S.cellKind
  colors := S.typeClass M S.colorKind
  disjoint := computationalTypes_disjoint S M
  label := decodedLabel S M color
  J :=
    { pairs := S.unionRelation M 0
      left_mem := by
        intro p hp
        simpa [CompilerSignature.sourceKind] using (S.unionMatching M 0 (hm 0)).left_mem p hp
      right_mem := by
        intro p hp
        simpa [CompilerSignature.targetKind] using (S.unionMatching M 0 (hm 0)).right_mem p hp
      left_injective := (hm 0).1
      right_injective := (hm 0).2 }
  R :=
    { pairs := S.unionRelation M 1
      left_mem := by
        intro p hp
        simpa [CompilerSignature.sourceKind] using (S.unionMatching M 1 (hm 1)).left_mem p hp
      right_mem := by
        intro p hp
        simpa [CompilerSignature.targetKind] using (S.unionMatching M 1 (hm 1)).right_mem p hp
      left_injective := (hm 1).1
      right_injective := (hm 1).2 }
  S :=
    { pairs := S.unionRelation M 2
      left_mem := by
        intro p hp
        simpa [CompilerSignature.sourceKind] using (S.unionMatching M 2 (hm 2)).left_mem p hp
      right_mem := by
        intro p hp
        simpa [CompilerSignature.targetKind] using (S.unionMatching M 2 (hm 2)).right_mem p hp
      left_injective := (hm 2).1
      right_injective := (hm 2).2 }
  marks := S.marks M
  marks_cells := S.marks_subset_cells M

/-- Full legality extends the actual root-incidence conditions by the
explicit positive local computation rules of the supplied finite table. -/
def RootedLegal [DecidableEq Alphabet] (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (color : Code → Alphabet) (P : Specification Alphabet) : Prop :=
  ∃ h : S.IncidenceLegal M, (rootedRealization S M color h.matching).Legal P

end TuranUniversality.Computation.MatchingSystem
