/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootedMonotonicity
public import TuranUniversality.Weighted.IncidenceWitness
public import TuranUniversality.Computation.LocalWitness

/-! # Bounded failures of actual rooted legality -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

variable {Roots Data Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Fintype Data] [DecidableEq Data]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet]

def markerSupport (M : RootedModel Roots Data) : Finset Data := M.dataTriples.biUnion id

theorem markerSupport_card (M : RootedModel Roots Data) (hone : M.dataTriples.card ≤ 1) :
    (markerSupport M).card ≤ 3 := by
  calc
    (markerSupport M).card ≤ M.dataTriples.card * 3 :=
      Finset.card_biUnion_le_card_mul _ _ 3 (fun p hp => le_of_eq (M.dataTriples_uniform p hp))
    _ ≤ 1 * 3 := Nat.mul_le_mul_right 3 hone
    _ = 3 := by norm_num

theorem subset_markerSupport (M : RootedModel Roots Data) (p : Finset Data)
    (hp : p ∈ M.dataTriples) : p ⊆ markerSupport M := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨p, hp, hx⟩

theorem decodedLabel_restrictData
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (color : Code → Alphabet) (W : Finset Data) (d : W) :
    decodedLabel S (M.restrictData W) color d = decodedLabel S M color d.val := by
  classical
  by_cases h : ∃ c, S.codes.Declared M d.val c
  · obtain ⟨c, hc⟩ := h
    rw [decodedLabel_of_declared S (M.restrictData W) color d c
      ((S.restrict_declared M W d c).mpr hc), decodedLabel_of_declared S M color d.val c hc]
  · have h' : ¬ ∃ c, S.codes.Declared (M.restrictData W) d c := by
      simpa only [S.restrict_declared] using h
    simp only [decodedLabel, dite_eq_right h, dite_eq_right h']

theorem marks_restrictData
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (W : Finset Data) (hmarks : markerSupport M ⊆ W) (d : W)
    (hd : d.val ∈ S.marks M) : d ∈ S.marks (M.restrictData W) := by
  obtain ⟨hxtype, p, hp, hxp⟩ := (Finset.mem_filter.mp hd).2
  have hpW : p ⊆ W := (subset_markerSupport M p hp).trans hmarks
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (S.restrict_typeClass M W d S.cellKind).mpr hxtype,
    liftDataSet W p, ?_, ?_⟩
  · apply (M.restrictData_dataTriples W _).mpr
    simpa only [liftDataSet_image W p hpW] using hp
  · exact (mem_liftDataSet W p d).mpr hxp

/-- Retaining the computational witness and the data-only edge gives an
actual rooted graph containing the same failed positive pattern. -/
noncomputable def restriction_realization_pullback
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (color : Code → Alphabet) (hM : S.IncidenceLegal M)
    (U W : Finset Data) (hUW : U ⊆ W) (hmarks : markerSupport M ⊆ W)
    (hW : S.IncidenceLegal (M.restrictData W)) :
    Realization.Pullback ((rootedRealization S M color hM.matching).restrict U)
      (rootedRealization S (M.restrictData W) color hW.matching) where
  domain := U
  map := fun x => ⟨x.val, hUW x.property⟩
  injective := by intro x y heq; exact Subtype.ext (congrArg (fun z : W => z.val) heq)
  J_domain := by
    intro x y hp
    exact (((rootedRealization S M color hM.matching).restrict_J U x y).mp hp).2
  R_domain := by
    intro x y hp
    exact (((rootedRealization S M color hM.matching).restrict_R U x y).mp hp).2
  S_domain := by
    intro x y hp
    exact (((rootedRealization S M color hM.matching).restrict_S U x y).mp hp).2
  marks_domain := Finset.inter_subset_right
  J_preserve := by
    intro x y hp
    apply (S.restrict_unionRelation M W 0 _ _).mpr
    exact (((rootedRealization S M color hM.matching).restrict_J U x.val y.val).mp hp).1
  R_preserve := by
    intro x y hp
    apply (S.restrict_unionRelation M W 1 _ _).mpr
    exact (((rootedRealization S M color hM.matching).restrict_R U x.val y.val).mp hp).1
  S_preserve := by
    intro x y hp
    apply (S.restrict_unionRelation M W 2 _ _).mpr
    exact (((rootedRealization S M color hM.matching).restrict_S U x.val y.val).mp hp).1
  label_preserve := fun x _ => decodedLabel_restrictData S M color W ⟨x.val, hUW x.property⟩
  marks_preserve := fun x hx => marks_restrictData S M W hmarks ⟨x.val, hUW x.property⟩
    (Finset.mem_inter.mp hx).1

def rootedWitnessBound (spec : Specification Alphabet) : ℕ := spec.witnessBound + 3

/-- Every failure of full rooted legality is witnessed by at most
`14 + 2 * prefix.length` data vertices, with all root labels retained. -/
theorem small_rooted_witness (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (color : Code → Alphabet) (spec : Specification Alphabet)
    (hbad : ¬ RootedLegal S M color spec) :
    ∃ W : Finset Data, W.card ≤ rootedWitnessBound spec ∧
      ¬ RootedLegal S (M.restrictData W) color spec := by
  classical
  by_cases hinc : S.IncidenceLegal M
  · have hcomp : ¬ (rootedRealization S M color hinc.matching).Legal spec :=
      fun h => hbad ⟨hinc, h⟩
    obtain ⟨U, hU, hfailure⟩ := (rootedRealization S M color hinc.matching).exists_small_failure spec hcomp
    let W := U ∪ markerSupport M
    have hcard : W.card ≤ rootedWitnessBound spec := by
      have hmarker := markerSupport_card M hinc.oneMarker
      have hunion := Finset.card_union_le U (markerSupport M)
      dsimp [W, rootedWitnessBound]
      omega
    refine ⟨W, hcard, ?_⟩
    rintro ⟨hWinc, hWcomp⟩
    exact hfailure ((restriction_realization_pullback S M color hinc U W
      Finset.subset_union_left Finset.subset_union_right hWinc).legal spec hWcomp)
  · obtain ⟨W, hW, hfailure⟩ := S.small_incidence_witness M hinc
    refine ⟨W, ?_, fun h => hfailure h.choose⟩
    unfold rootedWitnessBound Specification.witnessBound
    omega

end TuranUniversality.Selector
