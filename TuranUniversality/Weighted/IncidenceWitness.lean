module

public import TuranUniversality.Weighted.Incidence

/-! # Every failed incidence rule has at most six data vertices -/

@[expose] public section

namespace TuranUniversality.Weighted

universe u v w t
variable {Roots : Type u} {Data : Type v}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Data] [Fintype Data]

namespace RootedModel

/-- Restrict the data carrier while preserving every root label. -/
def restrictData (M : RootedModel Roots Data) (W : Finset Data) : RootedModel Roots W where
  edges := Finset.univ.filter fun p => (p.1, p.2.image Subtype.val) ∈ M.edges
  uniform := by
    intro p hp
    have h := M.uniform (p.1, p.2.image Subtype.val) (Finset.mem_filter.mp hp).2
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
    exact h

@[simp] theorem mem_restrictData (M : RootedModel Roots Data) (W : Finset Data)
    (p : Finset Roots) (q : Finset W) :
    (p, q) ∈ (M.restrictData W).edges ↔ (p, q.image Subtype.val) ∈ M.edges := by
  simp [restrictData]

@[simp] theorem restrictData_rootLink (M : RootedModel Roots Data) (W : Finset Data) (d : W) :
    (M.restrictData W).rootLink d = M.rootLink d.val := by
  ext p
  simp only [mem_rootLink, mem_restrictData, Finset.image_singleton]

@[simp] theorem restrictData_dataLink (M : RootedModel Roots Data) (W : Finset Data)
    (r : Roots) (p : Finset W) :
    p ∈ (M.restrictData W).dataLink r ↔ p.image Subtype.val ∈ M.dataLink r := by
  simp only [mem_dataLink, mem_restrictData]

@[simp] theorem restrictData_dataTriples (M : RootedModel Roots Data) (W : Finset Data) (p : Finset W) :
    p ∈ (M.restrictData W).dataTriples ↔ p.image Subtype.val ∈ M.dataTriples := by
  simp only [mem_dataTriples, mem_restrictData]

end RootedModel

def liftDataSet (W p : Finset Data) : Finset W := Finset.univ.filter fun d : W => d.val ∈ p

@[simp] theorem mem_liftDataSet (W p : Finset Data) (d : W) : d ∈ liftDataSet W p ↔ d.val ∈ p := by
  simp [liftDataSet]

theorem liftDataSet_image (W p : Finset Data) (hp : p ⊆ W) :
    (liftDataSet W p).image Subtype.val = p := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact (mem_liftDataSet W p e).mp he
  · intro hd
    exact Finset.mem_image.mpr ⟨⟨d, hp hd⟩, (mem_liftDataSet W p _).mpr hd, rfl⟩

namespace CompilerSignature

variable {Code : Type w} {Kinds : Type t} {L : ℕ}
  [DecidableEq Code] [Fintype Code] [DecidableEq Kinds] [Fintype Kinds]

@[simp] theorem restrict_candidates (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (W : Finset Data) (d : W) :
    S.codes.candidates (M.restrictData W) d = S.codes.candidates M d.val := by
  ext c
  simp only [CodeSystem.mem_candidates, RootedModel.restrictData_rootLink]

@[simp] theorem restrict_declared (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (W : Finset Data) (d : W) (c : Code) :
    S.codes.Declared (M.restrictData W) d c ↔ S.codes.Declared M d.val c := by
  unfold CodeSystem.Declared
  rw [S.restrict_candidates]

@[simp] theorem restrict_typeClass (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (W : Finset Data) (d : W) (k : Kinds) :
    d ∈ S.typeClass (M.restrictData W) k ↔ d.val ∈ S.typeClass M k := by
  simp only [typeClass, CodeSystem.mem_typeVertices, S.restrict_declared]

@[simp] theorem restrict_relationCopy (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (W : Finset Data) (e : Fin 3) (j : Fin L) (a b : W) :
    (a, b) ∈ S.relationCopy (M.restrictData W) e j ↔
      (a.val, b.val) ∈ S.relationCopy M e j := by
  simp only [mem_relationCopy, S.restrict_typeClass, RootedModel.mem_restrictData,
    Finset.image_insert, Finset.image_singleton]

@[simp] theorem restrict_unionRelation (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (W : Finset Data) (e : Fin 3) (a b : W) :
    (a, b) ∈ S.unionRelation (M.restrictData W) e ↔
      (a.val, b.val) ∈ S.unionRelation M e := by
  simp only [mem_unionRelation, S.restrict_relationCopy]

/-- All incidence clauses are detected by restrictions with at most six data
vertices. Root-pair candidate sets are preserved exactly under restriction. -/
theorem incidenceLegal_of_small_restrictions (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data)
    (h : ∀ W : Finset Data, W.card ≤ 6 → S.IncidenceLegal (M.restrictData W)) :
    S.IncidenceLegal M := by
  constructor
  · intro d
    let W : Finset Data := {d}
    have hW : W.card ≤ 6 := by simp [W]
    have hc := (h W hW).candidates ⟨d, by simp [W]⟩
    simpa only [S.restrict_candidates] using hc
  · intro r p hp a ha b hb hab c d hc hd hcd
    have hpcard := M.dataLink_uniform r p hp
    have hsmall := h p (by omega)
    let a' : p := ⟨a, ha⟩
    let b' : p := ⟨b, hb⟩
    let q := liftDataSet p p
    have hqimage : q.image Subtype.val = p := liftDataSet_image p p (Finset.Subset.refl _)
    have hq : q ∈ (M.restrictData p).dataLink r :=
      (M.restrictData_dataLink p r q).mpr (by simpa only [hqimage] using hp)
    exact hsmall.oneRoot r q hq a' (by simpa [q, a'] using ha) b' (by simpa [q, b'] using hb)
      (fun he => hab (congrArg Subtype.val he)) c d
      ((S.restrict_declared M p a' c).mpr hc) ((S.restrict_declared M p b' d).mpr hd) hcd
  · intro e
    have hmatch : ∀ p q : Data × Data, p ∈ S.unionRelation M e → q ∈ S.unionRelation M e →
        (p.1 = q.1 ∨ p.2 = q.2) → p = q := by
      intro p q hp hq heq
      let W : Finset Data := {p.1, p.2} ∪ {q.1, q.2}
      have hW : W.card ≤ 6 := by
        have hU := Finset.card_union_le ({p.1, p.2} : Finset Data) {q.1, q.2}
        have hp2 : ({p.1, p.2} : Finset Data).card ≤ 2 := Finset.card_le_two
        have hq2 : ({q.1, q.2} : Finset Data).card ≤ 2 := Finset.card_le_two
        dsimp [W]
        omega
      let p' : W × W := (⟨p.1, by simp [W]⟩, ⟨p.2, by simp [W]⟩)
      let q' : W × W := (⟨q.1, by simp [W]⟩, ⟨q.2, by simp [W]⟩)
      have hp' : p' ∈ S.unionRelation (M.restrictData W) e :=
        (S.restrict_unionRelation M W e p'.1 p'.2).mpr hp
      have hq' : q' ∈ S.unionRelation (M.restrictData W) e :=
        (S.restrict_unionRelation M W e q'.1 q'.2).mpr hq
      have hpq : p' = q' := by
        rcases heq with hl | hr
        · exact ((h W hW).matching e).1 hp' hq' (Subtype.ext hl)
        · exact ((h W hW).matching e).2 hp' hq' (Subtype.ext hr)
      exact Prod.ext (congrArg (fun z : W × W => z.1.val) hpq)
        (congrArg (fun z : W × W => z.2.val) hpq)
    exact ⟨fun p hp q hq heq => hmatch p q hp hq (Or.inl heq),
      fun p hp q hq heq => hmatch p q hp hq (Or.inr heq)⟩
  · apply Finset.card_le_one.mpr
    intro p hp q hq
    let W := p ∪ q
    have hp3 := M.dataTriples_uniform p hp
    have hq3 := M.dataTriples_uniform q hq
    have hW : W.card ≤ 6 := by
      have hh := Finset.card_union_le p q
      dsimp [W]
      omega
    let p' := liftDataSet W p
    let q' := liftDataSet W q
    have hpim : p'.image Subtype.val = p := liftDataSet_image W p Finset.subset_union_left
    have hqim : q'.image Subtype.val = q := liftDataSet_image W q Finset.subset_union_right
    have hp' : p' ∈ (M.restrictData W).dataTriples :=
      (M.restrictData_dataTriples W p').mpr (by simpa only [hpim] using hp)
    have hq' : q' ∈ (M.restrictData W).dataTriples :=
      (M.restrictData_dataTriples W q').mpr (by simpa only [hqim] using hq)
    have heq := Finset.card_le_one.mp (h W hW).oneMarker p' hp' q' hq'
    have him := congrArg (fun p : Finset W => p.image Subtype.val) heq
    simpa only [hpim, hqim] using him
  · intro p hp d hd c hc
    have hp3 := M.dataTriples_uniform p hp
    let d' : p := ⟨d, hd⟩
    let p' := liftDataSet p p
    have hpim : p'.image Subtype.val = p := liftDataSet_image p p (Finset.Subset.refl _)
    have hp' : p' ∈ (M.restrictData p).dataTriples :=
      (M.restrictData_dataTriples p p').mpr (by simpa only [hpim] using hp)
    exact (h p (by omega)).markerTypes p' hp' d' (by simpa [p', d'] using hd) c
      ((S.restrict_declared M p d' c).mpr hc)

theorem small_incidence_witness (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : ¬ S.IncidenceLegal M) :
    ∃ W : Finset Data, W.card ≤ 6 ∧ ¬ S.IncidenceLegal (M.restrictData W) := by
  classical
  by_contra hnot
  apply h
  apply S.incidenceLegal_of_small_restrictions M
  intro W hW
  by_contra hn
  exact hnot ⟨W, hW, hn⟩

end CompilerSignature

end TuranUniversality.Weighted
