module

public import TuranUniversality.Weighted.Codes
public import TuranUniversality.Weighted.Types

/-! # Physical types decoded from singleton candidate sets -/

@[expose] public section

namespace TuranUniversality.Weighted.CodeSystem

open scoped BigOperators

universe u v w t
variable {Roots : Type u} {Code : Type v} {Data : Type w} {Types : Type t}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Data] [Fintype Data] [DecidableEq Types] [Fintype Types]

def declaredVertices (C : CodeSystem Roots Code) (M : RootedModel Roots Data) : Finset Data :=
  Finset.univ.filter fun d => ¬ C.Ambiguous M d

def typeVertices (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (physical : Code → Types) (t : Types) : Finset Data :=
  Finset.univ.filter fun d => ∃ c, C.Declared M d c ∧ physical c = t

omit [DecidableEq Code] in
@[simp] theorem mem_declaredVertices (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) : d ∈ C.declaredVertices M ↔ ¬ C.Ambiguous M d := by
  simp [declaredVertices]

omit [Fintype Types] in
@[simp] theorem mem_typeVertices (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (physical : Code → Types) (t : Types) (d : Data) :
    d ∈ C.typeVertices M physical t ↔ ∃ c, C.Declared M d c ∧ physical c = t := by
  simp [typeVertices]

omit [DecidableEq Code] [Fintype Data] in
theorem declared_not_ambiguous (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) (c : Code) (hc : C.Declared M d c) : ¬ C.Ambiguous M d := by
  unfold Ambiguous
  rw [hc, Finset.card_singleton]
  omega

/-- The partition is constructed from the actual candidate sets. It is not an
additional assumed type assignment. H1 supplies a singleton code whenever a
vertex is not ambiguous. -/
def physicalPartition (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (physical : Code → Types) (hH1 : C.HasCandidates M) :
    TypePartition (C.declaredVertices M) Types where
  block := C.typeVertices M physical
  disjoint := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro d hds hdt
    obtain ⟨c, hc, hcs⟩ := (C.mem_typeVertices M physical s d).mp hds
    obtain ⟨c', hc', hct⟩ := (C.mem_typeVertices M physical t d).mp hdt
    have hcc := C.declared_unique M d c c' hc hc'
    subst c'
    exact hst (hcs.symm.trans hct)
  cover := by
    ext d
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_typeVertices,
      mem_declaredVertices]
    constructor
    · rintro ⟨t, c, hc, hct⟩
      exact C.declared_not_ambiguous M d c hc
    · intro hnot
      rcases C.declared_or_ambiguous M d (hH1 d) with ⟨c, hc⟩ | ha
      · exact ⟨physical c, c, hc, rfl⟩
      · exact False.elim (hnot ha)

omit [DecidableEq Code] in
theorem declared_ambiguous_mass (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (x : Data → ℝ) :
    (∑ d ∈ C.declaredVertices M, x d) + C.ambiguousWeight M x = ∑ d, x d := by
  unfold declaredVertices ambiguousWeight ambiguousVertices
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases ha : C.Ambiguous M d <;> simp [ha]

theorem total_type_mass (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (physical : Code → Types) (hH1 : C.HasCandidates M) (x : Data → ℝ) :
    (∑ t, (C.physicalPartition M physical hH1).mass x t) =
      (∑ d, x d) - C.ambiguousWeight M x := by
  have hsum := (C.physicalPartition M physical hH1).sum_blocks x
  have hmass := C.declared_ambiguous_mass M x
  change (∑ t, (C.physicalPartition M physical hH1).mass x t) =
    (∑ d ∈ C.declaredVertices M, x d) at hsum
  linarith

def ambiguousDataLink (C : CodeSystem Roots Code) (M : RootedModel Roots Data) (r : Roots) :
    Finset (Finset Data) := M.dataLink r \ (C.declaredVertices M).powersetCard 2

omit [DecidableEq Code] in
/-- The contribution from pairs with an ambiguous endpoint, in any one-root
link, is bounded by `tw - w²/2`. -/
theorem ambiguousDataLink_bound (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (x : Data → ℝ) (r : Roots) (hx : ∀ d, 0 ≤ x d) :
    (∑ p ∈ C.ambiguousDataLink M r, ∏ d ∈ p, x d) ≤
      (∑ d, x d) * C.ambiguousWeight M x - (C.ambiguousWeight M x) ^ 2 / 2 := by
  have hsub : (C.declaredVertices M).powersetCard 2 ⊆
      (Finset.univ : Finset Data).powersetCard 2 := by
    intro p hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp).2⟩
  have hL : C.ambiguousDataLink M r ⊆
      Finset.univ.powersetCard 2 \ (C.declaredVertices M).powersetCard 2 := by
    intro p hp
    obtain ⟨hpL, hpnot⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, M.dataLink_uniform r p hpL⟩, hpnot⟩
  have hmono : (∑ p ∈ C.ambiguousDataLink M r, ∏ d ∈ p, x d) ≤
      ∑ p ∈ Finset.univ.powersetCard 2 \ (C.declaredVertices M).powersetCard 2, ∏ d ∈ p, x d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hL
    intro p hp hnot
    exact Finset.prod_nonneg fun d hd => hx d
  have hsplit := Finset.sum_sdiff hsub (f := fun p : Finset Data => ∏ d ∈ p, x d)
  change (∑ p ∈ Finset.univ.powersetCard 2 \ (C.declaredVertices M).powersetCard 2,
    ∏ d ∈ p, x d) + elementary (C.declaredVertices M) x 2 = elementary Finset.univ x 2 at hsplit
  have hfull := elementary_second_identity Finset.univ x
  have hdecl := elementary_second_identity (C.declaredVertices M) x
  have hsq : (∑ d ∈ C.declaredVertices M, (x d) ^ 2) ≤ ∑ d, (x d) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro d hd hnot
    exact sq_nonneg _
  have hmass := C.declared_ambiguous_mass M x
  rw [← hmass] at hfull ⊢
  nlinarith

end TuranUniversality.Weighted.CodeSystem
