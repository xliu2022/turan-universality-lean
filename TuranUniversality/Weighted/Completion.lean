module

public import TuranUniversality.Weighted.LinkModel
public import TuranUniversality.Weighted.Incidence
public import TuranUniversality.Weighted.TypedLink
public import TuranUniversality.Weighted.BaselineModel

/-! # The concrete completion of a declared computation pattern -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

def assignmentPartition (physical : Code → Kinds) (code : Data → Code) :
    TypePartition (Finset.univ : Finset Data) Kinds where
  block k := Finset.univ.filter fun d => physical (code d) = k
  disjoint := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro d hds hdt
    exact hst ((Finset.mem_filter.mp hds).2.symm.trans (Finset.mem_filter.mp hdt).2)
  cover := by
    ext d
    simp

omit [DecidableEq Code] [Fintype Code] in
@[simp] theorem mem_assignmentPartition (physical : Code → Kinds) (code : Data → Code)
    (k : Kinds) (d : Data) : d ∈ (assignmentPartition physical code).block k ↔ physical (code d) = k := by
  simp [assignmentPartition]

/-- Finite input data for a completed rooted graph. The three actual partial
matchings and the marker triples are part of the construction. -/
structure Completion (S : CompilerSignature Roots Code Kinds L) (Data : Type t)
    [DecidableEq Data] [Fintype Data] where
  code : Data → Code
  matching : ∀ e : Fin 3, PartialMatching
    ((assignmentPartition S.physical code).block (S.sourceKind e))
    ((assignmentPartition S.physical code).block (S.targetKind e))
  markers : Finset (Finset Data)
  marker_uniform : ∀ p ∈ markers, p.card = 3
  one_marker : markers.card ≤ 1
  marker_type : ∀ p ∈ markers, ∀ d ∈ p, S.physical (code d) = S.cellKind

namespace Completion

variable {S : CompilerSignature Roots Code Kinds L}

abbrev partition (C : Completion S Data) := assignmentPartition S.physical C.code

def indexedLink (C : Completion S Data) (e : Fin 3) : Finset (Finset Data) :=
  C.partition.matchedLink (S.sourceKind e) (S.targetKind e) (C.matching e)

def dataLink (C : Completion S Data) (r : Roots) : Finset (Finset Data) :=
  if ∃ p : Fin 3 × Fin L, S.copyRoot p = r then
    Finset.univ.biUnion fun p : Fin 3 × Fin L =>
      if S.copyRoot p = r then C.indexedLink p.1 else ∅
  else C.partition.crossPairs

omit [DecidableEq Code] [Fintype Code] in
@[simp] theorem dataLink_copy (C : Completion S Data) (e : Fin 3) (j : Fin L) :
    C.dataLink (S.copyRoot (e, j)) = C.indexedLink e := by
  unfold dataLink
  rw [ite_eq_left ⟨(e, j), rfl⟩]
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    by_cases heq : S.copyRoot q = S.copyRoot (e, j)
    · have hqeq : q = (e, j) := S.copyRoot.injective heq
      simpa [heq, hqeq] using hq
    · simp [heq] at hq
  · intro hp
    exact ⟨(e, j), by simpa using hp⟩

omit [DecidableEq Code] [Fintype Code] in
theorem dataLink_additional (C : Completion S Data) (r : Roots)
    (hr : ¬ ∃ p : Fin 3 × Fin L, S.copyRoot p = r) : C.dataLink r = C.partition.crossPairs := by
  simp [dataLink, hr]

theorem dataLink_uniform (C : Completion S Data) (r : Roots) (p : Finset Data)
    (hp : p ∈ C.dataLink r) : p.card = 2 := by
  by_cases hr : ∃ q : Fin 3 × Fin L, S.copyRoot q = r
  · obtain ⟨⟨e, j⟩, rfl⟩ := hr
    rw [C.dataLink_copy] at hp
    exact C.partition.matchedLink_uniform _ _ (S.source_ne_target e) (C.matching e) p hp
  · rw [C.dataLink_additional r hr] at hp
    exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hp).1).2

def linkData (C : Completion S Data) : LinkData Roots Data where
  rootTriples := Finset.univ.powersetCard 3
  rootLink d := Finset.univ.powersetCard 2 \ (S.codes.missing (C.code d)).pairs
  dataLink := C.dataLink
  dataTriples := C.markers
  rootTriples_uniform := fun _p hp => (Finset.mem_powersetCard.mp hp).2
  rootLink_uniform := fun _d _p hp => (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hp).1).2
  dataLink_uniform := C.dataLink_uniform
  dataTriples_uniform := C.marker_uniform

def model (C : Completion S Data) : RootedModel Roots Data := C.linkData.model

@[simp] theorem model_rootTriples (C : Completion S Data) :
    C.model.rootTriples = Finset.univ.powersetCard 3 := C.linkData.model_rootTriples

@[simp] theorem model_rootLink (C : Completion S Data) (d : Data) :
    C.model.rootLink d = Finset.univ.powersetCard 2 \ (S.codes.missing (C.code d)).pairs :=
  C.linkData.model_rootLink d

@[simp] theorem model_dataLink (C : Completion S Data) (r : Roots) :
    C.model.dataLink r = C.dataLink r := C.linkData.model_dataLink r

@[simp] theorem model_dataTriples (C : Completion S Data) : C.model.dataTriples = C.markers :=
  C.linkData.model_dataTriples

theorem model_declared (C : Completion S Data) (hq : 0 < Fintype.card Roots) (d : Data) :
    S.codes.Declared C.model d (C.code d) := by
  have hc : S.codes.candidates C.model d =
      S.codes.candidates (baselineModel fun v => S.codes.missing (C.code v)) d := by
    ext c
    simp only [CodeSystem.mem_candidates, C.model_rootLink, baselineModel_rootLink]
  change S.codes.candidates C.model d = {C.code d}
  rw [hc]
  exact baselineModel_declared S.codes C.code hq d

theorem model_declared_iff (C : Completion S Data) (hq : 0 < Fintype.card Roots) (d : Data) (c : Code) :
    S.codes.Declared C.model d c ↔ c = C.code d := by
  constructor
  · exact fun hc => S.codes.declared_unique C.model d c (C.code d) hc (C.model_declared hq d)
  · rintro rfl
    exact C.model_declared hq d

theorem model_hasCandidates (C : Completion S Data) (hq : 0 < Fintype.card Roots) :
    S.codes.HasCandidates C.model := by
  intro d
  rw [C.model_declared hq d]
  exact Finset.singleton_nonempty _

theorem model_typeClass (C : Completion S Data) (hq : 0 < Fintype.card Roots) (k : Kinds) :
    S.typeClass C.model k = C.partition.block k := by
  ext d
  simp only [CompilerSignature.typeClass, CodeSystem.mem_typeVertices,
    C.model_declared_iff hq, mem_assignmentPartition]
  simp

theorem model_markerTypes (C : Completion S Data) (hq : 0 < Fintype.card Roots) : S.MarkerTypes C.model := by
  intro p hp d hd c hc
  have hcode := (C.model_declared_iff hq d c).mp hc
  rw [hcode]
  exact C.marker_type p (by simpa using hp) d hd

theorem model_relationCopy (C : Completion S Data) (hq : 0 < Fintype.card Roots)
    (e : Fin 3) (j : Fin L) : S.relationCopy C.model e j = (C.matching e).pairs := by
  ext p
  rcases p with ⟨a, b⟩
  rw [S.mem_relationCopy, C.model_typeClass hq, C.model_typeClass hq,
    ← C.model.mem_dataLink, C.model_dataLink, C.dataLink_copy]
  constructor
  · rintro ⟨ha, hb, hp⟩
    exact (C.partition.pair_mem_matchedLink_iff _ _ (S.source_ne_target e)
      (C.matching e) a b ha hb).mp hp
  · intro hp
    have ha := (C.matching e).left_mem _ hp
    have hb := (C.matching e).right_mem _ hp
    exact ⟨ha, hb, (C.partition.pair_mem_matchedLink_iff _ _ (S.source_ne_target e)
      (C.matching e) a b ha hb).mpr hp⟩

theorem model_unionRelation_subset (C : Completion S Data) (hq : 0 < Fintype.card Roots) (e : Fin 3) :
    S.unionRelation C.model e ⊆ (C.matching e).pairs := by
  intro p hp
  obtain ⟨j, hj⟩ := (S.mem_unionRelation C.model e p).mp hp
  simpa only [C.model_relationCopy hq] using hj

theorem model_unionRelation (C : Completion S Data) (hq : 0 < Fintype.card Roots) (hL : 0 < L)
    (e : Fin 3) : S.unionRelation C.model e = (C.matching e).pairs := by
  apply Finset.Subset.antisymm (C.model_unionRelation_subset hq e)
  intro p hp
  apply (S.mem_unionRelation C.model e p).mpr
  exact ⟨⟨0, hL⟩, by simpa only [C.model_relationCopy hq] using hp⟩

theorem model_matching (C : Completion S Data) (hq : 0 < Fintype.card Roots) (e : Fin 3) :
    S.IsMatching C.model e := by
  constructor
  · intro p hp q hq' heq
    exact (C.matching e).left_injective (C.model_unionRelation_subset hq e hp)
      (C.model_unionRelation_subset hq e hq') heq
  · intro p hp q hq' heq
    exact (C.matching e).right_injective (C.model_unionRelation_subset hq e hp)
      (C.model_unionRelation_subset hq e hq') heq

theorem model_oneRootRules (C : Completion S Data) (hq : 0 < Fintype.card Roots) : S.OneRootRules C.model := by
  intro r p hp a ha b hb hab c d hc hd hcd
  have hac : C.code a = c := ((C.model_declared_iff hq a c).mp hc).symm
  have hbd : C.code b = d := ((C.model_declared_iff hq b d).mp hd).symm
  have hpcard := C.model.dataLink_uniform r p hp
  have hpair : p = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
    · rw [hpcard, Finset.card_pair hab]
  have hwithin : p ∈ (C.partition.block (S.physical c)).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hpcard⟩
    rw [hpair]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_assignmentPartition]
    exact ⟨congrArg S.physical hac, (congrArg S.physical hbd).trans hcd.symm⟩
  by_cases hr : ∃ q : Fin 3 × Fin L, S.copyRoot q = r
  · obtain ⟨⟨e, j⟩, rfl⟩ := hr
    have hlink : p ∈ C.indexedLink e := by simpa using hp
    have hk := C.partition.matchedLink_same_type _ _ (S.source_ne_target e)
      (C.matching e) (S.physical c) p hlink hwithin
    refine ⟨⟨e, j, rfl⟩, ?_⟩
    unfold CompilerSignature.sourceKind CompilerSignature.targetKind at hk
    split_ifs at hk <;> tauto
  · have hcross : p ∈ C.partition.crossPairs := by
      rw [C.model_dataLink, C.dataLink_additional r hr] at hp
      exact hp
    exact False.elim (Finset.disjoint_left.mp (C.partition.cross_disjoint_within (S.physical c)) hcross hwithin)

theorem model_incidenceLegal (C : Completion S Data) (hq : 0 < Fintype.card Roots) : S.IncidenceLegal C.model where
  candidates := C.model_hasCandidates hq
  oneRoot := C.model_oneRootRules hq
  matching := C.model_matching hq
  oneMarker := by simpa using C.one_marker
  markerTypes := C.model_markerTypes hq

theorem model_marks (C : Completion S Data) (hq : 0 < Fintype.card Roots) :
    S.marks C.model = C.markers.biUnion id := by
  ext d
  simp only [CompilerSignature.marks, Finset.mem_filter, Finset.mem_univ, true_and,
    C.model_typeClass hq, mem_assignmentPartition, C.model_dataTriples, Finset.mem_biUnion, id_eq]
  constructor
  · exact fun h => h.2
  · rintro ⟨p, hp, hd⟩
    exact ⟨C.marker_type p hp d hd, p, hp, hd⟩

end Completion

end TuranUniversality.Weighted
