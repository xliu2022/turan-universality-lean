module

public import TuranUniversality.Effective.GraphRelations
public import TuranUniversality.Effective.MatchingEncoding
public import TuranUniversality.Selector.RootedWitnesses
public import TuranUniversality.Selector.Admissibility

/-! # Literal finite codes for partial root assignments and rooted edges -/

@[expose] public section

namespace TuranUniversality.Effective

open Weighted Selector Computation.MatchingSystem

abbrev RootedCode (Roots : Type*) := GraphCode × List (Option Roots)

namespace RootedCode

variable {Roots : Type*} [Fintype Roots] [DecidableEq Roots] [Primcodable Roots]

abbrev size (c : RootedCode Roots) : ℕ := c.1.1
def assignment (c : RootedCode Roots) (x : ℕ) : Option Roots := c.2.getD x none

theorem size_primrec : Primrec (size (Roots := Roots)) := Primrec.fst.comp Primrec.fst
theorem assignment_primrec : Primrec₂ (assignment (Roots := Roots)) :=
  (Primrec.list_getD none).comp (Primrec.snd.comp Primrec.fst) Primrec.snd

/-- A list represents an injective partial assignment on the actual graph
vertices. Entries beyond the vertex count are ignored. -/
def Valid (c : RootedCode Roots) : Prop :=
  ∀ x < c.size, ∀ y < c.size, ∀ r,
    c.assignment x = some r → c.assignment y = some r → x = y

instance (c : RootedCode Roots) : Decidable c.Valid := by
  unfold Valid
  infer_instance

def rooting (c : RootedCode Roots) (h : c.Valid) : VertexRooting Roots (Fin c.size) :=
  ⟨fun x => c.assignment x.val, fun x y r hx hy => Fin.ext (h x.val x.isLt y.val y.isLt r hx hy)⟩

def model (c : RootedCode Roots) (h : c.Valid) : RootedModel Roots (Fin c.size) :=
  rootedImage (decodeGraph c.1) (c.rooting h).val (c.rooting h).property

def RootPairEdge (c : RootedCode Roots) (r s : Roots) (x : ℕ) : Prop :=
  c.assignment x = none ∧ ∃ y < c.size, ∃ z < c.size,
    c.assignment y = some r ∧ c.assignment z = some s ∧ CodeEdge c.1 (y, z, x)

def RootEdge (c : RootedCode Roots) (r : Roots) (x y : ℕ) : Prop :=
  c.assignment x = none ∧ c.assignment y = none ∧ ∃ z < c.size,
    c.assignment z = some r ∧ CodeEdge c.1 (z, x, y)

def DataEdge (c : RootedCode Roots) (x y z : ℕ) : Prop :=
  c.assignment x = none ∧ c.assignment y = none ∧ c.assignment z = none ∧
    CodeEdge c.1 (x, y, z)

instance (c : RootedCode Roots) (r s : Roots) (x : ℕ) : Decidable (c.RootPairEdge r s x) := by
  unfold RootPairEdge
  infer_instance

instance (c : RootedCode Roots) (r : Roots) (x y : ℕ) : Decidable (c.RootEdge r x y) := by
  unfold RootEdge
  infer_instance

instance (c : RootedCode Roots) (x y z : ℕ) : Decidable (c.DataEdge x y z) := by
  unfold DataEdge
  infer_instance

/-- Numeric two-root edge queries are exactly the actual root-pair links. -/
theorem rootPairEdge_iff (c : RootedCode Roots) (h : c.Valid) (r s : Roots) (x : Fin c.size) :
    c.RootPairEdge r s x.val ↔ ({r, s}, {x}) ∈ (c.model h).edges := by
  constructor
  · rintro ⟨hx, y, hy, z, hz, hyr, hzs, he⟩
    let y' : Fin c.size := ⟨y, hy⟩
    let z' : Fin c.size := ⟨z, hz⟩
    have he' : {y', z', x} ∈ (decodeGraph c.1).edges := (codeEdge_iff c.1 y' z' x).mp he
    apply (split_edge_mem_iff _ _ _).mpr
    rw [model, rootedImage_toRGraph, two_root_disjSum]
    have him := (rootedGraph_embedding (decodeGraph c.1)
      (c.rooting h).val (c.rooting h).property).2 _ he'
    simpa [rooting, rootedVertex, y', z', hyr, hzs, hx] using him
  · intro he
    obtain ⟨y, z, hy, hz, hx, he'⟩ := two_root_edge_witness (decodeGraph c.1)
      (c.rooting h).val (c.rooting h).property r s x he
    exact ⟨hx, y.val, y.isLt, z.val, z.isLt, hy, hz, (codeEdge_iff c.1 y z x).mpr he'⟩

/-- Numeric one-root edge queries are exactly the actual data links. -/
theorem rootEdge_iff (c : RootedCode Roots) (h : c.Valid) (r : Roots) (x y : Fin c.size) :
    c.RootEdge r x.val y.val ↔ ({r}, {x, y}) ∈ (c.model h).edges := by
  constructor
  · rintro ⟨hx, hy, z, hz, hzr, he⟩
    let z' : Fin c.size := ⟨z, hz⟩
    have he' : {z', x, y} ∈ (decodeGraph c.1).edges := (codeEdge_iff c.1 z' x y).mp he
    apply (split_edge_mem_iff _ _ _).mpr
    rw [model, rootedImage_toRGraph, one_root_disjSum]
    have him := (rootedGraph_embedding (decodeGraph c.1)
      (c.rooting h).val (c.rooting h).property).2 _ he'
    simpa [rooting, rootedVertex, z', hzr, hx, hy] using him
  · intro he
    obtain ⟨z, hz, hx, hy, he'⟩ := one_root_edge_witness (decodeGraph c.1)
      (c.rooting h).val (c.rooting h).property r x y he
    exact ⟨hx, hy, z.val, z.isLt, hz, (codeEdge_iff c.1 z x y).mpr he'⟩

/-- Numeric data-triple queries are exactly the actual marker edges. -/
theorem dataEdge_iff (c : RootedCode Roots) (h : c.Valid) (x y z : Fin c.size) :
    c.DataEdge x.val y.val z.val ↔ (∅, {x, y, z}) ∈ (c.model h).edges := by
  constructor
  · rintro ⟨hx, hy, hz, he⟩
    have he' : {x, y, z} ∈ (decodeGraph c.1).edges := (codeEdge_iff c.1 x y z).mp he
    apply (split_edge_mem_iff _ _ _).mpr
    rw [model, rootedImage_toRGraph, zero_root_disjSum]
    have him := (rootedGraph_embedding (decodeGraph c.1)
      (c.rooting h).val (c.rooting h).property).2 _ he'
    simpa [rooting, rootedVertex, hx, hy, hz] using him
  · intro he
    obtain ⟨hx, hy, hz, he'⟩ := data_edge_witness (decodeGraph c.1)
      (c.rooting h).val (c.rooting h).property x y z he
    exact ⟨hx, hy, hz, (codeEdge_iff c.1 x y z).mpr he'⟩

theorem rootPairEdge_bound (c : RootedCode Roots) {r s : Roots} {x : ℕ}
    (h : c.RootPairEdge r s x) : x < c.size := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := h
  exact h.1.2.2.1

theorem rootEdge_bound (c : RootedCode Roots) {r : Roots} {x y : ℕ}
    (h : c.RootEdge r x y) : x < c.size ∧ y < c.size := by
  obtain ⟨_, _, _, _, _, h⟩ := h
  exact ⟨h.1.2.1, h.1.2.2.1⟩

theorem dataEdge_bound (c : RootedCode Roots) {x y z : ℕ}
    (h : c.DataEdge x y z) : x < c.size ∧ y < c.size ∧ z < c.size :=
  ⟨h.2.2.2.1.1, h.2.2.2.1.2.1, h.2.2.2.1.2.2.1⟩

variable {Code Kinds : Type*} {L : ℕ}
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]

def Candidate (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (a : Code) : Prop :=
  ∀ r s, {r, s} ∈ (S.codes.missing a).pairs → ¬ c.RootPairEdge r s x

def Declared (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (a : Code) : Prop :=
  Candidate S c x a ∧ ∀ b, Candidate S c x b → b = a

def HasType (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (kind : Kinds) : Prop :=
  ∃ a, Declared S c x a ∧ S.physical a = kind

def Relation (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (e : Fin 3) (x y : ℕ) : Prop :=
  HasType S c x (S.sourceKind e) ∧ HasType S c y (S.targetKind e) ∧
    ∃ j, c.RootEdge (S.copyRoot (e, j)) x y

def Marked (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) : Prop :=
  HasType S c x S.cellKind ∧ ∃ y < c.size, ∃ z < c.size, c.DataEdge x y z

instance (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (a : Code) : Decidable (Candidate S c x a) := by
  unfold Candidate
  infer_instance

instance (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (a : Code) : Decidable (Declared S c x a) := by
  unfold Declared
  infer_instance

instance (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (kind : Kinds) : Decidable (HasType S c x kind) := by
  unfold HasType
  infer_instance

instance (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (e : Fin 3) (x y : ℕ) : Decidable (Relation S c e x y) := by
  unfold Relation
  infer_instance

instance (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) : Decidable (Marked S c x) := by
  unfold Marked
  infer_instance

theorem candidate_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) (x : Fin c.size) (a : Code) :
    Candidate S c x.val a ↔ a ∈ S.codes.candidates (c.model h) x := by
  rw [S.codes.mem_candidates]
  constructor
  · intro hc
    apply Finset.disjoint_left.mpr
    intro p hp hpa
    obtain ⟨r, s, _, rfl⟩ := Finset.card_eq_two.mp ((S.codes.missing a).pair_card p hpa)
    exact hc r s hpa ((c.rootPairEdge_iff h r s x).mpr
      (((c.model h).mem_rootLink x {r, s}).mp hp))
  · intro hd r s hrs he
    exact Finset.disjoint_left.mp hd
      (((c.model h).mem_rootLink x {r, s}).mpr ((c.rootPairEdge_iff h r s x).mp he)) hrs

theorem declared_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) (x : Fin c.size) (a : Code) :
    Declared S c x.val a ↔ S.codes.Declared (c.model h) x a := by
  unfold Declared CodeSystem.Declared
  simp only [candidate_iff S c h]
  constructor
  · intro ha
    ext b
    simp only [Finset.mem_singleton]
    exact ⟨ha.2 b, fun hb => hb ▸ ha.1⟩
  · intro ha
    rw [ha]
    simp

theorem hasType_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) (x : Fin c.size) (kind : Kinds) :
    HasType S c x.val kind ↔ x ∈ S.typeClass (c.model h) kind := by
  simp only [HasType, CompilerSignature.typeClass, CodeSystem.mem_typeVertices,
    declared_iff S c h]

theorem relation_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) (e : Fin 3) (x y : Fin c.size) :
    Relation S c e x.val y.val ↔ (x, y) ∈ S.unionRelation (c.model h) e := by
  simp only [Relation, hasType_iff S c h, rootEdge_iff c h,
    CompilerSignature.mem_unionRelation, CompilerSignature.mem_relationCopy]
  exact ⟨fun h => ⟨h.2.2.choose, h.1, h.2.1, h.2.2.choose_spec⟩,
    fun ⟨j, hx, hy, he⟩ => ⟨hx, hy, j, he⟩⟩

theorem marked_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) (x : Fin c.size) : Marked S c x.val ↔ x ∈ S.marks (c.model h) := by
  simp only [Marked, CompilerSignature.marks, Finset.mem_filter, Finset.mem_univ,
    true_and, hasType_iff S c h]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨y, hy, z, hz, he⟩
    exact ⟨{x, ⟨y, hy⟩, ⟨z, hz⟩}, ((c.model h).mem_dataTriples _).mpr
      ((c.dataEdge_iff h x ⟨y, hy⟩ ⟨z, hz⟩).mp he), by simp⟩
  · rintro ⟨p, hp, hx⟩
    obtain ⟨a, b, d, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((c.model h).dataTriples_uniform p hp)
    have he := ((c.model h).mem_dataTriples _).mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨b.val, b.isLt, d.val, d.isLt, (c.dataEdge_iff h x b d).mpr he⟩
    · exact ⟨a.val, a.isLt, d.val, d.isLt,
        (c.dataEdge_iff h x a d).mpr (by simpa only [Finset.insert_comm] using he)⟩
    · exact ⟨a.val, a.isLt, b.val, b.isLt,
        (c.dataEdge_iff h x a b).mpr (by convert he using 1 <;> ext v <;> simp; tauto)⟩

theorem declared_unique (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) (a b : Code) (ha : Declared S c x a) (hb : Declared S c x b) : a = b :=
  hb.2 a ha.1

noncomputable def declaredCodes (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (x : ℕ) : List Code :=
  Finset.univ.toList.filter fun a => Declared S c x a

@[simp] theorem mem_declaredCodes (S : CompilerSignature Roots Code Kinds L)
    (c : RootedCode Roots) (x : ℕ) (a : Code) :
    a ∈ declaredCodes S c x ↔ Declared S c x a := by
  simp [declaredCodes]

variable {Alphabet : Type*} [Inhabited Alphabet]

noncomputable def label (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (x : ℕ) : Alphabet :=
  ((declaredCodes S c x).head?.map color).getD default

theorem label_eq (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) (h : c.Valid) (x : Fin c.size) :
    label S color c x.val = decodedLabel S (c.model h) color x := by
  by_cases hex : ∃ a, Declared S c x.val a
  · obtain ⟨a, ha⟩ := hex
    rw [decodedLabel_of_declared S (c.model h) color x a ((declared_iff S c h x a).mp ha)]
    have hmem := (mem_declaredCodes S c x.val a).mpr ha
    unfold label
    generalize hlist : declaredCodes S c x.val = xs at hmem ⊢
    cases xs with
    | nil => simp at hmem
    | cons b bs =>
        have hb : Declared S c x.val b :=
          (mem_declaredCodes S c x.val b).mp (hlist.symm ▸ (by simp : b ∈ b :: bs))
        have hba := declared_unique S c x.val b a hb ha
        simp [hba]
  · have hnil : declaredCodes S c x.val = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      exact hex ⟨a, (mem_declaredCodes S c x.val a).mp ha⟩
    have hnone : ¬ ∃ a, S.codes.Declared (c.model h) x a := by
      simpa only [← declared_iff S c h] using hex
    simp [label, hnil, decodedLabel, hnone]

def relationList (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (e : Fin 3) : RelationCode :=
  (cartesian (List.range c.size) (List.range c.size)).filter fun p => Relation S c e p.1 p.2

def markedList (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) : List ℕ :=
  (List.range c.size).filter fun x => Marked S c x

noncomputable def matchingCode (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (c : RootedCode Roots) : MatchingCode Alphabet where
  size := c.size
  labels := (List.range c.size).map (label S color c)
  jPairs := relationList S c 0
  rPairs := relationList S c 1
  sPairs := relationList S c 2
  marks := markedList S c

variable [Primcodable Alphabet] [DecidableEq Alphabet]

set_option backward.isDefEq.respectTransparency false in
/-- The finite list extraction describes precisely the actual matching
realization read from the rooted graph, including labels and marker vertices. -/
theorem matchingCode_represents (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (c : RootedCode Roots) (h : c.Valid)
    (hm : ∀ e, S.IsMatching (c.model h) e) :
    (matchingCode S color c).Represents (rootedRealization S (c.model h) color hm) := by
  have hrel (e : Fin 3) (x y : Fin c.size) :
      (x.val, y.val) ∈ MatchingCode.boundedRelation c.size (relationList S c e) ↔
        (x, y) ∈ S.unionRelation (c.model h) e := by
    simp only [MatchingCode.mem_boundedRelation, relationList, List.mem_filter,
      mem_cartesian, List.mem_range, x.isLt, y.isLt, and_self, true_and,
      decide_eq_true_eq, and_true, relation_iff S c h]
  refine ⟨hrel 0, hrel 1, hrel 2, ?_, ?_⟩
  · intro x
    change ((List.range c.size).map (label S color c)).getD x.val default = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact x.isLt), List.getElem_map,
      List.getElem_range]
    exact label_eq S color c h x
  · intro x
    have hx : x.val < c.size := x.isLt
    change x.val ∈ markedList S c ↔ x ∈ S.marks (c.model h)
    simpa only [markedList, List.mem_filter, List.mem_range, hx, true_and,
      decide_eq_true_eq] using marked_iff S c h x

end RootedCode
end TuranUniversality.Effective
