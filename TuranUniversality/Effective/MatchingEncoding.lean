module

public import TuranUniversality.Effective.RuleEncoding
public import TuranUniversality.Effective.RelationEncoding

/-! # Primitive-recursive data and queries for the actual three local relations -/

@[expose] public section

namespace TuranUniversality.Effective

open Computation.MatchingSystem

structure MatchingCode (Alphabet : Type*) where
  size : ℕ
  labels : List Alphabet
  jPairs : RelationCode
  rPairs : RelationCode
  sPairs : RelationCode
  marks : List ℕ
  deriving DecidableEq

abbrev MatchingTuple (Alphabet : Type*) :=
  ℕ × List Alphabet × RelationCode × RelationCode × RelationCode × List ℕ

def matchingEquiv {Alphabet : Type*} : MatchingCode Alphabet ≃ MatchingTuple Alphabet where
  toFun := fun c => (c.size, c.labels, c.jPairs, c.rPairs, c.sPairs, c.marks)
  invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv := fun c => by cases c; rfl
  right_inv := fun p => rfl

instance {Alphabet : Type*} [Primcodable Alphabet] : Primcodable (MatchingCode Alphabet) :=
  Primcodable.ofEquiv (MatchingTuple Alphabet) matchingEquiv

namespace MatchingCode

variable {Alphabet : Type*} [Primcodable Alphabet]

theorem tuple_primrec : Primrec (matchingEquiv (Alphabet := Alphabet)) := Primrec.of_equiv
theorem size_primrec : Primrec (size (Alphabet := Alphabet)) := Primrec.fst.comp tuple_primrec
theorem labels_primrec : Primrec (labels (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp tuple_primrec)
theorem jPairs_primrec : Primrec (jPairs (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp tuple_primrec))
theorem rPairs_primrec : Primrec (rPairs (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp tuple_primrec)))
theorem sPairs_primrec : Primrec (sPairs (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp tuple_primrec))))
theorem marks_primrec : Primrec (marks (Alphabet := Alphabet)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp tuple_primrec))))

def boundedRelation (n : ℕ) (r : RelationCode) : RelationCode :=
  r.filter fun p => p.1 < n ∧ p.2 < n

theorem boundedRelation_primrec : Primrec₂ boundedRelation := by
  exact filter_primrec ((Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).and
    (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd) Primrec.fst))

@[simp] theorem mem_boundedRelation (n : ℕ) (r : RelationCode) (x y : ℕ) :
    (x, y) ∈ boundedRelation n r ↔ (x, y) ∈ r ∧ x < n ∧ y < n := by
  simp [boundedRelation]

def J (c : MatchingCode Alphabet) := boundedRelation c.size c.jPairs
def R (c : MatchingCode Alphabet) := boundedRelation c.size c.rPairs
def S (c : MatchingCode Alphabet) := boundedRelation c.size c.sPairs
def horizontal (c : MatchingCode Alphabet) := composeRelation c.J c.R
def vertical (c : MatchingCode Alphabet) := composeRelation c.J c.S

theorem J_primrec : Primrec (J (Alphabet := Alphabet)) :=
  boundedRelation_primrec.comp size_primrec jPairs_primrec
theorem R_primrec : Primrec (R (Alphabet := Alphabet)) :=
  boundedRelation_primrec.comp size_primrec rPairs_primrec
theorem S_primrec : Primrec (S (Alphabet := Alphabet)) :=
  boundedRelation_primrec.comp size_primrec sPairs_primrec
theorem horizontal_primrec : Primrec (horizontal (Alphabet := Alphabet)) :=
  composeRelation_primrec.comp J_primrec R_primrec
theorem vertical_primrec : Primrec (vertical (Alphabet := Alphabet)) :=
  composeRelation_primrec.comp J_primrec S_primrec

def H (c : MatchingCode Alphabet) (x y : ℕ) : Prop := (x, y) ∈ c.horizontal
def V (c : MatchingCode Alphabet) (x y : ℕ) : Prop := (x, y) ∈ c.vertical

theorem H_primrec : PrimrecRel (fun (c : MatchingCode Alphabet) (p : ℕ × ℕ) => c.H p.1 p.2) :=
  list_mem_primrec.comp Primrec.snd (horizontal_primrec.comp Primrec.fst)
theorem V_primrec : PrimrecRel (fun (c : MatchingCode Alphabet) (p : ℕ × ℕ) => c.V p.1 p.2) :=
  list_mem_primrec.comp Primrec.snd (vertical_primrec.comp Primrec.fst)

theorem h_bound (c : MatchingCode Alphabet) {x y : ℕ} (h : c.H x y) : x < c.size ∧ y < c.size := by
  obtain ⟨b, hj, hr⟩ := (mem_composeRelation c.J c.R x y).mp h
  exact ⟨((mem_boundedRelation _ _ _ _).mp hj).2.1,
    ((mem_boundedRelation _ _ _ _).mp hr).2.2⟩

theorem v_bound (c : MatchingCode Alphabet) {x y : ℕ} (h : c.V x y) : x < c.size ∧ y < c.size := by
  obtain ⟨b, hj, hs⟩ := (mem_composeRelation c.J c.S x y).mp h
  exact ⟨((mem_boundedRelation _ _ _ _).mp hj).2.1,
    ((mem_boundedRelation _ _ _ _).mp hs).2.2⟩

variable [Inhabited Alphabet] [DecidableEq Alphabet]

def Lab (c : MatchingCode Alphabet) (x : ℕ) (a : Alphabet) : Prop :=
  ∃ b < c.size, (x, b) ∈ c.J ∧ c.labels.getD b default = a

instance (c : MatchingCode Alphabet) (x : ℕ) (a : Alphabet) : Decidable (c.Lab x a) := by
  unfold Lab
  infer_instance

theorem Lab_primrec :
    PrimrecRel (fun (c : MatchingCode Alphabet) (p : ℕ × Alphabet) => c.Lab p.1 p.2) := by
  apply bounded_exists_primrec (size_primrec.comp Primrec.fst)
  exact (list_mem_primrec.comp
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (J_primrec.comp (Primrec.fst.comp Primrec.fst))).and
    (Primrec.eq.comp
      ((Primrec.list_getD default).comp (labels_primrec.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

def HasPath (c : MatchingCode Alphabet) (n x z : ℕ) : Prop := CodePath c.horizontal n x z

theorem HasPath_primrec : PrimrecRel
    (fun (c : MatchingCode Alphabet) (p : ℕ × ℕ × ℕ) => c.HasPath p.1 p.2.1 p.2.2) :=
  codePath_primrec.comp (horizontal_primrec.comp Primrec.fst) Primrec.snd

/-- The code data agree with the literal finite carrier and its actual partial
matchings.  No legality or halting conclusion is included in this interface. -/
structure Represents (c : MatchingCode Alphabet) (A : Realization (Fin c.size) Alphabet) : Prop where
  j : ∀ x y, (x.val, y.val) ∈ c.J ↔ (x, y) ∈ A.J.pairs
  r : ∀ x y, (x.val, y.val) ∈ c.R ↔ (x, y) ∈ A.R.pairs
  s : ∀ x y, (x.val, y.val) ∈ c.S ↔ (x, y) ∈ A.S.pairs
  label : ∀ x, c.labels.getD x.val default = A.label x
  mark : ∀ x, x.val ∈ c.marks ↔ x ∈ A.marks

namespace Represents

variable {c : MatchingCode Alphabet} {A : Realization (Fin c.size) Alphabet} (h : c.Represents A)

include h

theorem H_iff (x y : Fin c.size) : c.H x.val y.val ↔ A.H x y := by
  rw [H, horizontal, mem_composeRelation]
  constructor
  · rintro ⟨b, hj, hr⟩
    have hb := ((mem_boundedRelation _ _ _ _).mp hj).2.2
    exact ⟨⟨b, hb⟩, (h.j x ⟨b, hb⟩).mp hj, (h.r ⟨b, hb⟩ y).mp hr⟩
  · rintro ⟨b, hj, hr⟩
    exact ⟨b.val, (h.j x b).mpr hj, (h.r b y).mpr hr⟩

theorem V_iff (x y : Fin c.size) : c.V x.val y.val ↔ A.V x y := by
  rw [V, vertical, mem_composeRelation]
  constructor
  · rintro ⟨b, hj, hs⟩
    have hb := ((mem_boundedRelation _ _ _ _).mp hj).2.2
    exact ⟨⟨b, hb⟩, (h.j x ⟨b, hb⟩).mp hj, (h.s ⟨b, hb⟩ y).mp hs⟩
  · rintro ⟨b, hj, hs⟩
    exact ⟨b.val, (h.j x b).mpr hj, (h.s b y).mpr hs⟩

theorem Lab_iff (x : Fin c.size) (a : Alphabet) : c.Lab x.val a ↔ A.Lab x a := by
  constructor
  · rintro ⟨b, hb, hj, hl⟩
    exact ⟨⟨b, hb⟩, (h.j x ⟨b, hb⟩).mp hj, (h.label ⟨b, hb⟩).symm.trans hl⟩
  · rintro ⟨b, hj, hl⟩
    exact ⟨b.val, b.isLt, (h.j x b).mpr hj, (h.label b).trans hl⟩

theorem Path_iff (n : ℕ) (x y : Fin c.size) :
    c.HasPath n x.val y.val ↔ Computation.MatchingSystem.Path A.H n x y := by
  change y.val ∈ reachableVertices c.horizontal x.val n ↔ _
  rw [mem_reachableVertices]
  induction n generalizing x with
  | zero => exact Fin.val_injective.eq_iff
  | succ n ih =>
    constructor
    · rintro ⟨b, hxb, hby⟩
      have hb := (c.h_bound hxb).2
      exact ⟨⟨b, hb⟩, (h.H_iff x ⟨b, hb⟩).mp hxb, (ih ⟨b, hb⟩).mp hby⟩
    · rintro ⟨b, hxb, hby⟩
      exact ⟨b.val, (h.H_iff x b).mpr hxb, (ih b).mpr hby⟩

end Represents
end MatchingCode
end TuranUniversality.Effective
