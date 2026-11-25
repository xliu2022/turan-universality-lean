module

public import TuranUniversality.Effective.ListOperations
public import TuranUniversality.Computation.MatchingSystem

/-! # Primitive-recursive finite relations, composition, and exact paths -/

@[expose] public section

namespace TuranUniversality.Effective

open Computation.MatchingSystem

abbrev RelationCode := List (ℕ × ℕ)

def composeRelation (r s : RelationCode) : RelationCode :=
  ((cartesian r s).filter fun p => p.1.2 = p.2.1).map fun p => (p.1.1, p.2.2)

theorem composeRelation_primrec : Primrec₂ composeRelation := by
  have hp : PrimrecPred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2 = p.2.1) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hm : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (p.1.1, p.2.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_map ((Primrec.listFilter hp).comp cartesian_primrec)
    (hm.comp Primrec.snd).to₂).to₂

@[simp] theorem mem_composeRelation (r s : RelationCode) (x z : ℕ) :
    (x, z) ∈ composeRelation r s ↔ ∃ y, (x, y) ∈ r ∧ (y, z) ∈ s := by
  simp only [composeRelation, List.mem_map, List.mem_filter, mem_cartesian,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨⟨hr, hs⟩, hbc⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    change b = c at hbc
    subst c
    exact ⟨b, hr, hs⟩
  · rintro ⟨y, hr, hs⟩
    exact ⟨((x, y), (y, z)), ⟨⟨hr, hs⟩, rfl⟩, rfl⟩

def nextVertices (r : RelationCode) (xs : List ℕ) : List ℕ :=
  (r.filter fun p => p.1 ∈ xs).map Prod.snd

theorem nextVertices_primrec : Primrec₂ nextVertices := by
  have hp : PrimrecRel (fun (xs : List ℕ) (p : ℕ × ℕ) => p.1 ∈ xs) :=
    list_mem_primrec.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  exact (Primrec.list_map ((filter_primrec hp).comp Primrec.snd Primrec.fst)
    (Primrec.snd.comp Primrec.snd).to₂).to₂

@[simp] theorem mem_nextVertices (r : RelationCode) (xs : List ℕ) (z : ℕ) :
    z ∈ nextVertices r xs ↔ ∃ y ∈ xs, (y, z) ∈ r := by
  simp only [nextVertices, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨y, b⟩, ⟨hr, hy⟩, rfl⟩
    exact ⟨y, hy, hr⟩
  · rintro ⟨y, hy, hr⟩
    exact ⟨(y, z), ⟨hr, hy⟩, rfl⟩

def reachableVertices (r : RelationCode) (x n : ℕ) : List ℕ :=
  (nextVertices r)^[n] [x]

theorem reachableVertices_primrec :
    Primrec (fun p : RelationCode × ℕ × ℕ => reachableVertices p.1 p.2.1 p.2.2) :=
  Primrec.nat_iterate (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
    (nextVertices_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem path_succ_tail {X : Type*} (r : X → X → Prop) (n : ℕ) (x z : X) :
    Path r (n + 1) x z ↔ ∃ y, Path r n x y ∧ r y z := by
  induction n generalizing x with
  | zero => simp [Computation.MatchingSystem.Path]
  | succ n ih =>
    constructor
    · rintro ⟨a, hxa, haz⟩
      obtain ⟨y, hay, hyz⟩ := (ih a).mp haz
      exact ⟨y, ⟨a, hxa, hay⟩, hyz⟩
    · rintro ⟨y, ⟨a, hxa, hay⟩, hyz⟩
      exact ⟨a, hxa, (ih a).mpr ⟨y, hay, hyz⟩⟩

/-- Exact path semantics, including the empty path and repeated vertices. -/
theorem mem_reachableVertices (r : RelationCode) (x n z : ℕ) :
    z ∈ reachableVertices r x n ↔ Path (fun a b => (a, b) ∈ r) n x z := by
  induction n generalizing z with
  | zero => simp [reachableVertices, Computation.MatchingSystem.Path, eq_comm]
  | succ n ih =>
    rw [reachableVertices, Function.iterate_succ_apply', mem_nextVertices, path_succ_tail]
    exact exists_congr fun y => and_congr (ih y) Iff.rfl

def CodePath (r : RelationCode) (n x z : ℕ) : Prop := z ∈ reachableVertices r x n

instance (r : RelationCode) (n x z : ℕ) : Decidable (CodePath r n x z) :=
  inferInstanceAs (Decidable (z ∈ reachableVertices r x n))

theorem codePath_primrec :
    PrimrecRel (fun (r : RelationCode) (p : ℕ × ℕ × ℕ) => CodePath r p.1 p.2.1 p.2.2) :=
  list_mem_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (reachableVertices_primrec.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))))

end TuranUniversality.Effective
