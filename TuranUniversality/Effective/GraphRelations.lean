module

public import TuranUniversality.Effective.GraphEncoding

/-! # Primitive-recursive edge queries on actual finite graph codes -/

@[expose] public section

namespace TuranUniversality.Effective

def tripleList (t : Triple) : List ℕ := [t.1, t.2.1, t.2.2]

theorem tripleList_primrec : Primrec tripleList :=
  Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))

def SameTriple (t s : Triple) : Prop :=
  tripleList t ⊆ tripleList s ∧ tripleList s ⊆ tripleList t

instance (t s : Triple) : Decidable (SameTriple t s) :=
  inferInstanceAs (Decidable (tripleList t ⊆ tripleList s ∧ tripleList s ⊆ tripleList t))

theorem sameTriple_primrec : PrimrecRel SameTriple := by
  have hsub : PrimrecRel (fun (xs ys : List ℕ) => xs ⊆ ys) :=
    list_mem_primrec.forall_mem_list
  exact (hsub.comp (tripleList_primrec.comp Primrec.fst)
    (tripleList_primrec.comp Primrec.snd)).and
    (hsub.comp (tripleList_primrec.comp Primrec.snd)
      (tripleList_primrec.comp Primrec.fst))

theorem sameTriple_iff (t s : Triple) : SameTriple t s ↔ tripleSet t = tripleSet s := by
  have ht : (tripleList t).toFinset = tripleSet t := by simp [tripleList, tripleSet]
  have hs : (tripleList s).toFinset = tripleSet s := by simp [tripleList, tripleSet]
  rw [← ht, ← hs]
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · intro a ha
      exact List.mem_toFinset.mpr (h.1 (List.mem_toFinset.mp ha))
    · intro a ha
      exact List.mem_toFinset.mpr (h.2 (List.mem_toFinset.mp ha))
  · intro h
    constructor <;> intro a ha
    · exact List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr ha)
    · exact List.mem_toFinset.mp (h.symm ▸ List.mem_toFinset.mpr ha)

def WellTriple (n : ℕ) (t : Triple) : Prop :=
  t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n ∧
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance (n : ℕ) (t : Triple) : Decidable (WellTriple n t) := by unfold WellTriple; infer_instance

theorem wellTriple_primrec : PrimrecRel WellTriple := by
  have ha : Primrec (fun p : ℕ × Triple => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : ℕ × Triple => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : ℕ × Triple => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.nat_lt.comp ha Primrec.fst).and
    ((Primrec.nat_lt.comp hb Primrec.fst).and
      ((Primrec.nat_lt.comp hc Primrec.fst).and
        ((Primrec.eq.comp ha hb).not.and
          ((Primrec.eq.comp ha hc).not.and (Primrec.eq.comp hb hc).not))))

/-- A query for one actual unordered edge, with all malformed triples rejected. -/
def CodeEdge (g : GraphCode) (t : Triple) : Prop :=
  WellTriple g.1 t ∧ ∃ s ∈ g.2, SameTriple t s

instance (g : GraphCode) (t : Triple) : Decidable (CodeEdge g t) := by
  unfold CodeEdge
  infer_instance

theorem codeEdge_primrec : PrimrecRel CodeEdge :=
  (wellTriple_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).and
    (sameTriple_primrec.swap.exists_mem_list.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem wellTriple_fin_iff {n : ℕ} (a b c : Fin n) :
    WellTriple n (a.val, b.val, c.val) ↔ ({a, b, c} : Finset (Fin n)).card = 3 := by
  simp only [WellTriple, a.isLt, b.isLt, c.isLt, true_and]
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
    simp_all [Fin.ext_iff]

/-- Code-level edge testing agrees exactly with the actual decoded graph. -/
theorem codeEdge_iff (g : GraphCode) (a b c : Fin g.1) :
    CodeEdge g (a.val, b.val, c.val) ↔ {a, b, c} ∈ (decodeGraph g).edges := by
  rw [CodeEdge, mem_decodeGraph, wellTriple_fin_iff]
  simp only [sameTriple_iff, tripleSet, Finset.image_insert, Finset.image_singleton]

end TuranUniversality.Effective
