module

public import TuranUniversality.Effective.GraphBuild
public import TuranUniversality.Selector.CompatibleProfiles
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # Primitive-recursive finite products of graph codes -/

namespace TuranUniversality.Effective

set_option backward.isDefEq.respectTransparency false

def tripleDiv (n : ℕ) (t : Triple) : Triple := (t.1 / n, t.2.1 / n, t.2.2 / n)
def tripleMod (n : ℕ) (t : Triple) : Triple := (t.1 % n, t.2.1 % n, t.2.2 % n)

theorem tripleDiv_primrec : Primrec₂ tripleDiv :=
  (Primrec.pair (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
    (Primrec.pair (Primrec.nat_div.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
      (Primrec.nat_div.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst))).to₂

theorem tripleMod_primrec : Primrec₂ tripleMod :=
  (Primrec.pair (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
    (Primrec.pair (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
      (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst))).to₂

def ProductEdge (p : GraphCode × GraphCode) (t : Triple) : Prop :=
  CodeEdge p.1 (tripleDiv p.2.1 t) ∧ CodeEdge p.2 (tripleMod p.2.1 t)

instance (p : GraphCode × GraphCode) (t : Triple) : Decidable (ProductEdge p t) := by
  unfold ProductEdge
  infer_instance

theorem productEdge_primrec : PrimrecRel ProductEdge := by
  have hg : Primrec (fun p : (GraphCode × GraphCode) × Triple => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hh : Primrec (fun p : (GraphCode × GraphCode) × Triple => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hn : Primrec (fun p : (GraphCode × GraphCode) × Triple => p.1.2.1) :=
    Primrec.fst.comp hh
  exact (codeEdge_primrec.comp hg (tripleDiv_primrec.comp hn Primrec.snd)).and
    (codeEdge_primrec.comp hh (tripleMod_primrec.comp hn Primrec.snd))

def binaryProductCode (g h : GraphCode) : GraphCode :=
  predicateGraphCode (g.1 * h.1) (ProductEdge (g, h))

theorem binaryProductCode_primrec : Primrec₂ binaryProductCode := by
  have hn : Primrec (fun p : GraphCode × GraphCode => p.1.1 * p.2.1) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  exact (Primrec.pair hn ((filter_primrec productEdge_primrec).comp Primrec.id
    (allTriples_primrec.comp hn))).to₂

def productLeft (g h : GraphCode) (x : Fin (g.1 * h.1)) : Fin g.1 :=
  (finProdFinEquiv.symm x).1

def productRight (g h : GraphCode) (x : Fin (g.1 * h.1)) : Fin h.1 :=
  (finProdFinEquiv.symm x).2

def binaryProductGraph (g h : GraphCode) : RGraph (Fin (g.1 * h.1)) 3 where
  edges := (Finset.univ.powersetCard 3).filter fun e =>
    e.image (productLeft g h) ∈ (decodeGraph g).edges ∧
    e.image (productRight g h) ∈ (decodeGraph h).edges
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

theorem mem_binaryProductGraph (g h : GraphCode) (e : Finset (Fin (g.1 * h.1))) :
    e ∈ (binaryProductGraph g h).edges ↔ e.card = 3 ∧
      e.image (productLeft g h) ∈ (decodeGraph g).edges ∧
      e.image (productRight g h) ∈ (decodeGraph h).edges := by
  simp [binaryProductGraph, Finset.mem_powersetCard]

theorem decode_binaryProductCode (g h : GraphCode) :
    decodeGraph (binaryProductCode g h) = binaryProductGraph g h := by
  apply decode_predicateGraphCode
  intro a b c
  change (CodeEdge g ((productLeft g h a).val, (productLeft g h b).val, (productLeft g h c).val) ∧
      CodeEdge h ((productRight g h a).val, (productRight g h b).val, (productRight g h c).val)) ↔ _
  rw [codeEdge_iff, codeEdge_iff, mem_binaryProductGraph]
  simp only [Finset.image_insert, Finset.image_singleton]
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, hleft, hright⟩
    have hc := (decodeGraph g).uniform _ hleft
    have hle := Finset.card_image_le (s := {a, b, c}) (f := productLeft g h)
    simp only [Finset.image_insert, Finset.image_singleton] at hle
    exact le_antisymm Finset.card_le_three (by omega)
  · exact fun h => h.2

theorem binaryProductCode_left (g h : GraphCode) :
    (decodeGraph (binaryProductCode g h)).IsHom (decodeGraph g) (productLeft g h) := by
  rw [decode_binaryProductCode]
  intro e he
  exact ((mem_binaryProductGraph g h e).mp he).2.1

theorem binaryProductCode_right (g h : GraphCode) :
    (decodeGraph (binaryProductCode g h)).IsHom (decodeGraph h) (productRight g h) := by
  rw [decode_binaryProductCode]
  intro e he
  exact ((mem_binaryProductGraph g h e).mp he).2.2

theorem binaryProductCode_lift {V : Type*} [DecidableEq V]
    (K : RGraph V 3) (g h : GraphCode)
    (f : V → Fin g.1) (j : V → Fin h.1)
    (hf : K.IsHom (decodeGraph g) f) (hj : K.IsHom (decodeGraph h) j) :
    K.IsHom (decodeGraph (binaryProductCode g h)) (fun v => finProdFinEquiv (f v, j v)) := by
  rw [decode_binaryProductCode]
  apply RGraph.isHom_of_triples
  intro a b c he
  rw [mem_binaryProductGraph]
  have hleft := hf _ he
  have hright := hj _ he
  have hproj (v : V) : productLeft g h (finProdFinEquiv (f v, j v)) = f v :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (f v, j v))
  have hproj' (v : V) : productRight g h (finProdFinEquiv (f v, j v)) = j v :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (f v, j v))
  simp only [Finset.image_insert, Finset.image_singleton] at hleft hright ⊢
  simp only [hproj, hproj']
  refine ⟨?_, hleft, hright⟩
  have habc := Finset.card_triple_eq_three_iff.mp ((decodeGraph g).uniform _ hleft)
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨fun heq => habc.1 (by simpa only [hproj] using congrArg (productLeft g h) heq),
    fun heq => habc.2.1 (by simpa only [hproj] using congrArg (productLeft g h) heq),
    fun heq => habc.2.2 (by simpa only [hproj] using congrArg (productLeft g h) heq)⟩

end TuranUniversality.Effective
