module

public import TuranUniversality.Effective.StructuralLabels
public import TuranUniversality.Effective.UniformChecksPrimrec

@[expose] public section

/-! # Primitive recursion of the finite legal-object tests -/

namespace TuranUniversality.Effective.StructuralCodes

open Uniform Structural

set_option maxRecDepth 5000

theorem supported_primrec : PrimrecRel (fun p : ℕ × List (List ℕ) => Supported p.1 p.2) :=
  forall_mem_primrec (allRows_primrec.comp (Primrec.const (3)) (Primrec.fst.comp (Primrec.fst))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.const (3)) (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd)) (forall_mem_primrec (Primrec.snd) (list_mem_primrec.comp (Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))))

theorem imageActive_primrec : PrimrecRel (fun p : ℕ × List ℕ => ImageActive p.1 p.2) :=
  bounded_forall_primrec (Primrec.fst.comp (Primrec.fst)) (list_mem_primrec.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd)) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))

theorem activeFree_primrec : PrimrecRel (fun p : List Code × ℕ × List (List ℕ) => ActiveFree p.1 p.2.1 p.2.2) :=
  forall_mem_primrec (Primrec.fst.comp (Primrec.fst)) (forall_mem_primrec (assignments_primrec.comp (Primrec.snd) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))) (implication_primrec (imageActive_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd)) (((injectiveAssignment_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd)).and (homAssignment_primrec.comp (Primrec.pair (Primrec.const (3)) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))))))) (Primrec.snd))).not)))

theorem legal_primrec : PrimrecRel (fun p : List Code × ℕ => Legal p.1 p.2) :=
  (supported_primrec.comp (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd)))) (Primrec.fst.comp (Primrec.snd))).and ((supported_primrec.comp (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd)))) (Primrec.fst.comp (Primrec.snd))).and (((edgeless_primrec.comp (Primrec.const (3)) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd))))).or (edgeless_primrec.comp (Primrec.const (3)) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd)))))).and ((activeFree_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd))))) (Primrec.fst.comp (Primrec.snd))).and (activeFree_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd))))) (Primrec.fst.comp (Primrec.snd))))))

theorem objectCodes_primrec : Primrec objectCodes :=
  Primrec.list_flatMap subsetRows_primrec
    (Primrec.list_flatMap (sublists_primrec.comp
      (allRows_primrec.comp (Primrec.const 3) Primrec.fst))
      (Primrec.list_map (sublists_primrec.comp
        (allRows_primrec.comp (Primrec.const 3) (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂).to₂

theorem labelCount_primrec : Primrec labelCount :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 5)) Primrec.id (Primrec.const 3)

theorem iff_primrec {A : Type*} [Primcodable A] {P Q : A → Prop}
    (hP : PrimrecPred P) (hQ : PrimrecPred Q) : PrimrecPred (fun a => P a ↔ Q a) :=
  ((implication_primrec hP hQ).and (implication_primrec hQ hP)).of_eq
    (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem labels_primrec : PrimrecRel (fun p : ℕ × ObjectCode × List ℕ => Labels p.1 p.2.1 p.2.2) :=
  (Primrec.eq.comp (Primrec.list_length.comp (intersectionRow_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))))) (labelCount_primrec.comp (Primrec.snd))).and ((iff_primrec (edge_primrec.comp (Primrec.pair (Primrec.const (3)) (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))))))) (intersectionRow_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))))) (Primrec.eq.comp (Primrec.snd) (Primrec.const (5)))).and (iff_primrec (edge_primrec.comp (Primrec.pair (Primrec.const (3)) (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))))))) (intersectionRow_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))))) (Primrec.eq.comp (Primrec.snd) (Primrec.const (6)))))

end TuranUniversality.Effective.StructuralCodes
