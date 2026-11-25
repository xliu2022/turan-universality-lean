module

public import TuranUniversality.Effective.StructuralLocalChecks
public import TuranUniversality.Effective.StructuralEdgesPrimrec

@[expose] public section

/-! # Primitive recursion for the actual finite structural tests -/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform Structural

set_option maxRecDepth 6000

theorem allGood_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × Code => AllGood Ω p.1 p.2) :=
  forall_mem_primrec (allRows_primrec.comp (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.const ((3 * b + 4)))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.const ((3 * b + 4)))) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd)) ((goodEdge_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst))) (Primrec.snd)))

theorem localOn_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × List Code × Code × List ℕ => LocalOn Ω p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  exists_mem_primrec (objectCodes_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst)))))) ((legal_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))))) (Primrec.snd)).and ((forall_mem_primrec (Primrec.fst.comp (Primrec.snd)) (list_mem_primrec.comp (Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))).and (forall_mem_primrec (allRows_primrec.comp (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.const ((3 * b + 4)))) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.const ((3 * b + 4)))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))))) (Primrec.snd)) (implication_primrec (forall_mem_primrec (dataRow_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))))) (Primrec.snd)) (list_mem_primrec.comp (Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))))) ((fits_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))))) (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))))) (Primrec.snd)))) (Primrec.snd.comp (Primrec.fst))))))))

theorem locallyLegal_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × List Code × Code => LocallyLegal Ω p.1 p.2.1 p.2.2) :=
  forall_mem_primrec (subsetRows_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (implication_primrec (Primrec.nat_le.comp (Primrec.list_length.comp (Primrec.snd)) (cutoff_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))) ((localOn_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)))

theorem admissible_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × List Code × Code => Admissible Ω p.1 p.2.1 p.2.2) :=
  ((allGood_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and ((locallyLegal_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd))

theorem rootInjective_primrec : PrimrecRel RootInjective :=
  bounded_forall_primrec (Primrec.fst) (bounded_forall_primrec (Primrec.fst.comp (Primrec.fst)) (implication_primrec ((Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst))) (Primrec.const (0))).not) (implication_primrec (Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst))) ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd))) (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd)))))

theorem canonical_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecPred (fun p : ℕ × List Code × Code => Canonical Ω p.1 p.2.1 p.2.2) :=
  exists_mem_primrec ((roleAssignments_primrec b).comp (Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd)))) ((admissible_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd))

theorem admits_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecPred (fun p : ℕ × List Code × Code => Admits Ω p.1 p.2.1 p.2.2) :=
  exists_mem_primrec ((roleAssignments_primrec b).comp (Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd)))) (((admissible_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)).and (rootInjective_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)))

end TuranUniversality.Effective.StructuralCodes
