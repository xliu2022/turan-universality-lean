module

public import TuranUniversality.Effective.HomomorphicClosureCodes

@[expose] public section

/-! # Joint primitive recursion of exact finite homomorphic closure

All displayed proof terms use the ordinary primitive-recursion closure
lemmas for bounded finite quantification and list filtering.
-/

namespace TuranUniversality.Effective.Uniform

open FiniteApproximation

set_option maxRecDepth 5000

theorem surjectiveAssignment_primrec : PrimrecRel (fun p : ℕ × ℕ => SurjectiveAssignment p.1 p.2) :=
  bounded_forall_primrec (Primrec.snd.comp (Primrec.fst)) (bounded_exists_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd)) (Primrec.snd.comp (Primrec.fst))))

theorem coversImageEdges_primrec : PrimrecRel (fun p : ℕ × Code × Code => CoversImageEdges p.1 p.2.1 p.2.2) :=
  forall_mem_primrec (allRows_primrec.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd)) (exists_mem_primrec (allRows_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))) ((edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))))) (Primrec.snd)).and (sameSet_primrec.comp (imageRow_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd)) (Primrec.snd.comp (Primrec.fst))))))

theorem isImage_primrec : PrimrecPred (fun p : ℕ × Code × Code => IsImage p.1 p.2.1 p.2.2) :=
  exists_mem_primrec (assignments_primrec.comp (Primrec.fst.comp (Primrec.snd)) (Primrec.snd.comp (Primrec.snd))) ((surjectiveAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)).and ((homAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)).and (coversImageEdges_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd))))

theorem imageFamily_primrec : PrimrecRel (fun p : ℕ × List Code => fun h => ∃ g ∈ p.2, IsImage p.1 g h) :=
  exists_mem_primrec (Primrec.snd.comp (Primrec.fst)) (isImage_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.snd) (Primrec.snd.comp (Primrec.fst)))))

theorem maxOrder_primrec : Primrec maxOrder :=
  listMax_primrec.comp (Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂)

theorem closureCodes_primrec : Primrec₂ closureCodes :=
  (filter_primrec imageFamily_primrec).comp Primrec.id
    (boundedCodes_primrec.comp Primrec.fst (maxOrder_primrec.comp Primrec.snd))

end TuranUniversality.Effective.Uniform
