module

public import TuranUniversality.Effective.GraphEmbedding

@[expose] public section

/-! # Kernel-checked primitive recursion for exact embedding search -/

namespace TuranUniversality.Effective

set_option maxRecDepth 2000

theorem embeddingAssignment_primrec : PrimrecRel EmbeddingAssignment := by
  have hi : PrimrecRel (fun (p : GraphCode × GraphCode) (xs : List ℕ) =>
      ∀ x < p.1.1, ∀ y < p.1.1, xs.getD x 0 = xs.getD y 0 → x = y) :=
    bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (implication_primrec (Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst))) ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd))) (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))))
  have he : PrimrecRel (fun (p : GraphCode × GraphCode) (xs : List ℕ) =>
      ∀ x < p.1.1, ∀ y < p.1.1, ∀ z < p.1.1,
        CodeEdge p.1 (x, y, z) → CodeEdge p.2 (xs.getD x 0, xs.getD y 0, xs.getD z 0)) :=
    bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))) (implication_primrec (codeEdge_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (Primrec.snd)))) (codeEdge_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.pair ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.pair ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.fst))) ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd))))))))
  exact hi.and he

theorem codeContains_primrec : PrimrecRel CodeContains := by
  have hl : Primrec (fun p : GraphCode × GraphCode => allWords (List.range p.2.1) p.1.1) :=
    allWords_primrec.comp (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst)
  exact embeddingAssignment_primrec.swap.exists_mem_list.comp hl Primrec.id

end TuranUniversality.Effective
