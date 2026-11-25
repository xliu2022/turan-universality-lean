module

public import TuranUniversality.Effective.StructuralEdges

@[expose] public section

/-! # Primitive recursion for the actual finite structural tests -/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform Structural

set_option maxRecDepth 6000

theorem supportCode_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) :
    Primrec (supportCode Ω) :=
  Primrec.pair (Primrec.const (5 * b))
    ((Primrec.list_getD ([] : List (List ℕ))).comp (Primrec.const (supportTable Ω)) Primrec.id)

theorem roleAssignments_primrec (b : ℕ) : Primrec₂ (roleAssignments b) :=
  assignments_primrec.comp (Primrec.pair Primrec.snd (Primrec.const []))
    (Primrec.pair (Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const (5 * b))) (Primrec.const 1))
      (Primrec.const []))

theorem dataRow_primrec : Primrec₂ dataRow := by
  have h : PrimrecRel (fun (xs : List ℕ) (v : ℕ) => xs.getD v 0 = 0) :=
    Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp Primrec.fst Primrec.snd) (Primrec.const 0)
  exact filter_primrec h

theorem rootCheck_primrec (b : ℕ) : PrimrecRel (fun p : ℕ × List ℕ × List ℕ => RootCheck b p.1 p.2.1 p.2.2) :=
  bounded_forall_primrec (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.const ((5 * b)))) (iff_primrec (list_mem_primrec.comp (Primrec.nat_add.comp (Primrec.snd) (Primrec.const (1))) (imageRow_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))) ((Primrec.nat_lt.comp (Primrec.snd) (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))).or (list_mem_primrec.comp (Primrec.nat_sub.comp (Primrec.snd) (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.fst)))))

theorem declares_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × List ℕ × List ℕ => Declares Ω p.1 p.2.1 p.2.2) :=
  exists_mem_primrec (allRows_primrec.comp (Primrec.const ((3 * b))) (Primrec.const ((5 * b)))) ((edge_primrec.comp (Primrec.pair (Primrec.const ((3 * b))) ((supportCode_primrec Ω).comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and ((rootCheck_primrec b).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))) (Primrec.snd)))

theorem goodEdge_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × List ℕ => GoodEdge Ω p.1 p.2) :=
  (Primrec.eq.comp (Primrec.list_length.comp (dataRow_primrec.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))) (Primrec.const (4))).and (bounded_exists_primrec (Primrec.const (7)) ((declares_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)))

theorem fits_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : PrimrecRel (fun p : ℕ × ℕ × List ℕ × List ℕ => Fits Ω p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  bounded_exists_primrec (Primrec.const (7)) ((labels_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.pair (Primrec.snd.comp (Primrec.fst)) (dataRow_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))))) (Primrec.snd)).and ((declares_primrec Ω).comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))))) (Primrec.snd)))

end TuranUniversality.Effective.StructuralCodes
