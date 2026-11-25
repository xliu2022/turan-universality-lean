module

public import TuranUniversality.Effective.UniformPrimrec
public import TuranUniversality.Effective.UniformFamily

@[expose] public section

/-! # Joint primitive recursion of suspension and extension searches -/

namespace TuranUniversality.Effective.Uniform

set_option maxRecDepth 5000

theorem edgeless_primrec : PrimrecRel Edgeless :=
  forall_mem_primrec (allRows_primrec.comp (Primrec.fst) (Primrec.fst.comp (Primrec.snd))) ((edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.fst))) (Primrec.snd)).not)

theorem core_primrec : PrimrecRel (fun p : ℕ × Code => Core p.1 p.2) :=
  (good_primrec.comp (Primrec.pair (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.const (3))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and ((Primrec.eq.comp (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.snd)) (Primrec.const (3))) (Primrec.fst.comp (Primrec.fst))).and (forall_mem_primrec (allRows_primrec.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd)) (forall_mem_primrec (Primrec.snd.comp (Primrec.fst)) (list_mem_primrec.comp (Primrec.snd) (Primrec.snd.comp (Primrec.fst)))))))

theorem outside_primrec : PrimrecRel (fun p : ℕ × List ℕ => Outside p.1 p.2) :=
  bounded_forall_primrec (Primrec.fst.comp (Primrec.fst)) ((list_mem_primrec.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd)) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))).not)

theorem linkHomAssignment_primrec : PrimrecRel (fun a : ℕ × Code × Code × List ℕ => LinkHomAssignment a.1 a.2.1 a.2.2.1 a.2.2.2) :=
  (outside_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)).and (forall_mem_primrec (allRows_primrec.comp (Primrec.const (3)) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.const (3)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd)) (edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))))) (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (imageRow_primrec.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))))))

theorem linkHasHom_primrec : PrimrecRel (fun a : ℕ × Code × Code => LinkHasHom a.1 a.2.1 a.2.2) :=
  exists_mem_primrec (assignments_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst)))) (linkHomAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd))

theorem admissible_primrec : PrimrecPred (fun a : ℕ × Code × Code => Admissible a.1 a.2.1 a.2.2) :=
  (edgeless_primrec.comp (Primrec.fst) (Primrec.snd.comp (Primrec.snd))).or (exists_mem_primrec (allRows_primrec.comp (Primrec.nat_sub.comp (Primrec.fst) (Primrec.const (3))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd)))) ((core_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and ((linkHasHom_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)).not)))

theorem coveredPair_primrec : PrimrecRel (fun p : ℕ × Code => fun q : ℕ × ℕ => CoveredPair p.1 p.2 q.1 q.2) :=
  exists_mem_primrec (allRows_primrec.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) ((edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd)).and ((list_mem_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd)).and (list_mem_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd))))

theorem noIsolates_primrec : PrimrecRel NoIsolates :=
  bounded_forall_primrec (Primrec.fst.comp (Primrec.snd)) (coveredPair_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.fst))) (Primrec.pair (Primrec.snd) (Primrec.snd)))

theorem coversAssignment_primrec : PrimrecRel (fun p : ℕ × Code × Code => CoversAssignment p.1 p.2.1 p.2.2) :=
  bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (bounded_forall_primrec (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (implication_primrec ((Primrec.eq.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd)).not) (coveredPair_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))))) (Primrec.pair ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst))) ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd))))))

theorem isExtension_primrec : PrimrecPred (fun p : ℕ × Code × Code => IsExtension p.1 p.2.1 p.2.2) :=
  (noIsolates_primrec.comp (Primrec.fst) (Primrec.snd.comp (Primrec.snd))).and (exists_mem_primrec (assignments_primrec.comp (Primrec.fst.comp (Primrec.snd)) (Primrec.snd.comp (Primrec.snd))) ((injectiveAssignment_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and ((homAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)).and (coversAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)))))

theorem choose_fixed_primrec (k : ℕ) : Primrec (fun n : ℕ => n.choose k) := by
  have hd (j : ℕ) : Primrec (fun n : ℕ => n.descFactorial j) := by
    induction j with
    | zero => simpa only [Nat.descFactorial_zero] using (Primrec.const (1 : ℕ) : Primrec (fun _ : ℕ => 1))
    | succ j ih =>
        simpa only [Nat.descFactorial_succ, id_eq] using
          Primrec.nat_mul.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const j)) ih
  exact (Primrec.nat_div.comp (hd k) (Primrec.const k.factorial)).of_eq
    (fun n => (Nat.choose_eq_descFactorial_div_factorial n k).symm)

theorem obstructionBound_primrec : Primrec₂ Uniformity.obstructionBound :=
  Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_mul.comp ((choose_fixed_primrec 3).comp Primrec.fst)
      (Primrec.nat_max.comp Primrec.fst Primrec.snd))

theorem extensionBound_primrec : Primrec₂ Uniformity.extensionBound :=
  Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_mul.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 2))
      ((choose_fixed_primrec 2).comp Primrec.snd))

theorem extensionCodes_primrec : Primrec₂ extensionCodes := by
  have hc : PrimrecRel (fun p : ℕ × Code => IsExtension p.1 p.2) :=
    isExtension_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (filter_primrec hc).comp Primrec.id
    (boundedCodes_primrec.comp Primrec.fst
      (extensionBound_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))

theorem basisCodes_primrec : Primrec₂ basisCodes := by
  have hc : PrimrecRel (fun p : ℕ × Code => fun g => ¬ Admissible p.1 p.2 g) :=
    (admissible_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).not
  exact (filter_primrec hc).comp Primrec.id
    (boundedCodes_primrec.comp Primrec.fst
      (obstructionBound_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))

theorem familyCodes_primrec : Primrec₂ familyCodes :=
  Primrec.list_flatMap basisCodes_primrec
    (extensionCodes_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

end TuranUniversality.Effective.Uniform
