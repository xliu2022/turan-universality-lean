module

public import TuranUniversality.Effective.UniformMaps

@[expose] public section

/-! # Joint primitive recursion for the actual finite graph predicates -/

namespace TuranUniversality.Effective.Uniform

set_option maxRecDepth 4000

theorem forall_mem_primrec {A B : Type*} [Primcodable A] [Primcodable B]
    {f : A → List B} {P : A × B → Prop} (hf : Primrec f) (hP : PrimrecPred P) :
    PrimrecPred (fun a => ∀ b ∈ f a, P (a, b)) := by
  have h : PrimrecRel (fun a b => P (a, b)) := hP
  exact h.swap.forall_mem_list.comp hf Primrec.id

theorem exists_mem_primrec {A B : Type*} [Primcodable A] [Primcodable B]
    {f : A → List B} {P : A × B → Prop} (hf : Primrec f) (hP : PrimrecPred P) :
    PrimrecPred (fun a => ∃ b ∈ f a, P (a, b)) := by
  have h : PrimrecRel (fun a b => P (a, b)) := hP
  exact h.swap.exists_mem_list.comp hf Primrec.id

theorem distinct_primrec : PrimrecPred Distinct :=
  bounded_forall_primrec (Primrec.list_length.comp (Primrec.id)) (bounded_forall_primrec (Primrec.list_length.comp (Primrec.fst)) (implication_primrec (Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.fst))) ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (Primrec.fst)) (Primrec.snd))) (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))))

theorem sameSet_primrec : PrimrecRel SameSet :=
  (forall_mem_primrec (Primrec.fst) (list_mem_primrec.comp (Primrec.snd) (Primrec.snd.comp (Primrec.fst)))).and (forall_mem_primrec (Primrec.snd) (list_mem_primrec.comp (Primrec.snd) (Primrec.fst.comp (Primrec.fst))))

theorem good_primrec : PrimrecRel (fun p : ℕ × ℕ => Good p.1 p.2) :=
  (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd)) (Primrec.fst.comp (Primrec.fst))).and ((distinct_primrec.comp (Primrec.snd)).and (forall_mem_primrec (Primrec.snd) (Primrec.nat_lt.comp (Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))))

theorem edge_primrec : PrimrecRel (fun p : ℕ × Code => Edge p.1 p.2) :=
  (good_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and (exists_mem_primrec (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))) ((Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd)) (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))).and (sameSet_primrec.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))))

theorem imageRow_primrec : Primrec₂ imageRow :=
  Primrec.list_map Primrec.snd
    ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem assignments_primrec : Primrec₂ assignments :=
  allWords_primrec.comp (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp Primrec.fst)

theorem injectiveAssignment_primrec : PrimrecRel InjectiveAssignment :=
  bounded_forall_primrec (Primrec.fst) (bounded_forall_primrec (Primrec.fst.comp (Primrec.fst)) (implication_primrec (Primrec.eq.comp ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.fst))) ((Primrec.list_getD (0 : ℕ)).comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd))) (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))))

theorem homAssignment_primrec : PrimrecRel (fun p : ℕ × Code × Code => HomAssignment p.1 p.2.1 p.2.2) :=
  forall_mem_primrec (allRows_primrec.comp (Primrec.fst.comp (Primrec.fst)) (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))))) (implication_primrec (edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (Primrec.snd)) (edge_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst))))) (imageRow_primrec.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd))))

theorem hasHom_primrec : PrimrecPred (fun p : ℕ × Code × Code => HasHom p.1 p.2.1 p.2.2) :=
  exists_mem_primrec (assignments_primrec.comp (Primrec.fst.comp (Primrec.snd)) (Primrec.snd.comp (Primrec.snd))) (homAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd))

theorem contains_primrec : PrimrecPred (fun p : ℕ × Code × Code => Contains p.1 p.2.1 p.2.2) :=
  exists_mem_primrec (assignments_primrec.comp (Primrec.fst.comp (Primrec.snd)) (Primrec.snd.comp (Primrec.snd))) ((injectiveAssignment_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst)))) (Primrec.snd)).and (homAssignment_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst))))) (Primrec.snd)))

end TuranUniversality.Effective.Uniform
