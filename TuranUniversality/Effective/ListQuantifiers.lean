module

public import TuranUniversality.Effective.ListOperations

/-! # Parameter-dependent finite list quantifiers -/

@[expose] public section

namespace TuranUniversality.Effective

variable {A B : Type*} [Primcodable A] [Primcodable B]

theorem forall_list_primrec {xs : A → List B} {P : A → B → Prop}
    (hxs : Primrec xs) (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∀ b ∈ xs a, P a b) :=
  hP.swap.forall_mem_list.comp hxs Primrec.id

theorem exists_list_primrec {xs : A → List B} {P : A → B → Prop}
    (hxs : Primrec xs) (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∃ b ∈ xs a, P a b) :=
  hP.swap.exists_mem_list.comp hxs Primrec.id

end TuranUniversality.Effective
