module

public import TuranUniversality.Effective.ListOperations
public import TuranUniversality.Computation.MatchingSystem

/-! # Fixed finite encodings for the actual local specification -/

@[expose] public section

namespace TuranUniversality.Effective

open Computation.MatchingSystem

noncomputable instance (priority := 50) finiteSetPrimcodable
    (A : Type*) [Fintype A] [DecidableEq A] : Primcodable (Finset A) :=
  Primcodable.ofEquiv (Fin (Fintype.card (Finset A))) (Fintype.equivFin _)

variable {A B : Type*} [Primcodable A] [Primcodable B]

theorem forall_finite_primrec [Fintype B] {P : A → B → Prop} (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∀ b, P a b) := by
  classical
  exact (hP.swap.forall_mem_list.comp
    (Primrec.const (Finset.univ.toList : List B)) Primrec.id).of_eq (fun a => by simp)

theorem exists_finite_primrec [Fintype B] {P : A → B → Prop} (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∃ b, P a b) := by
  classical
  exact (hP.swap.exists_mem_list.comp
    (Primrec.const (Finset.univ.toList : List B)) Primrec.id).of_eq (fun a => by simp)

theorem implication_primrec {P Q : A → Prop} (hP : PrimrecPred P) (hQ : PrimrecPred Q) :
    PrimrecPred (fun a => P a → Q a) := by
  classical
  exact (hP.not.or hQ).of_eq (fun a => by tauto)

variable {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet] [Primcodable Alphabet]

abbrev SpecificationTuple (Alphabet : Type*) [DecidableEq Alphabet] :=
  Alphabet × Finset Alphabet × Finset (Alphabet × Alphabet) ×
    Finset (Alphabet × Alphabet × Alphabet × Alphabet) × Finset Alphabet × List (Finset Alphabet)

def specificationEquiv : Specification Alphabet ≃ SpecificationTuple Alphabet where
  toFun := fun P => (P.leftWall, P.initial, P.horizontal, P.evolution, P.prefixTrigger, P.inputPrefix)
  invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv := fun P => by cases P; rfl
  right_inv := fun p => rfl

noncomputable instance specificationPrimcodable : Primcodable (Specification Alphabet) :=
  Primcodable.ofEquiv (SpecificationTuple Alphabet) specificationEquiv

theorem specificationTuple_primrec : Primrec (specificationEquiv (Alphabet := Alphabet)) :=
  Primrec.of_equiv

theorem leftWall_primrec : Primrec (Specification.leftWall (Alphabet := Alphabet)) :=
  Primrec.fst.comp specificationTuple_primrec

theorem initial_primrec : Primrec (Specification.initial (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp specificationTuple_primrec)

theorem horizontal_primrec : Primrec (Specification.horizontal (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp specificationTuple_primrec))

theorem evolution_primrec : Primrec (Specification.evolution (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp specificationTuple_primrec)))

theorem trigger_primrec : Primrec (Specification.prefixTrigger (Alphabet := Alphabet)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp specificationTuple_primrec))))

theorem inputPrefix_projection_primrec : Primrec (Specification.inputPrefix (Alphabet := Alphabet)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp specificationTuple_primrec))))

theorem finiteSet_mem_primrec {X : Type*} [Fintype X] [DecidableEq X] [Primcodable X] :
    PrimrecRel (fun (s : Finset X) (x : X) => x ∈ s) :=
  (Primrec.dom_finite (fun p : Finset X × X => decide (p.2 ∈ p.1))).primrecPred

end TuranUniversality.Effective
