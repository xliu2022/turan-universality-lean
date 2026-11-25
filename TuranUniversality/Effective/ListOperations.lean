module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Sublists

/-! # Primitive-recursive finite list operations used by the graph compiler -/

@[expose] public section

namespace TuranUniversality.Effective

variable {A B : Type*} [Primcodable A] [Primcodable B]

def cartesian (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

theorem cartesian_primrec : Primrec₂ (cartesian (A := A) (B := B)) :=
  (Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).to₂

@[simp] theorem mem_cartesian {xs : List A} {ys : List B} {p : A × B} :
    p ∈ cartesian xs ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  rcases p with ⟨x, y⟩
  simp [cartesian]

theorem sublists_primrec : Primrec (List.sublists' (α := A)) := by
  have hm : Primrec (fun p : List A × (A × List (List A)) =>
      p.2.2.map (List.cons p.2.1)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp ((Primrec.fst.comp Primrec.snd).comp Primrec.fst)
        Primrec.snd).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const [[]])
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) hm).to₂).of_eq
      (fun xs => by induction xs <;> simp_all [List.sublists'_cons])

theorem list_mem_primrec [DecidableEq A] : PrimrecRel (fun (a : A) (xs : List A) => a ∈ xs) :=
  (Primrec.eq.exists_mem_list).swap.of_eq (fun a xs => by simp)

/-- A parameter-dependent filter, in the argument order used by the compiler. -/
theorem filter_primrec {P : A → B → Prop} [DecidableRel P] (hP : PrimrecRel P) :
    Primrec₂ (fun (a : A) (xs : List B) => xs.filter fun b => P a b) :=
  hP.swap.listFilter.swap

/-- Bounded quantification with both bound and parameter varying primitively
recursively; the bound need not be a constant. -/
theorem bounded_exists_primrec {b : A → ℕ} {P : A → ℕ → Prop}
    (hb : Primrec b) (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∃ i < b a, P a i) :=
  (hP.swap.exists_mem_list.comp (Primrec.list_range.comp hb) Primrec.id).of_eq
    (fun a => by simp)

theorem bounded_forall_primrec {b : A → ℕ} {P : A → ℕ → Prop}
    (hb : Primrec b) (hP : PrimrecRel P) :
    PrimrecPred (fun a => ∀ i < b a, P a i) :=
  (hP.swap.forall_mem_list.comp (Primrec.list_range.comp hb) Primrec.id).of_eq
    (fun a => by simp)

end TuranUniversality.Effective
