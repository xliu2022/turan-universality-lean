module

public import TuranUniversality.Effective.MatchingEncoding

/-! # Bounded code-level checks equivalent to all actual local rules -/

@[expose] public section

namespace TuranUniversality.Effective.MatchingCode

open Computation.MatchingSystem

variable {Alphabet : Type*} [Primcodable Alphabet] [Inhabited Alphabet] [DecidableEq Alphabet]

def Q1 (c : MatchingCode Alphabet) : Prop :=
  ∀ x < c.size, ∀ e < c.size, ∀ n < c.size, ∀ y < c.size, ∀ z < c.size,
    c.H x e → c.V x n → c.V e y → c.H n z → y = z

def Q2 (c : MatchingCode Alphabet) (P : Specification Alphabet) : Prop :=
  ∀ l < c.size, ∀ x < c.size, ∀ r < c.size, ∀ x' < c.size,
    ∀ al ax ar b, c.H l x → c.H x r → c.V x x' →
      c.Lab l al → c.Lab x ax → c.Lab r ar → c.Lab x' b → (al, ax, ar, b) ∈ P.evolution

def Q3 (c : MatchingCode Alphabet) (P : Specification Alphabet) : Prop :=
  ∀ x < c.size, ∀ y < c.size, ∀ a b,
    c.H x y → c.Lab x a → c.Lab y b → (a, b) ∈ P.horizontal

def Q4Marked (c : MatchingCode Alphabet) (P : Specification Alphabet) : Prop :=
  ∀ a < c.size, a ∈ c.marks → ∀ y < c.size, ∀ sy sa,
    c.H y a → c.Lab y sy → c.Lab a sa → sy = P.leftWall ∧ sa ∈ P.initial

def Q4Prefix (c : MatchingCode Alphabet) (P : Specification Alphabet) : Prop :=
  ∀ x < c.size, ∀ sx, c.Lab x sx → sx ∈ P.prefixTrigger →
    ∀ j < P.inputPrefix.length, ∀ z < c.size, ∀ sz,
      c.HasPath j x z → c.Lab z sz → sz ∈ P.inputPrefix.getD j ∅

def Legal (c : MatchingCode Alphabet) (P : Specification Alphabet) : Prop :=
  c.Q1 ∧ c.Q2 P ∧ c.Q3 P ∧ c.Q4Marked P ∧ c.Q4Prefix P

namespace Represents

variable {c : MatchingCode Alphabet} {A : Realization (Fin c.size) Alphabet}
  (h : c.Represents A) (P : Specification Alphabet)

include h

theorem q1_iff : c.Q1 ↔ A.Q1 := by
  constructor
  · intro hc x e n y z hxe hxn hey hnz
    apply Fin.ext
    exact hc x.val x.isLt e.val e.isLt n.val n.isLt y.val y.isLt z.val z.isLt
      ((h.H_iff x e).mpr hxe) ((h.V_iff x n).mpr hxn)
      ((h.V_iff e y).mpr hey) ((h.H_iff n z).mpr hnz)
  · intro ha x hx e he n hn y hy z hz hxe hxn hey hnz
    exact congrArg Fin.val (ha ⟨x, hx⟩ ⟨e, he⟩ ⟨n, hn⟩ ⟨y, hy⟩ ⟨z, hz⟩
      ((h.H_iff _ _).mp hxe) ((h.V_iff _ _).mp hxn)
      ((h.V_iff _ _).mp hey) ((h.H_iff _ _).mp hnz))

theorem q2_iff : c.Q2 P ↔ A.Q2 P := by
  constructor
  · intro hc l x r x' al ax ar b hlx hxr hxx' hll hxx hrr hbb
    exact hc l.val l.isLt x.val x.isLt r.val r.isLt x'.val x'.isLt al ax ar b
      ((h.H_iff _ _).mpr hlx) ((h.H_iff _ _).mpr hxr) ((h.V_iff _ _).mpr hxx')
      ((h.Lab_iff _ _).mpr hll) ((h.Lab_iff _ _).mpr hxx)
      ((h.Lab_iff _ _).mpr hrr) ((h.Lab_iff _ _).mpr hbb)
  · intro ha l hl x hx r hr x' hx' al ax ar b hlx hxr hxx' hll hxx hrr hbb
    exact ha ⟨l, hl⟩ ⟨x, hx⟩ ⟨r, hr⟩ ⟨x', hx'⟩ al ax ar b
      ((h.H_iff _ _).mp hlx) ((h.H_iff _ _).mp hxr) ((h.V_iff _ _).mp hxx')
      ((h.Lab_iff _ _).mp hll) ((h.Lab_iff _ _).mp hxx)
      ((h.Lab_iff _ _).mp hrr) ((h.Lab_iff _ _).mp hbb)

theorem q3_iff : c.Q3 P ↔ A.Q3 P := by
  constructor
  · intro hc x y a b hxy hxa hyb
    exact hc x.val x.isLt y.val y.isLt a b ((h.H_iff _ _).mpr hxy)
      ((h.Lab_iff _ _).mpr hxa) ((h.Lab_iff _ _).mpr hyb)
  · intro ha x hx y hy a b hxy hxa hyb
    exact ha ⟨x, hx⟩ ⟨y, hy⟩ a b ((h.H_iff _ _).mp hxy)
      ((h.Lab_iff _ _).mp hxa) ((h.Lab_iff _ _).mp hyb)

theorem q4Marked_iff : c.Q4Marked P ↔ A.Q4Marked P := by
  constructor
  · intro hc a ha y sy sa hya hys has
    exact hc a.val a.isLt ((h.mark a).mpr ha) y.val y.isLt sy sa
      ((h.H_iff _ _).mpr hya) ((h.Lab_iff _ _).mpr hys) ((h.Lab_iff _ _).mpr has)
  · intro ha a ha' ham y hy sy sa hya hys has
    exact ha ⟨a, ha'⟩ ((h.mark _).mp ham) ⟨y, hy⟩ sy sa
      ((h.H_iff _ _).mp hya) ((h.Lab_iff _ _).mp hys) ((h.Lab_iff _ _).mp has)

theorem q4Prefix_iff : c.Q4Prefix P ↔ A.Q4Prefix P := by
  constructor
  · intro hc x sx hxs ht j hj z sz hp hzs
    have hh := hc x.val x.isLt sx ((h.Lab_iff _ _).mpr hxs) ht j hj z.val z.isLt sz
      ((h.Path_iff _ _ _).mpr hp) ((h.Lab_iff _ _).mpr hzs)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hh
  · intro ha x hx sx hxs ht j hj z hz sz hp hzs
    have hh := ha ⟨x, hx⟩ sx ((h.Lab_iff _ _).mp hxs) ht j hj ⟨z, hz⟩ sz
      ((h.Path_iff _ _ _).mp hp) ((h.Lab_iff _ _).mp hzs)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hh

/-- The finite-code checker is exactly the previously used positive local
legality predicate on the actual finite matching realization. -/
theorem legal_iff : c.Legal P ↔ A.Legal P :=
  and_congr h.q1_iff (and_congr (h.q2_iff P) (and_congr (h.q3_iff P)
    (and_congr (h.q4Marked_iff P) (h.q4Prefix_iff P))))

end Represents
end TuranUniversality.Effective.MatchingCode
