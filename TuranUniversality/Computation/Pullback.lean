module

public import TuranUniversality.Computation.MatchingSystem

/-!
# Pulling the concrete local rules back along a partial injection

Only vertices incident with a matching edge or carrying a mark need an image.
In particular isolated, unmarked vertices impose no condition on the target
carrier.  This is the form needed when a singleton support is reconstructed
inside one of its rooted images.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

variable {D E Alphabet : Type*} [DecidableEq D] [DecidableEq E]

namespace Realization

/-- A label-preserving partial injection on all constrained vertices. -/
structure Pullback (A : Realization D Alphabet) (B : Realization E Alphabet) where
  domain : Finset D
  map : {x // x ∈ domain} → E
  injective : Function.Injective map
  J_domain : ∀ x y, (x, y) ∈ A.J.pairs → x ∈ domain ∧ y ∈ domain
  R_domain : ∀ x y, (x, y) ∈ A.R.pairs → x ∈ domain ∧ y ∈ domain
  S_domain : ∀ x y, (x, y) ∈ A.S.pairs → x ∈ domain ∧ y ∈ domain
  marks_domain : A.marks ⊆ domain
  J_preserve : ∀ (x y : {x // x ∈ domain}), (x.1, y.1) ∈ A.J.pairs →
    (map x, map y) ∈ B.J.pairs
  R_preserve : ∀ (x y : {x // x ∈ domain}), (x.1, y.1) ∈ A.R.pairs →
    (map x, map y) ∈ B.R.pairs
  S_preserve : ∀ (x y : {x // x ∈ domain}), (x.1, y.1) ∈ A.S.pairs →
    (map x, map y) ∈ B.S.pairs
  label_preserve : ∀ (b : {x // x ∈ domain}), b.1 ∈ A.colors →
    B.label (map b) = A.label b.1
  marks_preserve : ∀ (a : {x // x ∈ domain}), a.1 ∈ A.marks → map a ∈ B.marks

namespace Pullback

variable {A : Realization D Alphabet} {B : Realization E Alphabet}
variable (F : Pullback A B)

theorem h_domain {x y : D} (h : A.H x y) : x ∈ F.domain ∧ y ∈ F.domain := by
  obtain ⟨b, hj, hr⟩ := h
  exact ⟨(F.J_domain x b hj).1, (F.R_domain b y hr).2⟩

theorem v_domain {x y : D} (h : A.V x y) : x ∈ F.domain ∧ y ∈ F.domain := by
  obtain ⟨b, hj, hs⟩ := h
  exact ⟨(F.J_domain x b hj).1, (F.S_domain b y hs).2⟩

theorem lab_domain {x : D} {a : Alphabet} (h : A.Lab x a) : x ∈ F.domain := by
  obtain ⟨b, hj, _⟩ := h
  exact (F.J_domain x b hj).1

theorem h_preserve {x y : D} (hx : x ∈ F.domain) (hy : y ∈ F.domain)
    (h : A.H x y) : B.H (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) := by
  obtain ⟨b, hj, hr⟩ := h
  let b' : {x // x ∈ F.domain} := ⟨b, (F.J_domain x b hj).2⟩
  exact ⟨F.map b', F.J_preserve _ b' hj, F.R_preserve b' _ hr⟩

theorem v_preserve {x y : D} (hx : x ∈ F.domain) (hy : y ∈ F.domain)
    (h : A.V x y) : B.V (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) := by
  obtain ⟨b, hj, hs⟩ := h
  let b' : {x // x ∈ F.domain} := ⟨b, (F.J_domain x b hj).2⟩
  exact ⟨F.map b', F.J_preserve _ b' hj, F.S_preserve b' _ hs⟩

theorem lab_preserve {x : D} {a : Alphabet} (hx : x ∈ F.domain)
    (h : A.Lab x a) : B.Lab (F.map ⟨x, hx⟩) a := by
  obtain ⟨b, hj, hl⟩ := h
  let b' : {x // x ∈ F.domain} := ⟨b, (F.J_domain x b hj).2⟩
  refine ⟨F.map b', F.J_preserve _ b' hj, ?_⟩
  exact (F.label_preserve b' (A.J.right_mem _ hj)).trans hl

theorem path_preserve {n : ℕ} {x y : D} (hx : x ∈ F.domain)
    (hy : y ∈ F.domain) (h : Path A.H n x y) :
    Path B.H n (F.map ⟨x, hx⟩) (F.map ⟨y, hy⟩) := by
  induction n generalizing x with
  | zero =>
    have hxy : x = y := h
    subst y
    rfl
  | succ n ih =>
    obtain ⟨z, hxz, hzy⟩ := h
    have hz := (F.h_domain hxz).2
    exact ⟨F.map ⟨z, hz⟩, F.h_preserve hx hz hxz, ih hz hzy⟩

variable [DecidableEq Alphabet] (P : Specification Alphabet)

include F

theorem q1 (h : B.Q1) : A.Q1 := by
  intro x e n y z hxe hxn hey hnz
  have hx := (F.h_domain hxe).1
  have he := (F.h_domain hxe).2
  have hn := (F.v_domain hxn).2
  have hy := (F.v_domain hey).2
  have hz := (F.h_domain hnz).2
  have heq := h _ _ _ _ _ (F.h_preserve hx he hxe) (F.v_preserve hx hn hxn)
    (F.v_preserve he hy hey) (F.h_preserve hn hz hnz)
  exact congrArg Subtype.val (F.injective heq)

theorem q2 (h : B.Q2 P) : A.Q2 P := by
  intro l x r x' al ax ar b hlx hxr hxx' hll hlx' hlr hlx''
  have hl := F.lab_domain hll
  have hx := F.lab_domain hlx'
  have hr := F.lab_domain hlr
  have hx' := F.lab_domain hlx''
  exact h _ _ _ _ _ _ _ _ (F.h_preserve hl hx hlx) (F.h_preserve hx hr hxr)
    (F.v_preserve hx hx' hxx') (F.lab_preserve hl hll) (F.lab_preserve hx hlx')
    (F.lab_preserve hr hlr) (F.lab_preserve hx' hlx'')

theorem q3 (h : B.Q3 P) : A.Q3 P := by
  intro x y a b hxy hxa hyb
  have hx := F.lab_domain hxa
  have hy := F.lab_domain hyb
  exact h _ _ _ _ (F.h_preserve hx hy hxy) (F.lab_preserve hx hxa)
    (F.lab_preserve hy hyb)

theorem q4Marked (h : B.Q4Marked P) : A.Q4Marked P := by
  intro a ha y sy sa hya hys has
  have ha' := F.marks_domain ha
  have hy := F.lab_domain hys
  exact h _ (F.marks_preserve ⟨a, ha'⟩ ha) _ _ _ (F.h_preserve hy ha' hya)
    (F.lab_preserve hy hys) (F.lab_preserve ha' has)

theorem q4Prefix (h : B.Q4Prefix P) : A.Q4Prefix P := by
  intro x sx hxs ht j hj z sz hp hzs
  have hx := F.lab_domain hxs
  have hz := F.lab_domain hzs
  exact h _ _ (F.lab_preserve hx hxs) ht j hj _ _ (F.path_preserve hx hz hp)
    (F.lab_preserve hz hzs)

/-- Every local clause is preserved under a partial label-preserving injection. -/
theorem legal (h : B.Legal P) : A.Legal P :=
  ⟨F.q1 h.1, F.q2 P h.2.1, F.q3 P h.2.2.1, F.q4Marked P h.2.2.2.1,
    F.q4Prefix P h.2.2.2.2⟩

end Pullback
end Realization
end TuranUniversality.Computation.MatchingSystem
