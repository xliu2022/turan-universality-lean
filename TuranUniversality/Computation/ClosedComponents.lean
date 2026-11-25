module

public import TuranUniversality.Computation.MatchingSystem

/-!
# Closed matching components yield commuting finite permutations

Closedness is checked at all six indexed incidences of the two types.  The
three actual partial matchings then become bijections on the component, and
Q1--Q4 transfer to total horizontal/vertical dynamics with present labels.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

open TuranUniversality.Weighted

variable {D Alphabet : Type*} [DecidableEq D]

theorem exists_equiv_of_unique_relation {A B : Type*} (r : A → B → Prop)
    (hl : ∀ a, ∃! b, r a b) (hr : ∀ b, ∃! a, r a b) :
    ∃ e : A ≃ B, ∀ a, r a (e a) := by
  classical
  let f : A → B := fun a => (hl a).choose
  have hf : ∀ a, r a (f a) := fun a => (hl a).choose_spec.1
  have hinj : Function.Injective f := by
    intro a a' h
    exact (hr (f a)).unique (hf a) (h ▸ hf a')
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha, _⟩ := hr b
    exact ⟨a, (hl a).unique (hf a) ha⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

namespace Realization

variable (A : Realization D Alphabet)

/-- A specified type class restricted to an actual relation component. -/
def ComponentIn (U : Finset D) (a : D) := {x : D // x ∈ U ∧ A.Connected a x}

abbrev CellComponent (a : D) := A.ComponentIn A.cells a

abbrev ColorComponent (a : D) := A.ComponentIn A.colors a

noncomputable instance componentInFintype (U : Finset D) (a : D) :
    Fintype (A.ComponentIn U a) := by
  classical
  change Fintype {x : D // x ∈ U ∧ A.Connected a x}
  exact Fintype.ofFinset (U.filter (A.Connected a)) (by
    intro x
    change x ∈ U.filter (A.Connected a) ↔ x ∈ U ∧ A.Connected a x
    simp)

/-- A partial matching whose two incidences are complete becomes a bijection
on the component.  Its edge witnesses remain the original matching instances. -/
theorem matching_equiv_on_component (a : D) {U V : Finset D} (P : PartialMatching U V)
    (hn : ∀ x y, (x, y) ∈ P.pairs → A.Neighbor x y)
    (hl : ∀ x ∈ U, A.Connected a x → ∃ y, (x, y) ∈ P.pairs)
    (hr : ∀ y ∈ V, A.Connected a y → ∃ x, (x, y) ∈ P.pairs) :
    ∃ e : A.ComponentIn U a ≃ A.ComponentIn V a,
      ∀ x, (x.val, (e x).val) ∈ P.pairs := by
  apply exists_equiv_of_unique_relation
    (fun (x : A.ComponentIn U a) (y : A.ComponentIn V a) => (x.val, y.val) ∈ P.pairs)
  · intro x
    obtain ⟨y, hy⟩ := hl x.val x.prop.1 x.prop.2
    let y' : A.ComponentIn V a :=
      ⟨y, P.right_mem _ hy, x.prop.2.tail (hn x.val y hy)⟩
    refine ⟨y', hy, ?_⟩
    intro z hz
    apply Subtype.ext
    exact pair_left_unique P hz hy
  · intro y
    obtain ⟨x, hx⟩ := hr y.val y.prop.1 y.prop.2
    let x' : A.ComponentIn U a :=
      ⟨x, P.left_mem _ hx, y.prop.2.tail (A.neighbor_symm (hn x y.val hx))⟩
    refine ⟨x', hx, ?_⟩
    intro z hz
    apply Subtype.ext
    exact pair_right_unique P hz hx

/-- Total dynamics on the cells of a closed component. -/
structure ClosedDynamics (a : D) where
  color : A.CellComponent a ≃ A.ColorComponent a
  horizontal : Equiv.Perm (A.CellComponent a)
  vertical : Equiv.Perm (A.CellComponent a)
  color_edge : ∀ x, (x.val, (color x).val) ∈ A.J.pairs
  horizontal_path : ∀ x, A.H x.val (horizontal x).val
  vertical_path : ∀ x, A.V x.val (vertical x).val

theorem closed_dynamics (a : D) (hc : A.ClosedAt a) : Nonempty (A.ClosedDynamics a) := by
  obtain ⟨eJ, hJ⟩ := A.matching_equiv_on_component a A.J
    (fun _ _ h => Or.inl h)
    (fun x hx hconn => ((hc x hconn).1 hx).1)
    (fun y hy hconn => ((hc y hconn).2 hy).1)
  obtain ⟨eR, hR⟩ := A.matching_equiv_on_component a A.R
    (fun _ _ h => Or.inr (Or.inr (Or.inl h)))
    (fun x hx hconn => ((hc x hconn).2 hx).2.1)
    (fun y hy hconn => ((hc y hconn).1 hy).2.1)
  obtain ⟨eS, hS⟩ := A.matching_equiv_on_component a A.S
    (fun _ _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (fun x hx hconn => ((hc x hconn).2 hx).2.2)
    (fun y hy hconn => ((hc y hconn).1 hy).2.2)
  exact ⟨{
    color := eJ
    horizontal := eJ.trans eR
    vertical := eJ.trans eS
    color_edge := hJ
    horizontal_path := fun x => ⟨(eJ x).val, hJ x, hR (eJ x)⟩
    vertical_path := fun x => ⟨(eJ x).val, hJ x, hS (eJ x)⟩ }⟩

namespace ClosedDynamics

variable {A : Realization D Alphabet} {a : D} (d : A.ClosedDynamics a)

def label (x : A.CellComponent a) : Alphabet := A.label (d.color x).val

theorem lab_present (x : A.CellComponent a) : A.Lab x.val (d.label x) :=
  ⟨(d.color x).val, d.color_edge x, rfl⟩

theorem horizontal_predecessor (x : A.CellComponent a) :
    A.H (d.horizontal.symm x).val x.val := by
  simpa only [Equiv.apply_symm_apply] using d.horizontal_path (d.horizontal.symm x)

theorem horizontal_path_iterate (n : ℕ) (x : A.CellComponent a) :
    Path A.H n x.val ((d.horizontal : A.CellComponent a → A.CellComponent a)^[n] x).val := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    refine ⟨(d.horizontal x).val, d.horizontal_path x, ?_⟩
    simpa only [Function.iterate_succ_apply] using ih (d.horizontal x)

theorem commute (h : A.Q1) : Function.Commute d.horizontal d.vertical := by
  intro x
  apply Subtype.ext
  exact (h x.val (d.horizontal x).val (d.vertical x).val
    (d.vertical (d.horizontal x)).val (d.horizontal (d.vertical x)).val
    (d.horizontal_path x) (d.vertical_path x)
    (d.vertical_path (d.horizontal x)) (d.horizontal_path (d.vertical x))).symm

variable [DecidableEq Alphabet] {P : Specification Alphabet}

theorem evolution (h : A.Q2 P) (x : A.CellComponent a) :
    (d.label (d.horizontal.symm x), d.label x, d.label (d.horizontal x),
      d.label (d.vertical x)) ∈ P.evolution :=
  h _ _ _ _ _ _ _ _ (d.horizontal_predecessor x) (d.horizontal_path x)
    (d.vertical_path x) (d.lab_present _) (d.lab_present _) (d.lab_present _) (d.lab_present _)

theorem horizontal_grammar (h : A.Q3 P) (x : A.CellComponent a) :
    (d.label x, d.label (d.horizontal x)) ∈ P.horizontal :=
  h _ _ _ _ (d.horizontal_path x) (d.lab_present _) (d.lab_present _)

theorem marked_initial (h : A.Q4Marked P) (x : A.CellComponent a)
    (hx : x.val ∈ A.marks) :
    d.label (d.horizontal.symm x) = P.leftWall ∧ d.label x ∈ P.initial :=
  h _ hx _ _ _ (d.horizontal_predecessor x) (d.lab_present _) (d.lab_present _)

theorem input_prefix (h : A.Q4Prefix P) (x : A.CellComponent a)
    (hx : d.label x ∈ P.prefixTrigger) (j : ℕ) (hj : j < P.inputPrefix.length) :
    d.label ((d.horizontal : A.CellComponent a → A.CellComponent a)^[j] x) ∈ P.inputPrefix[j] :=
  h _ _ (d.lab_present x) hx j hj _ _ (d.horizontal_path_iterate j x) (d.lab_present _)

end ClosedDynamics

end Realization

end TuranUniversality.Computation.MatchingSystem
