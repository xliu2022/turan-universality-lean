module

public import TuranUniversality.Density.FamilyBasic
public import TuranUniversality.Density.WeightedSampling

@[expose] public section

/-! # Actual four-vertex records and legal inner objects

The label alphabet has exactly seven elements: five active counts without a
witness, and two witnessed phases (both with active count three).  A local
realization uses ordinary injective avoidance on the active vertex set; in
particular, isolated vertices in a forbidden graph are not dropped silently.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

abbrev Label := Fin 5 ⊕ Bool

namespace Label

def count : Label → ℕ
  | .inl j => j.val
  | .inr _ => 3

def phase : Label → Option Bool
  | .inl _ => none
  | .inr a => some a

theorem card : Fintype.card Label = 7 := by decide

theorem count_le (l : Label) : l.count ≤ 4 := by
  cases l with
  | inl j => exact Nat.le_of_lt_succ j.isLt
  | inr a => exact (by decide : 3 ≤ 4)

theorem count_of_phase {l : Label} {a : Bool} (h : l.phase = some a) :
    l.count = 3 := by cases l <;> simp_all [count, phase]

theorem ext {l k : Label} (hc : l.count = k.count) (hp : l.phase = k.phase) : l = k := by
  cases l <;> cases k <;> simp_all [count, phase]
  exact Fin.ext hc

end Label

variable {V : Type*} [DecidableEq V]

/-- A partial system gives one label to each recorded four-set.  The values of
`label` on unrecorded sets are irrelevant. -/
structure RecordSystem (V : Type*) [DecidableEq V] where
  recorded : RGraph V 4
  label : Finset V → Label

/-- Two actual inner three-graphs on an active vertex set.  The avoidance field
is exactly ordinary avoidance after restricting the ambient carrier to `active`.
Vertices outside `active` are neutral. -/
structure LegalObject (B : Finset (FiniteGraph 3)) (V : Type*) [DecidableEq V] where
  active : Finset V
  inner : Bool → RGraph V 3
  supported : ∀ a e, e ∈ (inner a).edges → e ⊆ active
  onePhase : (inner false).edges = ∅ ∨ (inner true).edges = ∅
  free : ∀ a F, F ∈ B → ∀ f : Fin F.1 → V,
    (∀ v, f v ∈ active) → ¬ F.2.IsEmbedding (inner a) f

namespace LegalObject

variable {B : Finset (FiniteGraph 3)}

def Labels (O : LegalObject B V) (X : Finset V) (l : Label) : Prop :=
  (X ∩ O.active).card = l.count ∧
    ∀ a, X ∩ O.active ∈ (O.inner a).edges ↔ l.phase = some a

theorem Labels.unique {O : LegalObject B V} {X : Finset V} {l k : Label}
    (hl : O.Labels X l) (hk : O.Labels X k) : l = k := by
  apply Label.ext (hl.1.symm.trans hk.1)
  cases hp : l.phase with
  | none =>
    cases hq : k.phase with
    | none => rfl
    | some a => exact False.elim (by simpa [hp] using (hl.2 a).mp ((hk.2 a).mpr hq))
  | some a =>
    exact (hk.2 a).mp ((hl.2 a).mpr hp) |>.symm

theorem phase_exclusive (O : LegalObject B V) (e f : Finset V)
    (he : e ∈ (O.inner false).edges) (hf : f ∈ (O.inner true).edges) : False := by
  rcases O.onePhase with h | h
  · simpa [h] using he
  · simpa [h] using hf

/-- The unique complete record, with a harmless default for sets larger than four. -/
def label (O : LegalObject B V) (X : Finset V) : Label :=
  if X ∩ O.active ∈ (O.inner false).edges then .inr false
  else if X ∩ O.active ∈ (O.inner true).edges then .inr true
  else .inl ⟨min (X ∩ O.active).card 4, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem labels_label (O : LegalObject B V) (X : Finset V) (hX : X.card ≤ 4) :
    O.Labels X (O.label X) := by
  have hc : (X ∩ O.active).card ≤ 4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hX
  unfold label
  split_ifs with hf ht
  · refine ⟨(O.inner false).uniform _ hf, ?_⟩
    intro a
    cases a
    · simp [Label.phase, hf]
    · simp only [Label.phase, Option.some.injEq, Bool.false_eq_true, iff_false]
      exact fun ht => O.phase_exclusive _ _ hf ht
  · refine ⟨(O.inner true).uniform _ ht, ?_⟩
    intro a
    cases a <;> simp [Label.phase, hf, ht]
  · refine ⟨?_, ?_⟩
    · simp [Label.count, min_eq_left hc]
    · intro a; cases a <;> simp [Label.phase, hf, ht]

theorem labels_iff (O : LegalObject B V) (X : Finset V) (hX : X.card ≤ 4) (l : Label) :
    O.Labels X l ↔ O.label X = l :=
  ⟨fun h => (O.labels_label X hX).unique h, fun h => h ▸ O.labels_label X hX⟩

/-- An arbitrary active set with empty inner graphs is legal when all forbidden
graphs have an edge. -/
def empty (B : Finset (FiniteGraph 3))
    (hedges : ∀ F ∈ B, F.2.edges.Nonempty) (A : Finset V) : LegalObject B V where
  active := A
  inner _ := RGraph.empty V 3
  supported := by simp [RGraph.empty]
  onePhase := Or.inl rfl
  free := by
    intro a F hF f _ hf
    obtain ⟨e, he⟩ := hedges F hF
    simpa [RGraph.empty] using hf.2 e he

theorem empty_labels (hedges : ∀ F ∈ B, F.2.edges.Nonempty) (A X : Finset V)
    (j : Fin 5) (hj : (X ∩ A).card = j.val) :
    (empty B hedges A).Labels X (.inl j) := by
  refine ⟨hj, ?_⟩
  intro a
  simp [empty, RGraph.empty, Label.phase]

/-- All currently available records on `S` agree with this complete legal object. -/
def Realizes (O : LegalObject B V) (R : RecordSystem V) (S : Finset V) : Prop :=
  ∀ X ∈ R.recorded.edges, X ⊆ S → O.Labels X (R.label X)

theorem Realizes.mono {O : LegalObject B V} {R : RecordSystem V} {S T : Finset V}
    (h : O.Realizes R S) (hTS : T ⊆ S) : O.Realizes R T :=
  fun X hX hXT => h X hX (hXT.trans hTS)

end LegalObject

namespace RecordSystem

/-- The paper's local cutoff: three anchors, two count witnesses, and a failure
supported on at most `max 8 (v(F)+e(F))` data vertices. -/
def cutoff (B : Finset (FiniteGraph 3)) : ℕ :=
  5 + max 8 (B.sup (fun F => F.1 + F.2.edges.card))

theorem cutoff_ge_thirteen (B : Finset (FiniteGraph 3)) : 13 ≤ cutoff B := by
  have h := le_max_left 8 (B.sup (fun F => F.1 + F.2.edges.card))
  unfold cutoff
  omega

theorem cutoff_ge_forbidden (B : Finset (FiniteGraph 3)) {F : FiniteGraph 3}
    (hF : F ∈ B) : 5 + F.1 + F.2.edges.card ≤ cutoff B := by
  have h := Finset.le_sup (f := fun F : FiniteGraph 3 => F.1 + F.2.edges.card) hF
  have hm := le_max_right 8 (B.sup (fun F => F.1 + F.2.edges.card))
  unfold cutoff
  omega

def LocallyLegal (R : RecordSystem V) (B : Finset (FiniteGraph 3)) : Prop :=
  ∀ S : Finset V, S.card ≤ cutoff B →
    ∃ O : LegalObject B V, O.active ⊆ S ∧ O.Realizes R S

variable [Fintype V]

def neighborhood (R : RecordSystem V) (A : Finset V) : Finset V :=
  (Finset.univ \ A).filter (fun v => insert v A ∈ R.recorded.edges)

@[simp] theorem mem_neighborhood (R : RecordSystem V) (A : Finset V) (v : V) :
    v ∈ R.neighborhood A ↔ v ∉ A ∧ insert v A ∈ R.recorded.edges := by
  simp [neighborhood]

def reportedCount (R : RecordSystem V) (A : Finset V) (v : V) : ℕ :=
  (R.label (insert v A)).count

theorem count_through_anchor {B : Finset (FiniteGraph 3)} (R : RecordSystem V)
    (A S : Finset V) (hAS : A ⊆ S) (O : LegalObject B V) (hO : O.Realizes R S)
    {v : V} (hv : v ∈ R.neighborhood A) (hvS : v ∈ S) :
    R.reportedCount A v = (A ∩ O.active).card + if v ∈ O.active then 1 else 0 := by
  obtain ⟨hvA, hrec⟩ := (R.mem_neighborhood A v).mp hv
  have hc := (hO (insert v A) hrec (Finset.insert_subset hvS hAS)).1
  have hnot : v ∉ A ∩ O.active := fun h => hvA (Finset.mem_inter.mp h).1
  by_cases hact : v ∈ O.active
  · have hi : insert v A ∩ O.active = insert v (A ∩ O.active) := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    simp only [hi, Finset.card_insert_of_notMem hnot] at hc
    simpa only [reportedCount, ite_eq_left hact] using hc.symm
  · have hi : insert v A ∩ O.active = A ∩ O.active := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    simp only [hi] at hc
    simpa only [reportedCount, ite_eq_right hact, add_zero] using hc.symm

end RecordSystem

end TuranUniversality.Structural
