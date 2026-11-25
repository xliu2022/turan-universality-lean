module

public import TuranUniversality.Structural.RecordPinned

@[expose] public section

/-! # Claim 7.2: a common neighborhood has a complete legal realization

Counts through the three anchors either determine every neighbor's type, or
all such counts are equal and every available neighborhood record is of one
constant type.  The first case uses the explicit finite obstruction witnesses
from `RecordPinned`; the second uses empty inner graphs.
-/

namespace TuranUniversality.Structural

theorem Label.eq_plain_of_count {l : Label} (j : Fin 5) (hj : j.val ≠ 3)
    (h : l.count = j.val) : l = .inl j := by
  cases l with
  | inl k => exact congrArg Sum.inl (Fin.ext h)
  | inr a => exact False.elim (hj h.symm)

namespace LegalObject

variable {V : Type*} [DecidableEq V] {B : Finset (FiniteGraph 3)}

theorem label_if_same_type (O : LegalObject B V) {X : Finset V} {l : Label}
    (hX : X.card = 4) (hl : O.Labels X l) (v : V)
    (hsame : ∀ w ∈ X, w ∈ O.active ↔ v ∈ O.active) :
    l = if v ∈ O.active then .inl 4 else .inl 0 := by
  classical
  by_cases hv : v ∈ O.active
  · rw [ite_eq_left hv]
    apply Label.eq_plain_of_count 4 (by decide)
    have hi : X ∩ O.active = X :=
      Finset.inter_eq_left.mpr (fun w hw => (hsame w hw).mpr hv)
    simpa [hi, hX] using hl.1.symm
  · rw [ite_eq_right hv]
    apply Label.eq_plain_of_count 0 (by decide)
    have hi : X ∩ O.active = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hv ((hsame w (Finset.mem_inter.mp hw).1).mp (Finset.mem_inter.mp hw).2)
    simpa [hi] using hl.1.symm

end LegalObject

namespace RecordSystem

variable {V : Type*} [DecidableEq V] [Fintype V]
  {R : RecordSystem V} {B : Finset (FiniteGraph 3)}

private theorem anchor_pair_size (A : Finset V) (hA : A.card = 3) (u v : V) :
    (insert u (insert v A)).card ≤ 5 := by
  have h1 := Finset.card_insert_le v A
  have h2 := Finset.card_insert_le u (insert v A)
  omega

theorem counts_adjacent (h : R.LocallyLegal B) (A : Finset V) (hA : A.card = 3)
    {u v : V} (hu : u ∈ R.neighborhood A) (hv : v ∈ R.neighborhood A) :
    R.reportedCount A u ≤ R.reportedCount A v + 1 := by
  let S := insert u (insert v A)
  have hS : S.card ≤ cutoff B :=
    (anchor_pair_size A hA u v).trans (by have := cutoff_ge_thirteen B; omega)
  obtain ⟨O, _, hO⟩ := h S hS
  have hAS : A ⊆ S := fun w hw => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
  have huS : u ∈ S := Finset.mem_insert_self _ _
  have hvS : v ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcu := R.count_through_anchor A S hAS O hO hu huS
  have hcv := R.count_through_anchor A S hAS O hO hv hvS
  split_ifs at hcu hcv <;> omega

theorem type_recovery (A S : Finset V) (hAS : A ⊆ S)
    (O : LegalObject B V) (hO : O.Realizes R S) {u v : V} (s : ℕ)
    (hu : u ∈ R.neighborhood A) (hv : v ∈ R.neighborhood A)
    (huS : u ∈ S) (hvS : v ∈ S)
    (hcu : R.reportedCount A u = s) (hcv : R.reportedCount A v = s + 1)
    {w : V} (hw : w ∈ R.neighborhood A) (hwS : w ∈ S) :
    w ∈ O.active ↔ R.reportedCount A w = s + 1 := by
  have h1 := R.count_through_anchor A S hAS O hO hu huS
  have h2 := R.count_through_anchor A S hAS O hO hv hvS
  have hb : (A ∩ O.active).card = s := by
    split_ifs at h1 h2 <;> omega
  have h3 := R.count_through_anchor A S hAS O hO hw hwS
  rw [hb] at h3
  constructor
  · intro hwO
    simpa only [ite_eq_left hwO] using h3
  · intro hc
    by_contra hn
    simp only [ite_eq_right hn, add_zero] at h3
    omega

theorem pinned_of_two_counts (h : R.LocallyLegal B) (A : Finset V) (hA : A.card = 3)
    {u v : V} (s : ℕ) (hu : u ∈ R.neighborhood A) (hv : v ∈ R.neighborhood A)
    (hcu : R.reportedCount A u = s) (hcv : R.reportedCount A v = s + 1) :
    R.PinnedLocallyLegal B (R.neighborhood A)
      ((R.neighborhood A).filter (fun w => R.reportedCount A w = s + 1)) := by
  intro T hTN hTb
  let S := insert u (insert v A) ∪ T
  have hS : S.card ≤ cutoff B := by
    have h1 := anchor_pair_size A hA u v
    have h2 := Finset.card_union_le (insert u (insert v A)) T
    rw [cutoff_eq]
    dsimp only [S]
    omega
  obtain ⟨O, _, hO⟩ := h S hS
  have hAS : A ⊆ S := fun w hw =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
  have huS : u ∈ S := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  have hvS : v ∈ S := Finset.mem_union_left _
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  refine ⟨O, hO.mono Finset.subset_union_right, ?_⟩
  intro w hw
  simpa only [Finset.mem_filter, hTN hw, true_and] using
    type_recovery A S hAS O hO s hu hv huS hvS hcu hcv (hTN hw)
      (Finset.mem_union_right _ hw)

theorem same_type_of_same_count (A S : Finset V) (hAS : A ⊆ S)
    (O : LegalObject B V) (hO : O.Realizes R S) {u v : V}
    (hu : u ∈ R.neighborhood A) (hv : v ∈ R.neighborhood A)
    (huS : u ∈ S) (hvS : v ∈ S)
    (hc : R.reportedCount A u = R.reportedCount A v) :
    u ∈ O.active ↔ v ∈ O.active := by
  have h1 := R.count_through_anchor A S hAS O hO hu huS
  have h2 := R.count_through_anchor A S hAS O hO hv hvS
  constructor
  · intro huO
    by_contra hvO
    simp only [ite_eq_left huO, ite_eq_right hvO, add_zero] at h1 h2
    omega
  · intro hvO
    by_contra huO
    simp only [ite_eq_left hvO, ite_eq_right huO, add_zero] at h1 h2
    omega

theorem constant_label_shape (h : R.LocallyLegal B) (A : Finset V) (hA : A.card = 3)
    (hc : ∀ u ∈ R.neighborhood A, ∀ v ∈ R.neighborhood A,
      R.reportedCount A u = R.reportedCount A v)
    {X : Finset V} (hX : X ∈ R.recorded.edges) (hXN : X ⊆ R.neighborhood A) :
    R.label X = .inl 0 ∨ R.label X = .inl 4 := by
  have hXcard := R.recorded.uniform X hX
  have hS : (A ∪ X).card ≤ cutoff B := by
    have h1 := Finset.card_union_le A X
    have h2 := cutoff_ge_thirteen B
    omega
  obtain ⟨O, _, hO⟩ := h (A ∪ X) hS
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  have hl := O.label_if_same_type hXcard (hO X hX Finset.subset_union_right) v
    (fun w hw => same_type_of_same_count A (A ∪ X) Finset.subset_union_left O hO
      (hXN hw) (hXN hv) (Finset.mem_union_right _ hw) (Finset.mem_union_right _ hv)
      (hc w (hXN hw) v (hXN hv)))
  split_ifs at hl
  · exact Or.inr hl
  · exact Or.inl hl

theorem constant_labels_equal (h : R.LocallyLegal B) (A : Finset V) (hA : A.card = 3)
    (hc : ∀ u ∈ R.neighborhood A, ∀ v ∈ R.neighborhood A,
      R.reportedCount A u = R.reportedCount A v)
    {X Y : Finset V} (hX : X ∈ R.recorded.edges) (hXN : X ⊆ R.neighborhood A)
    (hY : Y ∈ R.recorded.edges) (hYN : Y ⊆ R.neighborhood A) : R.label X = R.label Y := by
  let S := A ∪ X ∪ Y
  have hXcard := R.recorded.uniform X hX
  have hYcard := R.recorded.uniform Y hY
  have hS : S.card ≤ cutoff B := by
    have h1 := Finset.card_union_le A X
    have h2 := Finset.card_union_le (A ∪ X) Y
    have h3 := cutoff_ge_thirteen B
    dsimp only [S]
    omega
  obtain ⟨O, _, hO⟩ := h S hS
  have hAS : A ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hXS : X ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hYS : Y ⊆ S := Finset.subset_union_right
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  have ht {w : V} (hwN : w ∈ R.neighborhood A) (hwS : w ∈ S) :
      w ∈ O.active ↔ v ∈ O.active :=
    same_type_of_same_count A S hAS O hO hwN (hXN hv) hwS (hXS hv)
      (hc w hwN v (hXN hv))
  have hx := O.label_if_same_type hXcard (hO X hX hXS) v (fun w hw => ht (hXN hw) (hXS hw))
  have hy := O.label_if_same_type hYcard (hO Y hY hYS) v (fun w hw => ht (hYN hw) (hYS hw))
  exact hx.trans hy.symm

theorem realization_of_constant_counts (h : R.LocallyLegal B)
    (hedges : ∀ F ∈ B, F.2.edges.Nonempty) (A : Finset V) (hA : A.card = 3)
    (hc : ∀ u ∈ R.neighborhood A, ∀ v ∈ R.neighborhood A,
      R.reportedCount A u = R.reportedCount A v) :
    ∃ O : LegalObject B V, O.active ⊆ R.neighborhood A ∧ O.Realizes R (R.neighborhood A) := by
  classical
  by_cases hex : ∃ X ∈ R.recorded.edges, X ⊆ R.neighborhood A
  · obtain ⟨X, hX, hXN⟩ := hex
    rcases constant_label_shape h A hA hc hX hXN with hl | hl
    · refine ⟨LegalObject.empty B hedges ∅, Finset.empty_subset _, ?_⟩
      intro Y hY hYN
      have hlabel : R.label Y = .inl 0 :=
        (constant_labels_equal h A hA hc hY hYN hX hXN).trans hl
      rw [hlabel]
      exact LegalObject.empty_labels hedges ∅ Y 0 (by simp)
    · refine ⟨LegalObject.empty B hedges (R.neighborhood A), Finset.Subset.refl _, ?_⟩
      intro Y hY hYN
      have hlabel : R.label Y = .inl 4 :=
        (constant_labels_equal h A hA hc hY hYN hX hXN).trans hl
      rw [hlabel]
      apply LegalObject.empty_labels hedges (R.neighborhood A) Y 4
      rw [Finset.inter_eq_left.mpr hYN, R.recorded.uniform Y hY]
      rfl
  · refine ⟨LegalObject.empty B hedges ∅, Finset.empty_subset _, ?_⟩
    intro X hX hXN
    exact False.elim (hex ⟨X, hX, hXN⟩)

/-- Claim 7.2, for the actual record system and the paper's exact local cutoff. -/
theorem commonLink (h : R.LocallyLegal B) (hedges : ∀ F ∈ B, F.2.edges.Nonempty)
    (A : Finset V) (hA : A.card = 3) :
    ∃ O : LegalObject B V, O.active ⊆ R.neighborhood A ∧ O.Realizes R (R.neighborhood A) := by
  classical
  by_cases hpair : ∃ u ∈ R.neighborhood A, ∃ v ∈ R.neighborhood A,
      R.reportedCount A v = R.reportedCount A u + 1
  · obtain ⟨u, hu, v, hv, hcv⟩ := hpair
    let U := (R.neighborhood A).filter (fun w =>
      R.reportedCount A w = R.reportedCount A u + 1)
    have hp : R.PinnedLocallyLegal B (R.neighborhood A) U :=
      pinned_of_two_counts h A hA (R.reportedCount A u) hu hv rfl hcv
    have hU : U ⊆ R.neighborhood A := Finset.filter_subset _ _
    obtain ⟨O, heq, hO⟩ := R.exists_realization_of_pinned B (R.neighborhood A) U hU hp
    exact ⟨O, heq ▸ hU, hO⟩
  · apply realization_of_constant_counts h hedges A hA
    intro u hu v hv
    have h1 := counts_adjacent h A hA hu hv
    have h2 := counts_adjacent h A hA hv hu
    have h3 : R.reportedCount A v ≠ R.reportedCount A u + 1 :=
      fun heq => hpair ⟨u, hu, v, hv, heq⟩
    have h4 : R.reportedCount A u ≠ R.reportedCount A v + 1 :=
      fun heq => hpair ⟨v, hv, u, hu, heq⟩
    omega

end RecordSystem
end TuranUniversality.Structural
