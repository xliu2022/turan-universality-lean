module

public import TuranUniversality.Effective.StructuralRoleEncoding

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact numeric support and label checks for ordinary edges -/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform Structural

def rootVertex {b t : ℕ} {V : Type*} (m : Rooted.Roots b t) : Compiled.Vertex b t V :=
  (Equiv.sumAssoc (Fin t) (Support.Vertex b) V) (.inl m)

theorem place_eq_rootVertex {b t : ℕ} {V : Type*}
    (ρ : V → Option (Rooted.Roots b t)) (v : V) (m : Rooted.Roots b t) :
    Rooted.place ρ v = rootVertex m ↔ ρ v = some m := by
  cases hm : ρ v with
  | none => cases m <;> simp [Rooted.place, Selector.rootedVertex, rootVertex, hm]
  | some a => cases a <;> cases m <;>
      simp [Rooted.place, Selector.rootedVertex, rootVertex, hm]

theorem root_mem_image {b t : ℕ} {V : Type*} [DecidableEq V]
    (ρ : V → Option (Rooted.Roots b t)) (e : Finset V) (m : Rooted.Roots b t) :
    rootVertex m ∈ e.image (Rooted.place ρ) ↔ ∃ v ∈ e, ρ v = some m := by
  simp only [Finset.mem_image, place_eq_rootVertex]

theorem root_mem_edge {b t : ℕ} {V : Type*} [DecidableEq V]
    (Z : Finset (Support.Vertex b)) (X : Finset V) (m : Rooted.Roots b t) :
    rootVertex m ∈ Compiled.edge t Z X ↔ m ∈ Finset.univ.disjSum Z := by
  cases m <;> simp [rootVertex]

theorem image_eq_edge_iff {b t : ℕ} {V : Type*} [DecidableEq V] [Fintype V]
    (ρ : V → Option (Rooted.Roots b t)) (e : Finset V) (Z : Finset (Support.Vertex b)) :
    e.image (Rooted.place ρ) = Compiled.edge t Z (Roles.dataSet ρ e) ↔
      ∀ m, (∃ v ∈ e, ρ v = some m) ↔ m ∈ Finset.univ.disjSum Z := by
  constructor
  · intro h m
    rw [← root_mem_image, h, root_mem_edge]
  · intro h
    ext v
    rcases v with i | (u | v)
    · have hh := h (.inl i)
      rw [← root_mem_image, ← root_mem_edge Z (Roles.dataSet ρ e)] at hh
      exact hh
    · have hh := h (.inr u)
      rw [← root_mem_image, ← root_mem_edge Z (Roles.dataSet ρ e)] at hh
      exact hh
    · rw [Compiled.mem_edge_data, Roles.data_mem_image]

theorem mem_support_image {b : ℕ} (z : List ℕ) (v : Support.Vertex b) :
    v ∈ (rowSet (5 * b) z).image (supportEquiv b).symm ↔ (supportEquiv b v).val ∈ z := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
    simpa only [Equiv.apply_symm_apply] using (mem_rowSet (5 * b) z u).mp hu
  · intro h
    exact Finset.mem_image.mpr ⟨supportEquiv b v, (mem_rowSet _ _ _).mpr h,
      (supportEquiv b).symm_apply_apply v⟩

theorem root_expected_iff (b t : ℕ) (z : List ℕ) (m : Rooted.Roots b t) :
    ((rootEquiv b t m).val < t ∨ (rootEquiv b t m).val - t ∈ z) ↔
      m ∈ Finset.univ.disjSum ((rowSet (5 * b) z).image (supportEquiv b).symm) := by
  cases m with
  | inl i => simp [i.isLt]
  | inr v =>
      simp only [rootEquiv_right, Nat.add_sub_cancel_left, Finset.mem_disjSum,
        Sum.isRight_inr, Sum.getRight_inr, mem_support_image]
      simp

def RootCheck (b t : ℕ) (xs w z : List ℕ) : Prop :=
  ∀ j < t + 5 * b, (j + 1 ∈ imageRow xs w ↔ j < t ∨ j - t ∈ z)

instance (b t : ℕ) (xs w z : List ℕ) : Decidable (RootCheck b t xs w z) := by
  unfold RootCheck
  infer_instance

theorem rootCheck_correct (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (w : List ℕ) (hw : ∀ a ∈ w, a < n) (z : List ℕ) :
    RootCheck b t xs w z ↔
      (rowSet n w).image (Rooted.place (roleMap b t n xs hx)) =
        Compiled.edge t ((rowSet (5 * b) z).image (supportEquiv b).symm)
          (Roles.dataSet (roleMap b t n xs hx) (rowSet n w)) := by
  rw [image_eq_edge_iff]
  constructor
  · intro h m
    rw [← root_mem_imageRow b t n xs hx w hw m, ← root_expected_iff b t z m]
    exact h _ (rootEquiv b t m).isLt
  · intro h j hj
    let m := (rootEquiv b t).symm ⟨j, hj⟩
    have hm : (rootEquiv b t m).val = j := congrArg Fin.val ((rootEquiv b t).apply_symm_apply _)
    have hh := h m
    rw [← root_mem_imageRow b t n xs hx w hw m, ← root_expected_iff b t z m, hm] at hh
    exact hh

noncomputable def Declares {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (xs w : List ℕ) (l : ℕ) : Prop :=
  ∃ z ∈ allRows (3 * b) (5 * b), Edge (3 * b) (supportCode Ω l) z ∧ RootCheck b t xs w z

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (xs w : List ℕ) (l : ℕ) : Decidable (Declares Ω t xs w l) := by
  unfold Declares
  infer_instance

theorem declares_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (w : List ℕ) (hw : ∀ a ∈ w, a < n) (l : Fin 7) :
    Declares Ω t xs w l.val ↔
      Roles.Declares Ω (roleMap b t n xs hx) (rowSet n w) (CodePools.labelEquiv l) := by
  constructor
  · rintro ⟨z, _, hz, hroot⟩
    have he := edge_rowSet (3 * b) (supportCode Ω l.val) z hz
    rw [decode_supportCode] at he
    exact ⟨(rowSet (5 * b) z).image (supportEquiv b).symm,
      (supportGraph_image_mem Ω _ _).mp he,
      (rootCheck_correct b t n xs hx w hw z).mp hroot⟩
  · rintro ⟨Z, hZ, him⟩
    let Y := Z.image (supportEquiv b)
    have hY : Y ∈ (supportGraph Ω (CodePools.labelEquiv l)).edges := by
      apply (supportGraph_image_mem Ω _ Y).mpr
      simpa only [Y, Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id'] using hZ
    let z := subsetRow Y
    have hzset : (rowSet (5 * b) z).image (supportEquiv b).symm = Z := by
      rw [show rowSet (5 * b) z = Y from rowSet_subsetRow Y]
      simp [Y, Finset.image_image]
    have hgood := subsetRows_good (subsetRow_mem Y)
    have hlen : z.length = 3 * b := by
      rw [subsetRow_length]
      exact (supportGraph Ω (CodePools.labelEquiv l)).uniform Y hY
    refine ⟨z, (mem_allRows _ _ _).mpr ⟨hlen, hgood.2.2⟩, ?_, ?_⟩
    · apply (edge_iff_rowSet_of_distinct (supportCode Ω l.val).2 z hgood.2.1 hgood.2.2).mpr
      change rowSet (5 * b) z ∈ (decode (3 * b) (supportCode Ω l.val)).edges
      rw [decode_supportCode, show rowSet (5 * b) z = Y from rowSet_subsetRow Y]
      exact hY
    · apply (rootCheck_correct b t n xs hx w hw z).mpr
      rw [hzset]
      exact him

noncomputable def GoodEdge {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (xs w : List ℕ) : Prop :=
  (dataRow xs w).length = 4 ∧ ∃ l < 7, Declares Ω t xs w l

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (xs w : List ℕ) : Decidable (GoodEdge Ω t xs w) := by
  unfold GoodEdge
  infer_instance

theorem goodEdge_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (w : List ℕ) (hw : Good w.length n w) :
    GoodEdge Ω t xs w ↔ Roles.GoodEdge Ω (roleMap b t n xs hx) (rowSet n w) := by
  have hc : (Roles.dataSet (roleMap b t n xs hx) (rowSet n w)).card = (dataRow xs w).length := by
    rw [← rowSet_dataRow]
    exact rowSet_card (dataRow_good hw xs)
  unfold GoodEdge Roles.GoodEdge
  rw [hc]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨l, hl, hh⟩
    exact ⟨CodePools.labelEquiv ⟨l, hl⟩, (declares_correct Ω t n xs hx w hw.2.2 ⟨l, hl⟩).mp hh⟩
  · rintro ⟨l, hl⟩
    let k := CodePools.labelEquiv.symm l
    exact ⟨k.val, k.isLt, (declares_correct Ω t n xs hx w hw.2.2 k).mpr (by simpa [k] using hl)⟩

noncomputable def Fits {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t n : ℕ) (xs w : List ℕ) (z : ObjectCode) : Prop :=
  ∃ l < 7, Labels n z (dataRow xs w) l ∧ Declares Ω t xs w l

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t n : ℕ) (xs w : List ℕ) (z : ObjectCode) : Decidable (Fits Ω t n xs w z) := by
  unfold Fits
  infer_instance

theorem fits_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (fs : List Code) (t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (w : List ℕ) (hw : Good w.length n w) (hc : (dataRow xs w).length = 4)
    (z : ObjectCode) (hz : Legal fs n z) :
    Fits Ω t n xs w z ↔ Roles.Fits Ω (roleMap b t n xs hx) (object fs n z hz) (rowSet n w) := by
  let O := object fs n z hz
  let X := Roles.dataSet (roleMap b t n xs hx) (rowSet n w)
  have hX : X.card = 4 := by
    rw [show X = rowSet n (dataRow xs w) from (rowSet_dataRow b t n xs hx w).symm,
      rowSet_card (dataRow_good hw xs), hc]
  rw [Roles.fits_iff_declares Ω _ _ _ hX]
  constructor
  · rintro ⟨l, hl, hlabel, hdeclare⟩
    have heq := (O.labels_iff X (le_of_eq hX) (CodePools.labelEquiv ⟨l, hl⟩)).mp
      (by simpa only [rowSet_dataRow b t n xs hx w, O, X] using
        (labels_correct fs n z hz (dataRow xs w) (dataRow_good hw xs) ⟨l, hl⟩).mp hlabel)
    rw [heq]
    exact (declares_correct Ω t n xs hx w hw.2.2 ⟨l, hl⟩).mp hdeclare
  · intro hdeclare
    let l := CodePools.labelEquiv.symm (O.label X)
    have hl : CodePools.labelEquiv l = O.label X := CodePools.labelEquiv.apply_symm_apply _
    refine ⟨l.val, l.isLt, ?_, ?_⟩
    · apply (labels_correct fs n z hz (dataRow xs w) (dataRow_good hw xs) l).mpr
      rw [rowSet_dataRow, hl]
      exact O.labels_label X (le_of_eq hX)
    · apply (declares_correct Ω t n xs hx w hw.2.2 l).mpr
      rw [hl]
      exact hdeclare

end TuranUniversality.Effective.StructuralCodes
