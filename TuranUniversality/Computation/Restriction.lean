module

public import TuranUniversality.Computation.Pullback

/-! # Restricting a finite matching realization to a vertex subset -/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

open TuranUniversality.Weighted

variable {D Alphabet : Type*} [DecidableEq D]

/-- Keep exactly the pairs whose two endpoints are retained. -/
def restrictMatching {C B : Finset D} (P : PartialMatching C B) (U : Finset D) :
    PartialMatching (C ∩ U) (B ∩ U) where
  pairs := P.pairs.filter fun p => p.1 ∈ U ∧ p.2 ∈ U
  left_mem := by
    intro p hp
    exact Finset.mem_inter.mpr ⟨P.left_mem p (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2.1⟩
  right_mem := by
    intro p hp
    exact Finset.mem_inter.mpr ⟨P.right_mem p (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2.2⟩
  left_injective := by
    intro p hp q hq h
    exact P.left_injective (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 h
  right_injective := by
    intro p hp q hq h
    exact P.right_injective (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 h

@[simp] theorem mem_restrictMatching {C B : Finset D} (P : PartialMatching C B)
    (U : Finset D) (x y : D) :
    (x, y) ∈ (restrictMatching P U).pairs ↔ (x, y) ∈ P.pairs ∧ x ∈ U ∧ y ∈ U := by
  simp [restrictMatching]

namespace Realization

variable (A : Realization D Alphabet)

def restrict (U : Finset D) : Realization D Alphabet where
  cells := A.cells ∩ U
  colors := A.colors ∩ U
  disjoint := A.disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
  label := A.label
  J := restrictMatching A.J U
  R := restrictMatching A.R U
  S := restrictMatching A.S U
  marks := A.marks ∩ U
  marks_cells := by
    intro a ha
    exact Finset.mem_inter.mpr ⟨A.marks_cells (Finset.mem_inter.mp ha).1,
      (Finset.mem_inter.mp ha).2⟩

@[simp] theorem restrict_J (U : Finset D) (x y : D) :
    (x, y) ∈ (A.restrict U).J.pairs ↔ (x, y) ∈ A.J.pairs ∧ x ∈ U ∧ y ∈ U :=
  mem_restrictMatching A.J U x y

@[simp] theorem restrict_R (U : Finset D) (x y : D) :
    (x, y) ∈ (A.restrict U).R.pairs ↔ (x, y) ∈ A.R.pairs ∧ x ∈ U ∧ y ∈ U :=
  mem_restrictMatching A.R U x y

@[simp] theorem restrict_S (U : Finset D) (x y : D) :
    (x, y) ∈ (A.restrict U).S.pairs ↔ (x, y) ∈ A.S.pairs ∧ x ∈ U ∧ y ∈ U :=
  mem_restrictMatching A.S U x y

@[simp] theorem restrict_label (U : Finset D) (x : D) : (A.restrict U).label x = A.label x := rfl

@[simp] theorem restrict_marks (U : Finset D) (x : D) :
    x ∈ (A.restrict U).marks ↔ x ∈ A.marks ∧ x ∈ U := Finset.mem_inter

def restrictionPullback (U : Finset D) : Pullback (A.restrict U) A where
  domain := U
  map := Subtype.val
  injective := Subtype.val_injective
  J_domain := by intro x y h; exact ((A.restrict_J U x y).mp h).2
  R_domain := by intro x y h; exact ((A.restrict_R U x y).mp h).2
  S_domain := by intro x y h; exact ((A.restrict_S U x y).mp h).2
  marks_domain := Finset.inter_subset_right
  J_preserve := by intro x y h; exact ((A.restrict_J U x y).mp h).1
  R_preserve := by intro x y h; exact ((A.restrict_R U x y).mp h).1
  S_preserve := by intro x y h; exact ((A.restrict_S U x y).mp h).1
  label_preserve := by intros; rfl
  marks_preserve := by intro a h; exact (Finset.mem_inter.mp h).1

theorem restrict_legal [DecidableEq Alphabet] (P : Specification Alphabet)
    (h : A.Legal P) (U : Finset D) : (A.restrict U).Legal P :=
  (A.restrictionPullback U).legal P h

theorem h_restrict_mono {U W : Finset D} (hUW : U ⊆ W) {x y : D}
    (h : (A.restrict U).H x y) : (A.restrict W).H x y := by
  obtain ⟨b, hj, hr⟩ := h
  obtain ⟨hj, hx, hb⟩ := (A.restrict_J U x b).mp hj
  obtain ⟨hr, _, hy⟩ := (A.restrict_R U b y).mp hr
  exact ⟨b, (A.restrict_J W x b).mpr ⟨hj, hUW hx, hUW hb⟩,
    (A.restrict_R W b y).mpr ⟨hr, hUW hb, hUW hy⟩⟩

theorem path_restrict_mono {U W : Finset D} (hUW : U ⊆ W) {n : ℕ} {x y : D}
    (h : Path (A.restrict U).H n x y) : Path (A.restrict W).H n x y :=
  path_mono (fun _ _ h => A.h_restrict_mono hUW h) h

theorem retain_h {U : Finset D} {x b y : D}
    (hj : (x, b) ∈ A.J.pairs) (hr : (b, y) ∈ A.R.pairs)
    (hx : x ∈ U) (hb : b ∈ U) (hy : y ∈ U) : (A.restrict U).H x y :=
  ⟨b, (A.restrict_J U x b).mpr ⟨hj, hx, hb⟩,
    (A.restrict_R U b y).mpr ⟨hr, hb, hy⟩⟩

theorem retain_v {U : Finset D} {x b y : D}
    (hj : (x, b) ∈ A.J.pairs) (hs : (b, y) ∈ A.S.pairs)
    (hx : x ∈ U) (hb : b ∈ U) (hy : y ∈ U) : (A.restrict U).V x y :=
  ⟨b, (A.restrict_J U x b).mpr ⟨hj, hx, hb⟩,
    (A.restrict_S U b y).mpr ⟨hs, hb, hy⟩⟩

theorem retain_lab {U : Finset D} {x b : D} {a : Alphabet}
    (hj : (x, b) ∈ A.J.pairs) (hl : A.label b = a)
    (hx : x ∈ U) (hb : b ∈ U) : (A.restrict U).Lab x a :=
  ⟨b, (A.restrict_J U x b).mpr ⟨hj, hx, hb⟩, hl⟩

/-- A length-`n` witnessed horizontal path uses at most `2n+1` vertices,
including the intermediate `J` colors.  Repeated witnesses are allowed. -/
theorem path_small_support {n : ℕ} {x y : D} (h : Path A.H n x y) :
    ∃ U : Finset D, U.card ≤ 2 * n + 1 ∧ x ∈ U ∧ y ∈ U ∧
      Path (A.restrict U).H n x y := by
  induction n generalizing x with
  | zero =>
    have hxy : x = y := h
    subst y
    exact ⟨{x}, by simp, by simp, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨z, ⟨b, hj, hr⟩, hz⟩ := h
    obtain ⟨U, hU, hzU, hyU, hp⟩ := ih hz
    let W := insert x (insert b U)
    have hUW : U ⊆ W := by intro a ha; simp [W, ha]
    have hxW : x ∈ W := by simp [W]
    have hbW : b ∈ W := by simp [W]
    refine ⟨W, ?_, hxW, hUW hyU, z, ?_, A.path_restrict_mono hUW hp⟩
    · have hcard : W.card ≤ U.card + 2 := by
        exact (Finset.card_insert_le _ _).trans (by
          have := Finset.card_insert_le b U
          omega)
      omega
    · exact ⟨b, (A.restrict_J W x b).mpr ⟨hj, hxW, hbW⟩,
        (A.restrict_R W b z).mpr ⟨hr, hbW, hUW hzU⟩⟩

end Realization
end TuranUniversality.Computation.MatchingSystem
