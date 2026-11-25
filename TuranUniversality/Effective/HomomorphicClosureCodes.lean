module

public import TuranUniversality.Effective.FiniteApproximation
public import TuranUniversality.Density.HomomorphicClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual finite searches for homomorphic images

The numeric test requires a surjective vertex map, preservation of every
source edge, and a preimage for every target edge. Thus it preserves
isolated vertices and agrees with the exact finite homomorphic closure.
-/

namespace TuranUniversality.Effective.Uniform

open FiniteApproximation

def SurjectiveAssignment (n m : ℕ) (xs : List ℕ) : Prop :=
  ∀ b < m, ∃ a < n, xs.getD a 0 = b

instance (n m : ℕ) (xs : List ℕ) : Decidable (SurjectiveAssignment n m xs) := by
  unfold SurjectiveAssignment
  infer_instance

def CoversImageEdges (r : ℕ) (g h : Code) (xs : List ℕ) : Prop :=
  ∀ w ∈ allRows r h.1, Edge r h w →
    ∃ v ∈ allRows r g.1, Edge r g v ∧ SameSet (imageRow xs v) w

instance (r : ℕ) (g h : Code) (xs : List ℕ) : Decidable (CoversImageEdges r g h xs) := by
  unfold CoversImageEdges
  infer_instance

def IsImage (r : ℕ) (g h : Code) : Prop :=
  ∃ xs ∈ assignments g h,
    SurjectiveAssignment g.1 h.1 xs ∧ HomAssignment r g h xs ∧ CoversImageEdges r g h xs

instance (r : ℕ) (g h : Code) : Decidable (IsImage r g h) := by
  unfold IsImage
  infer_instance

theorem surjectiveAssignment_iff (g h : Code) (xs : List ℕ) (hx : xs ∈ assignments g h) :
    SurjectiveAssignment g.1 h.1 xs ↔ Function.Surjective (assignmentMap g h xs hx) := by
  constructor
  · intro hs b
    obtain ⟨a, ha, hab⟩ := hs b.val b.isLt
    exact ⟨⟨a, ha⟩, Fin.ext hab⟩
  · intro hs b hb
    obtain ⟨a, ha⟩ := hs ⟨b, hb⟩
    exact ⟨a.val, a.isLt, congrArg Fin.val ha⟩

theorem coversImageEdges_iff (r : ℕ) (g h : Code) (xs : List ℕ)
    (hx : xs ∈ assignments g h) :
    CoversImageEdges r g h xs ↔
      (decode r h).edges ⊆ (decode r g).edges.image
        (fun e => e.image (assignmentMap g h xs hx)) := by
  constructor
  · intro hh e he
    have hw := edge_canonical r h e he
    obtain ⟨v, _, hv, hsame⟩ := hh (e.toList.map Fin.val)
      ((mem_allRows _ _ _).mpr ⟨hw.1.1, hw.1.2.2⟩) hw
    let d := rowSet g.1 v
    have hd : d ∈ (decode r g).edges := edge_rowSet r g v hv
    refine Finset.mem_image.mpr ⟨d, hd, ?_⟩
    apply Finset.image_injective Fin.val_injective
    rw [assignmentMap_image g h xs hx d v (rowSet_image g.1 v hv.1.2.2)]
    rw [(sameSet_iff _ _).mp hsame, list_map_toFinset, Finset.toList_toFinset]
  · intro hh w _ hw
    let e := rowSet h.1 w
    obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp (hh (edge_rowSet r h w hw))
    have hv := edge_canonical r g d hd
    refine ⟨d.toList.map Fin.val, (mem_allRows _ _ _).mpr ⟨hv.1.1, hv.1.2.2⟩, hv, ?_⟩
    apply (sameSet_iff _ _).mpr
    rw [← assignmentMap_image g h xs hx d (d.toList.map Fin.val)
      (by rw [list_map_toFinset, Finset.toList_toFinset]), hde]
    exact rowSet_image h.1 w hw.1.2.2

theorem isImage_correct (r : ℕ) (g h : Code) :
    IsImage r g h ↔ IsHomomorphicImage (decodeFinite r g) (decodeFinite r h) := by
  constructor
  · rintro ⟨xs, hx, hs, hhom, hc⟩
    refine ⟨assignmentMap g h xs hx, (surjectiveAssignment_iff g h xs hx).mp hs, ?_⟩
    apply Finset.Subset.antisymm ((coversImageEdges_iff r g h xs hx).mp hc)
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact (homAssignment_iff r g h xs hx).mp hhom d hd
  · rintro ⟨f, hs, him⟩
    change (decode r h).edges = (decode r g).edges.image (fun e => e.image f) at him
    obtain ⟨xs, hx, hxs⟩ := map_assignment g h f
    refine ⟨xs, hx, (surjectiveAssignment_iff g h xs hx).mpr (hxs ▸ hs), ?_, ?_⟩
    · apply (homAssignment_iff r g h xs hx).mpr
      intro e he
      rw [hxs, him]
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    · apply (coversImageEdges_iff r g h xs hx).mpr
      rw [hxs, him]

def maxOrder (fs : List Code) : ℕ := listMax (fs.map Prod.fst)

theorem maxOrder_correct (r : ℕ) (fs : List Code) :
    maxOrder fs = (decodeFamily r fs).sup (fun A => A.1) := by
  classical
  apply Nat.le_antisymm
  · apply (listMax_le_iff _ _).mpr
    intro n hn
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
    exact Finset.le_sup (f := fun A : FiniteGraph r => A.1)
      ((mem_decodeFamily r fs _).mpr ⟨g, hg, rfl⟩)
  · apply Finset.sup_le
    intro A hA
    obtain ⟨g, hg, rfl⟩ := (mem_decodeFamily r fs A).mp hA
    exact le_listMax (List.mem_map.mpr ⟨g, hg, rfl⟩)

def closureCodes (r : ℕ) (fs : List Code) : List Code :=
  (boundedCodes r (maxOrder fs)).filter (fun h => ∃ g ∈ fs, IsImage r g h)

theorem closureCodes_decode (r : ℕ) (fs : List Code) :
    decodeFamily r (closureCodes r fs) = homomorphicClosure (decodeFamily r fs) := by
  classical
  ext A
  rw [mem_decodeFamily, mem_homomorphicClosure]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hbound, htest⟩ := List.mem_filter.mp hh
    obtain ⟨g, hg, him⟩ := of_decide_eq_true htest
    exact ⟨(mem_boundedCodes_size hbound).trans_eq (maxOrder_correct r fs),
      decodeFinite r g, (mem_decodeFamily r fs _).mpr ⟨g, hg, rfl⟩,
      (isImage_correct r g h).mp him⟩
  · rintro ⟨hbound, B, hB, him⟩
    obtain ⟨g, hg, rfl⟩ := (mem_decodeFamily r fs B).mp hB
    refine ⟨encodeFinite A, List.mem_filter.mpr ⟨?_, ?_⟩, decode_encodeFinite A⟩
    · apply encode_mem_boundedCodes A
      rw [maxOrder_correct r fs]
      exact hbound
    · apply decide_eq_true
      refine ⟨g, hg, (isImage_correct r g (encodeFinite A)).mpr ?_⟩
      simpa only [decode_encodeFinite] using him

end TuranUniversality.Effective.Uniform
