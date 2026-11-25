module

public import TuranUniversality.Effective.StructuralEdges
public import TuranUniversality.Effective.StructuralBounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Finite numeric tests for the actual local canonical class -/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform Structural

theorem rowSet_canonical {n : ℕ} (e : Finset (Fin n)) :
    rowSet n (e.toList.map Fin.val) = e := by
  ext v
  simp [mem_rowSet, Fin.val_inj]

theorem forall_edges_rows (r : ℕ) (g : Code) (P : List ℕ → Prop)
    (Q : Finset (Fin g.1) → Prop)
    (hPQ : ∀ w, Good w.length g.1 w → (P w ↔ Q (rowSet g.1 w))) :
    (∀ w ∈ allRows r g.1, Edge r g w → P w) ↔ ∀ e ∈ (decode r g).edges, Q e := by
  constructor
  · intro h e he
    have hw := edge_canonical r g e he
    have hh := (hPQ _ ⟨rfl, hw.1.2⟩).mp
      (h _ ((mem_allRows _ _ _).mpr ⟨hw.1.1, hw.1.2.2⟩) hw)
    simpa only [rowSet_canonical] using hh
  · intro h w _ hw
    exact (hPQ w ⟨rfl, hw.1.2⟩).mpr (h _ (edge_rowSet r g w hw))

noncomputable def AllGood {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (g : Code) (xs : List ℕ) : Prop :=
  ∀ w ∈ allRows (t + (3 * b + 4)) g.1, Edge (t + (3 * b + 4)) g w → GoodEdge Ω t xs w

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (g : Code) (xs : List ℕ) : Decidable (AllGood Ω t g xs) := by
  unfold AllGood
  infer_instance

theorem allGood_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (g : Code) (xs : List ℕ) (hx : xs ∈ roleAssignments b t g.1) :
    AllGood Ω t g xs ↔ ∀ e ∈ (decode (t + (3 * b + 4)) g).edges,
      Roles.GoodEdge Ω (roleMap b t g.1 xs hx) e :=
  forall_edges_rows _ g _ _ (goodEdge_correct Ω t g.1 xs hx)

noncomputable def LocalOn {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs s : List ℕ) : Prop :=
  ∃ z ∈ objectCodes g.1, Legal fs g.1 z ∧ (∀ a ∈ z.1, a ∈ s) ∧
    ∀ w ∈ allRows (t + (3 * b + 4)) g.1, Edge (t + (3 * b + 4)) g w →
      (∀ a ∈ dataRow xs w, a ∈ s) → Fits Ω t g.1 xs w z

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs s : List ℕ) : Decidable (LocalOn Ω t fs g xs s) := by
  unfold LocalOn
  infer_instance

theorem localOn_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) (hx : xs ∈ roleAssignments b t g.1)
    (hgood : AllGood Ω t g xs) (s : List ℕ) :
    LocalOn Ω t fs g xs s ↔ ∃ O : LegalObject (decodeFamily 3 fs) (Fin g.1),
      O.active ⊆ rowSet g.1 s ∧
        ∀ e ∈ (decode (t + (3 * b + 4)) g).edges,
          Roles.dataSet (roleMap b t g.1 xs hx) e ⊆ rowSet g.1 s →
            Roles.Fits Ω (roleMap b t g.1 xs hx) O e := by
  constructor
  · rintro ⟨z, hz, hleg, hactive, hfit⟩
    have hzgood := subsetRows_good ((mem_objectCodes g.1 z).mp hz).1
    refine ⟨object fs g.1 z hleg, (rowSet_subset_iff_mem z.1 s hzgood.2.2).mpr hactive, ?_⟩
    intro e he hdata
    have hw := edge_canonical (t + (3 * b + 4)) g e he
    have hrows := (mem_allRows _ _ _).mpr ⟨hw.1.1, hw.1.2.2⟩
    have hgw := dataRow_good (show Good (e.toList.map Fin.val).length g.1 (e.toList.map Fin.val)
      from ⟨rfl, hw.1.2⟩) xs
    have hd : ∀ a ∈ dataRow xs (e.toList.map Fin.val), a ∈ s := by
      apply (rowSet_subset_iff_mem _ s hgw.2.2).mp
      rw [rowSet_dataRow b t g.1 xs hx, rowSet_canonical]
      exact hdata
    have hh := (fits_correct Ω fs t g.1 xs hx _ ⟨rfl, hw.1.2⟩
      (hgood _ hrows hw).1 z hleg).mp (hfit _ hrows hw hd)
    simpa only [rowSet_canonical] using hh
  · rintro ⟨O, hactive, hfit⟩
    refine ⟨encodeObject O, encodeObject_mem O, encodeObject_legal fs O, ?_, ?_⟩
    · apply (rowSet_subset_iff_mem (subsetRow O.active) s
        (subsetRows_good (subsetRow_mem O.active)).2.2).mp
      rw [rowSet_subsetRow]
      exact hactive
    · intro w hrows hw hdata
      have hgw := dataRow_good (show Good w.length g.1 w from ⟨rfl, hw.1.2⟩) xs
      apply (fits_correct Ω fs t g.1 xs hx w ⟨rfl, hw.1.2⟩
        (hgood w hrows hw).1 _ (encodeObject_legal fs O)).mpr
      rw [object_encodeObject]
      apply hfit _ (edge_rowSet _ _ _ hw)
      rw [← rowSet_dataRow b t g.1 xs hx w]
      exact (rowSet_subset_iff_mem _ s hgw.2.2).mpr hdata

noncomputable def LocallyLegal {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) : Prop :=
  ∀ s ∈ subsetRows g.1, s.length ≤ cutoff fs → LocalOn Ω t fs g xs s

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) : Decidable (LocallyLegal Ω t fs g xs) := by
  unfold LocallyLegal
  infer_instance

theorem locallyLegal_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) (hx : xs ∈ roleAssignments b t g.1)
    (hgood : AllGood Ω t g xs) :
    LocallyLegal Ω t fs g xs ↔ Roles.LocallyLegal (decodeFamily 3 fs) Ω
      (decode (t + (3 * b + 4)) g) (roleMap b t g.1 xs hx) := by
  constructor
  · intro h S hS
    have hs : (subsetRow S).length ≤ cutoff fs := by
      rw [subsetRow_length, cutoff_correct]
      exact hS
    have hh := (localOn_correct Ω t fs g xs hx hgood (subsetRow S)).mp
      (h _ (subsetRow_mem S) hs)
    simpa only [rowSet_subsetRow] using hh
  · intro h s hs hcard
    apply (localOn_correct Ω t fs g xs hx hgood s).mpr
    apply h
    rw [rowSet_card (subsetRows_good hs), ← cutoff_correct]
    exact hcard

noncomputable def Admissible {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) : Prop :=
  AllGood Ω t g xs ∧ LocallyLegal Ω t fs g xs

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) : Decidable (Admissible Ω t fs g xs) := by
  unfold Admissible
  infer_instance

theorem admissible_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) (xs : List ℕ) (hx : xs ∈ roleAssignments b t g.1) :
    Admissible Ω t fs g xs ↔ Roles.Admissible (decodeFamily 3 fs) Ω
      (decode (t + (3 * b + 4)) g) (roleMap b t g.1 xs hx) := by
  constructor
  · rintro ⟨hgood, hlocal⟩
    exact ⟨(allGood_correct Ω t g xs hx).mp hgood,
      (locallyLegal_correct Ω t fs g xs hx hgood).mp hlocal⟩
  · rintro ⟨hgood, hlocal⟩
    have hg := (allGood_correct Ω t g xs hx).mpr hgood
    exact ⟨hg, (locallyLegal_correct Ω t fs g xs hx hg).mpr hlocal⟩

def RootInjective (n : ℕ) (xs : List ℕ) : Prop :=
  ∀ v < n, ∀ w < n, xs.getD v 0 ≠ 0 → xs.getD v 0 = xs.getD w 0 → v = w

instance (n : ℕ) (xs : List ℕ) : Decidable (RootInjective n xs) := by
  unfold RootInjective
  infer_instance

theorem rootInjective_correct (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n) :
    RootInjective n xs ↔ ∀ v w m,
      roleMap b t n xs hx v = some m → roleMap b t n xs hx w = some m → v = w := by
  constructor
  · intro h v w m hv hw
    apply Fin.ext
    have hv' := (roleMap_some_iff b t n xs hx v m).mp hv
    have hw' := (roleMap_some_iff b t n xs hx w m).mp hw
    exact h v.val v.isLt w.val w.isLt (by omega) (hv'.trans hw'.symm)
  · intro h v hv w hw hnon heq
    have hnone : roleMap b t n xs hx ⟨v, hv⟩ ≠ none :=
      fun hh => hnon ((roleMap_none_iff b t n xs hx _).mp hh)
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hnone
    have hw' : roleMap b t n xs hx ⟨w, hw⟩ = some m := by
      apply (roleMap_some_iff b t n xs hx _ m).mpr
      rw [← heq]
      exact (roleMap_some_iff b t n xs hx _ m).mp hm
    exact congrArg Fin.val (h ⟨v, hv⟩ ⟨w, hw⟩ m hm hw')

noncomputable def Canonical {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) : Prop :=
  ∃ xs ∈ roleAssignments b t g.1, Admissible Ω t fs g xs

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) : Decidable (Canonical Ω t fs g) := by
  unfold Canonical
  infer_instance

noncomputable def Admits {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) : Prop :=
  ∃ xs ∈ roleAssignments b t g.1, Admissible Ω t fs g xs ∧ RootInjective g.1 xs

noncomputable instance {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) : Decidable (Admits Ω t fs g) := by
  unfold Admits
  infer_instance

theorem canonical_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (t : ℕ) (fs : List Code) (g : Code) :
    Canonical Ω t fs g ↔ Structural.Canonical (decodeFamily 3 fs) Ω (decode (t + (3 * b + 4)) g) := by
  rw [Roles.canonical_iff _ Ω hdis]
  constructor
  · rintro ⟨xs, hx, hh⟩
    exact ⟨roleMap b t g.1 xs hx, (admissible_correct Ω t fs g xs hx).mp hh⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨xs, hx, hxs⟩ := encode_roleMap b t g.1 ρ
    refine ⟨xs, hx, (admissible_correct Ω t fs g xs hx).mpr ?_⟩
    rwa [hxs]

theorem admits_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) (g : Code) :
    Admits Ω t fs g ↔ Rooted.Admits (decodeFamily 3 fs) Ω (decode (t + (3 * b + 4)) g) := by
  rw [Rooted.admits_iff_singleton_root_roles]
  constructor
  · rintro ⟨xs, hx, hh, hi⟩
    exact ⟨roleMap b t g.1 xs hx, (admissible_correct Ω t fs g xs hx).mp hh,
      (rootInjective_correct b t g.1 xs hx).mp hi⟩
  · rintro ⟨ρ, hρ, hi⟩
    obtain ⟨xs, hx, hxs⟩ := encode_roleMap b t g.1 ρ
    refine ⟨xs, hx, (admissible_correct Ω t fs g xs hx).mpr ?_,
      (rootInjective_correct b t g.1 xs hx).mpr ?_⟩ <;> rwa [hxs]

end TuranUniversality.Effective.StructuralCodes
