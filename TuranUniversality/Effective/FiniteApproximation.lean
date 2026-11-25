module

public import TuranUniversality.Effective.FiniteEdgeCount
public import TuranUniversality.Effective.UniformDecodeFamily
public import TuranUniversality.Density.HomFreeMax

@[expose] public section

/-! # Exact finite searches for uniform forbidden families

All graph and family inputs are the existing natural-number list codes. The
rank and the size of the search are also inputs. No decidability oracle is
part of the algorithm: homomorphisms are checked by enumerating finite maps.
-/

namespace TuranUniversality.Effective.FiniteApproximation

open TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

abbrev FamilyCode := List Code

/-- The actual finite-map test, retaining every decoded forbidden graph. -/
def FamilyHomFreeCode (r : ℕ) (fs : FamilyCode) (g : Code) : Prop :=
  ∀ f ∈ fs, ¬ HasHom r f g

instance (r : ℕ) (fs : FamilyCode) (g : Code) :
    Decidable (FamilyHomFreeCode r fs g) := by
  unfold FamilyHomFreeCode
  infer_instance

theorem familyHomFreeCode_correct (r : ℕ) (fs : FamilyCode) (g : Code) :
    FamilyHomFreeCode r fs g ↔ familyHomFree (decodeFamily r fs) (decode r g) := by
  classical
  constructor
  · intro h A hA
    obtain ⟨f, hf, rfl⟩ := (mem_decodeFamily r fs A).mp hA
    exact fun hh => h f hf ((hasHom_iff r f g).mpr hh)
  · intro h f hf hh
    exact h (decodeFinite r f) ((mem_decodeFamily r fs _).mpr ⟨f, hf, rfl⟩)
      ((hasHom_iff r f g).mp hh)

theorem familyHomFreeCode_primrec :
    PrimrecRel (fun p : ℕ × FamilyCode => FamilyHomFreeCode p.1 p.2) :=
  forall_mem_primrec (Primrec.snd.comp Primrec.fst)
    (hasHom_primrec.not.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))))

/-- All labelled graphs of order `m` passing the finite-map test. -/
def homFreeCodes (r : ℕ) (fs : FamilyCode) (m : ℕ) : List Code :=
  (Uniform.graphCodes r m).filter (FamilyHomFreeCode r fs)

theorem homFreeCodes_primrec :
    Primrec₂ (fun p : ℕ × FamilyCode => homFreeCodes p.1 p.2) :=
  (filter_primrec familyHomFreeCode_primrec).comp Primrec.fst
    (Uniform.graphCodes_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

/-- Natural maximum with the empty-list value zero. -/
def listMax (xs : List ℕ) : ℕ := xs.foldr max 0

theorem listMax_primrec : Primrec listMax :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem listMax_le_iff (xs : List ℕ) (n : ℕ) :
    listMax xs ≤ n ↔ ∀ x ∈ xs, x ≤ n := by
  induction xs with
  | nil => simp [listMax]
  | cons x xs ih => simpa [listMax] using
      (and_congr Iff.rfl ih : (x ≤ n ∧ listMax xs ≤ n) ↔
        (x ≤ n ∧ ∀ y ∈ xs, y ≤ n))

theorem le_listMax {xs : List ℕ} {n : ℕ} (h : n ∈ xs) :
    n ≤ listMax xs := (listMax_le_iff xs _).mp le_rfl n h

/-- The exact largest edge count; a search without feasible graphs returns zero. -/
def homFreeMaxCode (r : ℕ) (fs : FamilyCode) (m : ℕ) : ℕ :=
  listMax ((homFreeCodes r fs m).map (edgeCount r))

theorem homFreeMaxCode_primrec :
    Primrec₂ (fun p : ℕ × FamilyCode => homFreeMaxCode p.1 p.2) :=
  listMax_primrec.comp (Primrec.list_map homFreeCodes_primrec
    (edgeCount_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂)

theorem homFreeMaxCode_correct (r : ℕ) (fs : FamilyCode) (m : ℕ) :
    homFreeMaxCode r fs m = homFreeMax (decodeFamily r fs) m := by
  apply Nat.le_antisymm
  · apply (listMax_le_iff _ _).mpr
    intro n hn
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hgc, hfree⟩ := List.mem_filter.mp hg
    have hsize := ((Uniform.mem_graphCodes r m g).mp hgc).1
    have hfree' := (familyHomFreeCode_correct r fs g).mp (of_decide_eq_true hfree)
    rcases g with ⟨k, rows⟩
    dsimp only at hsize
    subst k
    rw [edgeCount_eq_card]
    exact edge_card_le_homFreeMax (decodeFamily r fs) (decode r (m, rows)) hfree'
  · apply (homFreeMax_le_iff _ _ _).mpr
    intro G hG
    have hf : FamilyHomFreeCode r fs (encode G) :=
      (familyHomFreeCode_correct r fs (encode G)).mpr (by simpa only [decode_encode] using hG)
    have he : encode G ∈ homFreeCodes r fs m :=
      List.mem_filter.mpr ⟨Uniform.encode_mem_graphCodes (⟨m, G⟩ : FiniteGraph r),
        decide_eq_true hf⟩
    have hle : edgeCount r (encode G) ≤ homFreeMaxCode r fs m :=
      le_listMax (List.mem_map.mpr ⟨encode G, he, rfl⟩)
    simpa only [edgeCount_eq_card, decode_encode] using hle

theorem hasEdgeless_correct (r : ℕ) (fs : FamilyCode) :
    HasEdgeless r fs ↔ ∃ A ∈ decodeFamily r fs, A.2.edges = ∅ := by
  classical
  constructor
  · rintro ⟨g, hg, he⟩
    exact ⟨decodeFinite r g, (mem_decodeFamily r fs _).mpr ⟨g, hg, rfl⟩,
      Finset.card_eq_zero.mp ((edgeCount_eq_card r g).symm.trans he)⟩
  · rintro ⟨A, hA, he⟩
    obtain ⟨g, hg, rfl⟩ := (mem_decodeFamily r fs A).mp hA
    exact ⟨g, hg, (edgeCount_eq_card r g).trans (Finset.card_eq_zero.mpr he)⟩

theorem edges_nonempty_of_not_hasEdgeless (r : ℕ) (fs : FamilyCode)
    (h : ¬ HasEdgeless r fs) :
    ∀ A ∈ decodeFamily r fs, A.2.edges.Nonempty := by
  intro A hA
  exact Finset.nonempty_iff_ne_empty.mpr (fun he =>
    h ((hasEdgeless_correct r fs).mpr ⟨A, hA, he⟩))

end TuranUniversality.Effective.FiniteApproximation
