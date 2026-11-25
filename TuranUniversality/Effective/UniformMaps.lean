module

public import TuranUniversality.Effective.UniformRows
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # Actual bounded searches for homomorphisms and embeddings -/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

def imageRow (xs w : List ℕ) : List ℕ := w.map fun a => xs.getD a 0

def assignments (g h : Code) : List (List ℕ) := allWords (List.range h.1) g.1

def InjectiveAssignment (n : ℕ) (xs : List ℕ) : Prop :=
  ∀ a < n, ∀ b < n, xs.getD a 0 = xs.getD b 0 → a = b

instance (n : ℕ) (xs : List ℕ) : Decidable (InjectiveAssignment n xs) := by
  unfold InjectiveAssignment
  infer_instance

def HomAssignment (r : ℕ) (g h : Code) (xs : List ℕ) : Prop :=
  ∀ w ∈ allRows r g.1, Edge r g w → Edge r h (imageRow xs w)

instance (r : ℕ) (g h : Code) (xs : List ℕ) : Decidable (HomAssignment r g h xs) := by
  unfold HomAssignment
  infer_instance

def HasHom (r : ℕ) (g h : Code) : Prop :=
  ∃ xs ∈ assignments g h, HomAssignment r g h xs

instance (r : ℕ) (g h : Code) : Decidable (HasHom r g h) := by
  unfold HasHom
  infer_instance

def Contains (r : ℕ) (g h : Code) : Prop :=
  ∃ xs ∈ assignments g h, InjectiveAssignment g.1 xs ∧ HomAssignment r g h xs

instance (r : ℕ) (g h : Code) : Decidable (Contains r g h) := by
  unfold Contains
  infer_instance

def assignmentMap (g h : Code) (xs : List ℕ) (hx : xs ∈ assignments g h) :
    Fin g.1 → Fin h.1 := fun i =>
  ⟨xs.getD i.val 0, by
    obtain ⟨hlen, hbound⟩ := (mem_allWords (List.range h.1) g.1 xs).mp hx
    have hi : i.val < xs.length := by simpa only [hlen] using i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_range.mp (hbound _ (List.getElem_mem hi))⟩

theorem assignmentMap_image (g h : Code) (xs : List ℕ) (hx : xs ∈ assignments g h)
    (e : Finset (Fin g.1)) (w : List ℕ) (he : e.image Fin.val = w.toFinset) :
    (e.image (assignmentMap g h xs hx)).image Fin.val = (imageRow xs w).toFinset := by
  rw [imageRow, list_map_toFinset, ← he, Finset.image_image, Finset.image_image]
  rfl

theorem homAssignment_iff (r : ℕ) (g h : Code) (xs : List ℕ)
    (hx : xs ∈ assignments g h) :
    HomAssignment r g h xs ↔ (decode r g).IsHom (decode r h) (assignmentMap g h xs hx) := by
  constructor
  · intro hhom e he
    let w := e.toList.map Fin.val
    have hw : Edge r g w := edge_canonical r g e he
    have hrows : w ∈ allRows r g.1 := (mem_allRows r g.1 w).mpr ⟨hw.1.1, hw.1.2.2⟩
    have him : e.image Fin.val = w.toFinset := by
      rw [list_map_toFinset]
      simp
    exact (edge_iff_of_image r h _ _ (by simp [imageRow, hw.1.1])
      (assignmentMap_image g h xs hx e w him)).mp (hhom w hrows hw)
  · intro hhom w hw he
    let e := rowSet g.1 w
    have he' : e ∈ (decode r g).edges := edge_rowSet r g w he
    apply (edge_iff_of_image r h (e.image (assignmentMap g h xs hx)) _ _ _).mpr
      (hhom e he')
    · simp [imageRow, he.1.1]
    · exact assignmentMap_image g h xs hx e w (rowSet_image g.1 w he.1.2.2)

theorem injectiveAssignment_iff (g h : Code) (xs : List ℕ)
    (hx : xs ∈ assignments g h) :
    InjectiveAssignment g.1 xs ↔ Function.Injective (assignmentMap g h xs hx) := by
  constructor
  · intro hi a b hab
    exact Fin.ext (hi a.val a.isLt b.val b.isLt (congrArg Fin.val hab))
  · intro hi a ha b hb heq
    exact congrArg Fin.val (hi (show assignmentMap g h xs hx ⟨a, ha⟩ =
      assignmentMap g h xs hx ⟨b, hb⟩ from Fin.ext heq))

theorem map_assignment (g h : Code) (f : Fin g.1 → Fin h.1) :
    ∃ xs, ∃ hx : xs ∈ assignments g h, assignmentMap g h xs hx = f := by
  let xs := List.ofFn fun i : Fin g.1 => (f i).val
  have hxs : xs ∈ assignments g h := by
    apply (mem_allWords _ _ _).mpr
    refine ⟨by simp [xs], ?_⟩
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact List.mem_range.mpr (f i).isLt
  refine ⟨xs, hxs, ?_⟩
  funext i
  apply Fin.ext
  simp [assignmentMap, xs, List.getD_eq_getElem?_getD]

theorem hasHom_iff (r : ℕ) (g h : Code) :
    HasHom r g h ↔ ∃ f, (decode r g).IsHom (decode r h) f := by
  constructor
  · rintro ⟨xs, hx, hh⟩
    exact ⟨assignmentMap g h xs hx, (homAssignment_iff r g h xs hx).mp hh⟩
  · rintro ⟨f, hf⟩
    obtain ⟨xs, hx, hxs⟩ := map_assignment g h f
    exact ⟨xs, hx, (homAssignment_iff r g h xs hx).mpr (hxs ▸ hf)⟩

theorem contains_iff (r : ℕ) (g h : Code) :
    Contains r g h ↔ ∃ f, (decode r g).IsEmbedding (decode r h) f := by
  constructor
  · rintro ⟨xs, hx, hi, hh⟩
    exact ⟨assignmentMap g h xs hx, (injectiveAssignment_iff g h xs hx).mp hi,
      (homAssignment_iff r g h xs hx).mp hh⟩
  · rintro ⟨f, hf⟩
    obtain ⟨xs, hx, hxs⟩ := map_assignment g h f
    exact ⟨xs, hx, (injectiveAssignment_iff g h xs hx).mpr (hxs ▸ hf.1),
      (homAssignment_iff r g h xs hx).mpr (hxs ▸ hf.2)⟩

end TuranUniversality.Effective.Uniform
