module

public import TuranUniversality.Effective.UniformEncoding
public import TuranUniversality.Effective.RuleEncoding
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! # Finite row predicates, with their exact set semantics -/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

def Distinct (w : List ℕ) : Prop :=
  ∀ i < w.length, ∀ j < w.length, w.getD i 0 = w.getD j 0 → i = j

instance (w : List ℕ) : Decidable (Distinct w) := by
  unfold Distinct
  infer_instance

theorem distinct_iff (w : List ℕ) : Distinct w ↔ w.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  constructor
  · intro h i j hij
    apply Fin.ext
    apply h i.val i.isLt j.val j.isLt
    simpa only [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ j.isLt] using hij
  · intro h i hi j hj hij
    have he : w[i] = w[j] := by
      simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hij
    exact congrArg Fin.val (@h ⟨i, hi⟩ ⟨j, hj⟩ he)

def SameSet (a b : List ℕ) : Prop :=
  (∀ x ∈ a, x ∈ b) ∧ (∀ x ∈ b, x ∈ a)

instance (a b : List ℕ) : Decidable (SameSet a b) := by
  unfold SameSet
  infer_instance

theorem sameSet_iff (a b : List ℕ) : SameSet a b ↔ a.toFinset = b.toFinset := by
  constructor
  · rintro ⟨hab, hba⟩
    ext x
    simpa using ⟨hab x, hba x⟩
  · intro h
    constructor <;> intro x hx
    · exact List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr hx)
    · exact List.mem_toFinset.mp (h.symm ▸ List.mem_toFinset.mpr hx)

def Good (r n : ℕ) (w : List ℕ) : Prop :=
  w.length = r ∧ Distinct w ∧ ∀ x ∈ w, x < n

instance (r n : ℕ) (w : List ℕ) : Decidable (Good r n w) := by
  unfold Good
  infer_instance

def Edge (r : ℕ) (g : Code) (w : List ℕ) : Prop :=
  Good r g.1 w ∧ ∃ t ∈ g.2, t.length = r ∧ SameSet w t

instance (r : ℕ) (g : Code) (w : List ℕ) : Decidable (Edge r g w) := by
  unfold Edge
  infer_instance

theorem list_map_toFinset {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (w : List A) : (w.map f).toFinset = w.toFinset.image f := by
  ext b
  simp

theorem list_nodup_of_card {A : Type*} [DecidableEq A] (w : List A)
    (h : w.toFinset.card = w.length) : w.Nodup :=
  (Multiset.toFinset_card_eq_card_iff_nodup (m := (w : Multiset A))).mp h

theorem edge_iff_of_image (r : ℕ) (g : Code) (e : Finset (Fin g.1)) (w : List ℕ)
    (hlen : w.length = r) (him : e.image Fin.val = w.toFinset) :
    Edge r g w ↔ e ∈ (decode r g).edges := by
  rw [mem_decode]
  constructor
  · rintro ⟨⟨_, hd, _⟩, t, ht, htlen, hsame⟩
    have hc := List.toFinset_card_of_nodup ((distinct_iff w).mp hd)
    have hecard : e.card = r := by
      rw [← Finset.card_image_of_injective e Fin.val_injective, him, hc, hlen]
    exact ⟨hecard, t, ht, htlen, him.trans ((sameSet_iff w t).mp hsame)⟩
  · rintro ⟨hecard, t, ht, htlen, het⟩
    refine ⟨⟨hlen, (distinct_iff w).mpr (list_nodup_of_card w ?_), ?_⟩,
      t, ht, htlen, (sameSet_iff w t).mpr (him.symm.trans het)⟩
    · rw [← him, Finset.card_image_of_injective _ Fin.val_injective, hecard, hlen]
    · intro a ha
      have ha' : a ∈ e.image Fin.val := him.symm ▸ List.mem_toFinset.mpr ha
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha'
      exact v.isLt

def rowSet (n : ℕ) (w : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val ∈ w

@[simp] theorem mem_rowSet (n : ℕ) (w : List ℕ) (i : Fin n) :
    i ∈ rowSet n w ↔ i.val ∈ w := by simp [rowSet]

theorem rowSet_image (n : ℕ) (w : List ℕ) (h : ∀ a ∈ w, a < n) :
    (rowSet n w).image Fin.val = w.toFinset := by
  ext a
  simp only [Finset.mem_image, mem_rowSet, List.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro ha
    exact ⟨⟨a, h a ha⟩, ha, rfl⟩

theorem edge_rowSet (r : ℕ) (g : Code) (w : List ℕ) (h : Edge r g w) :
    rowSet g.1 w ∈ (decode r g).edges :=
  (edge_iff_of_image r g _ w h.1.1 (rowSet_image g.1 w h.1.2.2)).mp h

theorem edge_canonical (r : ℕ) (g : Code) (e : Finset (Fin g.1))
    (h : e ∈ (decode r g).edges) : Edge r g (e.toList.map Fin.val) := by
  apply (edge_iff_of_image r g e _ _ _).mpr h
  · simp [(decode r g).uniform e h]
  · rw [list_map_toFinset]
    simp

end TuranUniversality.Effective.Uniform
