module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic

@[expose] public section

/-! # Binary words, prefixWord paths, and reverse complementation -/

namespace TuranUniversality.Structural.Cube

open scoped symmDiff

abbrev Word (b : ℕ) := Finset (Fin b)

@[simp] theorem empty_symmDiff {b : ℕ} (w : Word b) : (∅ : Word b) ∆ w = w := by
  ext i
  simp [Finset.mem_symmDiff]

@[simp] theorem symmDiff_empty {b : ℕ} (w : Word b) : w ∆ (∅ : Word b) = w := by
  rw [symmDiff_comm, empty_symmDiff]

def prefixWord (b k : ℕ) : Word b := Finset.univ.filter fun i => i.val < k

@[simp] theorem mem_prefix (b k : ℕ) (i : Fin b) : i ∈ prefixWord b k ↔ i.val < k := by
  simp [prefixWord]

@[simp] theorem prefix_zero (b : ℕ) : prefixWord b 0 = ∅ := by
  ext i
  simp

@[simp] theorem prefix_full (b : ℕ) : prefixWord b b = Finset.univ := by
  ext i
  simp

theorem prefix_card (b k : ℕ) (hk : k ≤ b) : (prefixWord b k).card = k := by
  by_cases h : k < b
  · have he : prefixWord b k = Finset.Iio (⟨k, h⟩ : Fin b) := by
      ext i
      simp only [mem_prefix, Finset.mem_Iio, Fin.lt_def]
    rw [he, Fin.card_Iio]
  · have he : k = b := by omega
    subst k
    simp

theorem prefix_mono (b : ℕ) {k l : ℕ} (h : k ≤ l) : prefixWord b k ⊆ prefixWord b l := by
  intro i hi
  exact (mem_prefix b l i).mpr (lt_of_lt_of_le ((mem_prefix b k i).mp hi) h)

def prefixPath (b : ℕ) : Finset (Word b) :=
  Finset.univ.image fun k : Fin (b + 1) => prefixWord b k.val

@[simp] theorem mem_prefixPath (b : ℕ) (w : Word b) :
    w ∈ prefixPath b ↔ ∃ k ≤ b, prefixWord b k = w := by
  constructor
  · intro h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨k.val, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨k, by omega⟩, Finset.mem_univ _, rfl⟩

theorem prefix_mem_prefixPath (b k : ℕ) (hk : k ≤ b) : prefixWord b k ∈ prefixPath b :=
  (mem_prefixPath b _).mpr ⟨k, hk, rfl⟩

def distance {b : ℕ} (u v : Word b) : ℕ := (u ∆ v).card

@[simp] theorem distance_self {b : ℕ} (w : Word b) : distance w w = 0 := by
  simp [distance]

theorem distance_comm {b : ℕ} (u v : Word b) : distance u v = distance v u := by
  simp only [distance, symmDiff_comm]

theorem distance_prefix_le (b k l : ℕ) (hkl : k ≤ l) (hl : l ≤ b) :
    distance (prefixWord b k) (prefixWord b l) = l - k := by
  have hsub := prefix_mono b hkl
  rw [distance, Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr hsub,
    Finset.empty_union, Finset.card_sdiff_of_subset hsub,
    prefix_card b l hl, prefix_card b k (hkl.trans hl)]

theorem distance_prefix (b k l : ℕ) (hk : k ≤ b) (hl : l ≤ b) :
    distance (prefixWord b k) (prefixWord b l) = (l - k) + (k - l) := by
  rcases le_total k l with h | h
  · rw [distance_prefix_le b k l h hl]
    omega
  · rw [distance_comm, distance_prefix_le b l k h hk]
    omega

theorem prefix_has_neighbor (b : ℕ) (hb : 0 < b) (w : Word b)
    (hw : w ∈ prefixPath b) : ∃ v ∈ prefixPath b, distance w v = 1 := by
  obtain ⟨k, hk, rfl⟩ := (mem_prefixPath b w).mp hw
  by_cases h : k < b
  · refine ⟨prefixWord b (k + 1), prefix_mem_prefixPath b (k + 1) (by omega), ?_⟩
    rw [distance_prefix_le b k (k + 1) (by omega) (by omega)]
    omega
  · refine ⟨prefixWord b (k - 1), prefix_mem_prefixPath b (k - 1) (by omega), ?_⟩
    rw [distance_comm, distance_prefix_le b (k - 1) k (by omega) hk]
    omega

/-- A coordinate permutation followed by a fixed set of bit flips. -/
def wordAction {b : ℕ} (π : Equiv.Perm (Fin b)) (flips w : Word b) : Word b :=
  flips ∆ w.map π.toEmbedding

theorem wordAction_distance {b : ℕ} (π : Equiv.Perm (Fin b)) (flips u v : Word b) :
    distance (wordAction π flips u) (wordAction π flips v) = distance u v := by
  have he : wordAction π flips u ∆ wordAction π flips v = (u ∆ v).map π.toEmbedding := by
    ext i
    simp only [wordAction, Finset.mem_symmDiff, Finset.mem_map_equiv]
    tauto
  rw [distance, he, Finset.card_map]
  rfl

theorem wordAction_injective {b : ℕ} (π : Equiv.Perm (Fin b)) (flips : Word b) :
    Function.Injective (wordAction π flips) := by
  intro u v huv
  have h := wordAction_distance π flips u v
  rw [huv, distance_self] at h
  exact Finset.symmDiff_eq_empty.mp (Finset.card_eq_zero.mp h.symm)

/-- Reverse the coordinate order and complement every bit. -/
def reverseComplement {b : ℕ} (w : Word b) : Word b :=
  Finset.univ \ w.map Fin.revPerm.toEmbedding

@[simp] theorem mem_reverseComplement {b : ℕ} (w : Word b) (i : Fin b) :
    i ∈ reverseComplement w ↔ Fin.rev i ∉ w := by
  simp [reverseComplement, Finset.mem_map_equiv, Fin.revPerm_symm]

@[simp] theorem reverseComplement_reverseComplement {b : ℕ} (w : Word b) :
    reverseComplement (reverseComplement w) = w := by
  ext i
  simp

theorem reverseComplement_eq_action {b : ℕ} (w : Word b) :
    reverseComplement w = wordAction Fin.revPerm Finset.univ w := by
  ext i
  simp [wordAction, Finset.mem_symmDiff, Finset.mem_map_equiv, Fin.revPerm_symm]

theorem reverseComplement_distance {b : ℕ} (u v : Word b) :
    distance (reverseComplement u) (reverseComplement v) = distance u v := by
  rw [reverseComplement_eq_action, reverseComplement_eq_action, wordAction_distance]

theorem reverseComplement_prefix (b k : ℕ) (hk : k ≤ b) :
    reverseComplement (prefixWord b k) = prefixWord b (b - k) := by
  ext i
  simp only [mem_reverseComplement, mem_prefix, Fin.val_rev]
  have hi := i.isLt
  omega

theorem reverseComplement_mem_prefixPath {b : ℕ} {w : Word b}
    (hw : w ∈ prefixPath b) : reverseComplement w ∈ prefixPath b := by
  obtain ⟨k, hk, rfl⟩ := (mem_prefixPath b w).mp hw
  rw [reverseComplement_prefix b k hk]
  exact prefix_mem_prefixPath b (b - k) (by omega)

/-- Extra neutral words are isolated in the unit-distance graph of the pool. -/
def IsolatedExtras (b : ℕ) (extra : Finset (Word b)) : Prop :=
  ∀ w ∈ extra, ∀ v ∈ prefixPath b ∪ extra, distance w v ≠ 1

end TuranUniversality.Structural.Cube
