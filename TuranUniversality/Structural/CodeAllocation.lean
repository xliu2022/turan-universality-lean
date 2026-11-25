module

public import TuranUniversality.Structural.CodeWords

@[expose] public section

/-! # Successive disjoint intervals of the fixed-word enumeration -/

open scoped BigOperators

namespace TuranUniversality.Structural.CodePools

open Cube
variable {I : Type*} [Fintype I] [LinearOrder I]

def offset (d : I → ℕ) (i : I) : ℕ := ∑ j ∈ Finset.univ.filter (fun j => j < i), d j

theorem offset_add (d : I → ℕ) (i : I) :
    offset d i + d i = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), d j := by
  have heq : Finset.univ.filter (fun j => j ≤ i) =
      insert i (Finset.univ.filter (fun j => j < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    exact le_iff_eq_or_lt
  rw [heq, Finset.sum_insert (by simp)]
  exact Nat.add_comm _ _

theorem offset_add_le_total (d : I → ℕ) (i : I) : offset d i + d i ≤ ∑ j, d j := by
  rw [offset_add]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem offset_end_le_of_lt (d : I → ℕ) {i j : I} (h : i < j) :
    offset d i + d i ≤ offset d j := by
  rw [offset_add, offset]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  have hki := (Finset.mem_filter.mp hk).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki.trans_lt h⟩

def segmentIndex (d : I → ℕ) (capacity : ℕ) (hcap : (∑ i, d i) ≤ capacity) (i : I) :
    Fin (d i) ↪ Fin capacity where
  toFun j := ⟨offset d i + j.val, (Nat.add_lt_add_left j.isLt _).trans_le
    ((offset_add_le_total d i).trans hcap)⟩
  inj' := by intro j k h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

noncomputable def allocatedWords (k : ℕ) (d : I → ℕ) (hcap : (∑ i, d i) ≤ 2 ^ k)
    (i : I) : Finset (Word (2 + 2 * k)) :=
  Finset.univ.map ((segmentIndex d (2 ^ k) hcap i).trans (fixedWordEnumeration k))

theorem allocatedWords_card (k : ℕ) (d : I → ℕ) (hcap : (∑ i, d i) ≤ 2 ^ k) (i : I) :
    (allocatedWords k d hcap i).card = d i := by simp [allocatedWords]

theorem allocatedWords_subset (k : ℕ) (d : I → ℕ) (hcap : (∑ i, d i) ≤ 2 ^ k) (i : I) :
    allocatedWords k d hcap i ⊆ fixedStartWords k := by
  intro w hw
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hw
  exact fixedWordEnumeration_mem k _

theorem allocatedWords_disjoint (k : ℕ) (d : I → ℕ) (hcap : (∑ i, d i) ≤ 2 ^ k)
    {i j : I} (hij : i ≠ j) :
    Disjoint (allocatedWords k d hcap i) (allocatedWords k d hcap j) := by
  apply Finset.disjoint_left.mpr
  intro w hwi hwj
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hwi
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hwj
  have heq := (fixedWordEnumeration k).injective (ha.trans hb.symm)
  have hv := congrArg Fin.val heq
  change offset d i + a.val = offset d j + b.val at hv
  rcases lt_or_gt_of_ne hij with h | h
  · have hs := offset_end_le_of_lt d h
    have ha := a.isLt
    omega
  · have hs := offset_end_le_of_lt d h
    have hb := b.isLt
    omega

theorem allocatedWords_disjoint_prefixPath (k : ℕ) (d : I → ℕ)
    (hcap : (∑ i, d i) ≤ 2 ^ k) (i : I) :
    Disjoint (allocatedWords k d hcap i) (prefixPath (2 + 2 * k)) :=
  Finset.disjoint_left.mpr (fun _ hw hp =>
    (Finset.disjoint_left.mp (fixedStartWords_disjoint_prefixPath k))
      (allocatedWords_subset k d hcap i hw) hp)

end TuranUniversality.Structural.CodePools
