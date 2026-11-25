module

public import TuranUniversality.Structural.CubeBasic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # The reverse-complement fixed binary words used by the code pools

There are exactly `2^k` fixed words of length `2+2*k` with first bit zero.
They are constructed by choosing the `k` free bits in the left half and
reflecting the complementary left half into the right half. Their Hamming
weight and isolation from the prefix path are proved explicitly.
-/

namespace TuranUniversality.Structural.Cube

open scoped symmDiff

def payloadIndex (k : ℕ) : Fin k ↪ Fin (2 + 2 * k) where
  toFun j := ⟨j.val + 1, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def firstIndex (k : ℕ) : Fin (2 + 2 * k) := ⟨0, by omega⟩

def lastIndex (k : ℕ) : Fin (2 + 2 * k) := (firstIndex k).rev

def mirrorWord (k : ℕ) (s : Word k) : Word (2 + 2 * k) :=
  s.map (payloadIndex k) ∪
    ((prefixWord (2 + 2 * k) (k + 1) \ s.map (payloadIndex k)).map Fin.revPerm.toEmbedding)

theorem payloadIndex_lt_half (k : ℕ) (s : Word k) {i : Fin (2 + 2 * k)}
    (hi : i ∈ s.map (payloadIndex k)) : i.val < k + 1 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  dsimp [payloadIndex]
  omega

theorem rev_high_of_low (k : ℕ) {i : Fin (2 + 2 * k)} (hi : i.val < k + 1) :
    ¬ i.rev.val < k + 1 := by rw [Fin.val_rev]; have := i.isLt; omega

theorem rev_low_of_high (k : ℕ) {i : Fin (2 + 2 * k)} (hi : ¬ i.val < k + 1) :
    i.rev.val < k + 1 := by rw [Fin.val_rev]; have := i.isLt; omega

theorem mem_mirrorWord_low (k : ℕ) (s : Word k) (i : Fin (2 + 2 * k))
    (hi : i.val < k + 1) : i ∈ mirrorWord k s ↔ i ∈ s.map (payloadIndex k) := by
  have hrev := rev_high_of_low k hi
  simp only [mirrorWord, Finset.mem_union, Finset.mem_map_equiv, Fin.revPerm_symm,
    Fin.revPerm_apply, Finset.mem_sdiff, mem_prefix]
  tauto

theorem mem_mirrorWord_high (k : ℕ) (s : Word k) (i : Fin (2 + 2 * k))
    (hi : ¬ i.val < k + 1) : i ∈ mirrorWord k s ↔ i.rev ∉ s.map (payloadIndex k) := by
  have hrev := rev_low_of_high k hi
  have hnot : i ∉ s.map (payloadIndex k) := fun h => hi (payloadIndex_lt_half k s h)
  simp only [mirrorWord, Finset.mem_union, Finset.mem_map_equiv, Fin.revPerm_symm,
    Fin.revPerm_apply, Finset.mem_sdiff, mem_prefix, hnot, false_or, hrev, true_and]

theorem reverseComplement_mirrorWord (k : ℕ) (s : Word k) :
    reverseComplement (mirrorWord k s) = mirrorWord k s := by
  ext i
  rw [mem_reverseComplement]
  by_cases hi : i.val < k + 1
  · rw [mem_mirrorWord_high k s i.rev (rev_high_of_low k hi),
      mem_mirrorWord_low k s i hi, Fin.rev_rev]
    simp
  · rw [mem_mirrorWord_low k s i.rev (rev_low_of_high k hi),
      mem_mirrorWord_high k s i hi]

theorem first_notMem_mirrorWord (k : ℕ) (s : Word k) : firstIndex k ∉ mirrorWord k s := by
  rw [mem_mirrorWord_low k s _ (by simp [firstIndex])]
  rintro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  have := congrArg Fin.val hj
  simp [payloadIndex, firstIndex] at this

theorem payload_mem_mirrorWord (k : ℕ) (s : Word k) (j : Fin k) :
    payloadIndex k j ∈ mirrorWord k s ↔ j ∈ s := by
  rw [mem_mirrorWord_low k s _ (by dsimp [payloadIndex]; omega)]
  exact Finset.mem_map' _

theorem mirrorWord_injective (k : ℕ) : Function.Injective (mirrorWord k) := by
  intro s t h
  ext j
  rw [← payload_mem_mirrorWord k s j, h, payload_mem_mirrorWord]

def fixedStartWords (k : ℕ) : Finset (Word (2 + 2 * k)) :=
  Finset.univ.filter fun w => reverseComplement w = w ∧ firstIndex k ∉ w

@[simp] theorem mem_fixedStartWords (k : ℕ) (w : Word (2 + 2 * k)) :
    w ∈ fixedStartWords k ↔ reverseComplement w = w ∧ firstIndex k ∉ w := by
  simp [fixedStartWords]

theorem mirrorWord_mem_fixedStartWords (k : ℕ) (s : Word k) :
    mirrorWord k s ∈ fixedStartWords k :=
  (mem_fixedStartWords k _).mpr ⟨reverseComplement_mirrorWord k s, first_notMem_mirrorWord k s⟩

theorem fixed_word_determined_by_left (k : ℕ) (u v : Word (2 + 2 * k))
    (hu : reverseComplement u = u) (hv : reverseComplement v = v)
    (hleft : ∀ i : Fin (2 + 2 * k), i.val < k + 1 → (i ∈ u ↔ i ∈ v)) : u = v := by
  ext i
  by_cases hi : i.val < k + 1
  · exact hleft i hi
  · have h := hleft i.rev (rev_low_of_high k hi)
    have hu' : i ∈ u ↔ i.rev ∉ u := by
      have h := mem_reverseComplement u i
      rwa [hu] at h
    have hv' : i ∈ v ↔ i.rev ∉ v := by
      have h := mem_reverseComplement v i
      rwa [hv] at h
    rw [hu', hv']
    exact not_congr h

noncomputable def leftPayload (k : ℕ) (w : Word (2 + 2 * k)) : Word k :=
  w.preimage (payloadIndex k) (payloadIndex k).injective.injOn

theorem leftPayload_injective (k : ℕ) :
    Function.Injective (fun w : fixedStartWords k => leftPayload k w.val) := by
  intro u v huv
  change leftPayload k u.val = leftPayload k v.val at huv
  apply Subtype.ext
  obtain ⟨huR, hu0⟩ := (mem_fixedStartWords k _).mp u.property
  obtain ⟨hvR, hv0⟩ := (mem_fixedStartWords k _).mp v.property
  apply fixed_word_determined_by_left k _ _ huR hvR
  intro i hi
  by_cases hi0 : i.val = 0
  · have heq : i = firstIndex k := Fin.ext hi0
    simp only [heq, hu0, hv0]
  · let j : Fin k := ⟨i.val - 1, by omega⟩
    have heq : payloadIndex k j = i := by apply Fin.ext; dsimp [payloadIndex, j]; omega
    have hmem : j ∈ leftPayload k u.val ↔ j ∈ leftPayload k v.val := by rw [huv]
    simpa only [leftPayload, Finset.mem_preimage, heq] using hmem

theorem fixedStartWords_card (k : ℕ) : (fixedStartWords k).card = 2 ^ k := by
  apply Nat.le_antisymm
  · have h := Fintype.card_le_of_injective _ (leftPayload_injective k)
    simpa only [Fintype.card_coe, Fintype.card_finset, Fintype.card_fin] using h
  · have h := Finset.card_le_card (show Finset.univ.image (mirrorWord k) ⊆ fixedStartWords k by
      intro w hw
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hw
      exact mirrorWord_mem_fixedStartWords k s)
    rw [Finset.card_image_of_injective _ (mirrorWord_injective k)] at h
    simpa only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] using h

theorem fixedStartWords_word_card (k : ℕ) {w : Word (2 + 2 * k)}
    (hw : w ∈ fixedStartWords k) : w.card = k + 1 := by
  have hR := (mem_fixedStartWords k w).mp hw |>.1
  have hcard := congrArg Finset.card hR
  rw [reverseComplement, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, Finset.card_map] at hcard
  have hle : w.card ≤ 2 + 2 * k := by simpa using Finset.card_le_card (Finset.subset_univ w)
  omega

theorem fixedStartWords_last_mem (k : ℕ) {w : Word (2 + 2 * k)}
    (hw : w ∈ fixedStartWords k) : lastIndex k ∈ w := by
  obtain ⟨hR, h0⟩ := (mem_fixedStartWords k w).mp hw
  have hmem : lastIndex k ∈ reverseComplement w := by simp [lastIndex, h0]
  rwa [hR] at hmem

theorem fixedStartWords_disjoint_prefixPath (k : ℕ) :
    Disjoint (fixedStartWords k) (prefixPath (2 + 2 * k)) := by
  apply Finset.disjoint_left.mpr
  intro w hw hp
  obtain ⟨j, hj, rfl⟩ := (mem_prefixPath _ w).mp hp
  have h0 := (mem_fixedStartWords k _).mp hw |>.2
  have hj0 : j = 0 := by
    have : ¬ 0 < j := by simpa [firstIndex] using h0
    omega
  subst j
  have hc := fixedStartWords_word_card k hw
  simp at hc

theorem distance_ne_one_of_equal_card {b : ℕ} (u v : Word b) (hcard : u.card = v.card) :
    distance u v ≠ 1 := by
  have hdiff := Finset.card_sdiff_comm hcard
  have hd : Disjoint (u \ v) (v \ u) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  rw [distance, Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  omega

theorem fixedStartWords_pair_distance (k : ℕ) {u v : Word (2 + 2 * k)}
    (hu : u ∈ fixedStartWords k) (hv : v ∈ fixedStartWords k) : distance u v ≠ 1 :=
  distance_ne_one_of_equal_card u v ((fixedStartWords_word_card k hu).trans
    (fixedStartWords_word_card k hv).symm)

theorem fixedStartWords_prefix_distance (k : ℕ) (hk : 1 ≤ k)
    {w : Word (2 + 2 * k)} (hw : w ∈ fixedStartWords k)
    {v : Word (2 + 2 * k)} (hv : v ∈ prefixPath (2 + 2 * k)) : distance w v ≠ 1 := by
  obtain ⟨j, hj, rfl⟩ := (mem_prefixPath _ v).mp hv
  have hc := fixedStartWords_word_card k hw
  by_cases hj0 : j = 0
  · subst j
    simp [distance, hc]
    omega
  by_cases hjb : j = 2 + 2 * k
  · subst j
    rw [prefix_full, distance, Finset.symmDiff_def]
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ w), Finset.empty_union]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ w), Finset.card_univ,
      Fintype.card_fin, hc]
    omega
  have h0 := (mem_fixedStartWords k w).mp hw |>.2
  have hlast := fixedStartWords_last_mem k hw
  have h0prefix : firstIndex k ∈ prefixWord (2 + 2 * k) j := by
    rw [mem_prefix]
    dsimp [firstIndex]
    omega
  have hlastprefix : lastIndex k ∉ prefixWord (2 + 2 * k) j := by
    rw [mem_prefix]
    simp only [lastIndex, Fin.val_rev, firstIndex]
    omega
  have hne : firstIndex k ≠ lastIndex k := by
    intro h
    have hv := congrArg Fin.val h
    simp only [firstIndex, lastIndex, Fin.val_rev] at hv
    omega
  have hsub : {firstIndex k, lastIndex k} ⊆ w ∆ prefixWord (2 + 2 * k) j := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_symmDiff.mpr (Or.inr ⟨h0prefix, h0⟩)
    · exact Finset.mem_symmDiff.mpr (Or.inl ⟨hlast, hlastprefix⟩)
  have hcard : 2 ≤ distance w (prefixWord (2 + 2 * k) j) := by
    simpa only [Finset.card_pair hne, distance] using Finset.card_le_card hsub
  omega

theorem isolatedExtras_of_subset_fixedStartWords (k : ℕ) (hk : 1 ≤ k)
    (extra : Finset (Word (2 + 2 * k))) (hsub : extra ⊆ fixedStartWords k) :
    IsolatedExtras (2 + 2 * k) extra := by
  intro w hw v hv
  rcases Finset.mem_union.mp hv with hp | he
  · exact fixedStartWords_prefix_distance k hk (hsub hw) hp
  · exact fixedStartWords_pair_distance k (hsub hw) (hsub he)

theorem prefixPath_card (b : ℕ) : (prefixPath b).card = b + 1 := by
  rw [prefixPath, Finset.card_image_of_injective]
  · simp
  · intro i j h
    apply Fin.ext
    have hc := congrArg Finset.card h
    rw [prefix_card b i.val (by omega), prefix_card b j.val (by omega)] at hc
    exact hc

def bitList {b : ℕ} (w : Word b) : List Bool := List.ofFn (fun i : Fin b => decide (i ∈ w))

theorem bitList_injective (b : ℕ) : Function.Injective (@bitList b) := by
  intro u v h
  have hfun := List.ofFn_injective h
  ext i
  have hi := congrFun hfun i
  simpa only [decide_eq_decide] using hi

/-- The lexicographic enumeration used by the paper's successive pools. -/
noncomputable def fixedWordEnumeration (k : ℕ) : Fin (2 ^ k) ↪ Word (2 + 2 * k) := by
  letI : LinearOrder (Word (2 + 2 * k)) := LinearOrder.lift' bitList (bitList_injective _)
  exact ((fixedStartWords k).orderEmbOfFin (fixedStartWords_card k)).toEmbedding

theorem fixedWordEnumeration_mem (k : ℕ) (i : Fin (2 ^ k)) :
    fixedWordEnumeration k i ∈ fixedStartWords k := by
  letI : LinearOrder (Word (2 + 2 * k)) := LinearOrder.lift' bitList (bitList_injective _)
  exact (fixedStartWords k).orderEmbOfFin_mem (fixedStartWords_card k) i

end TuranUniversality.Structural.Cube
