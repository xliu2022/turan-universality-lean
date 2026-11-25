module

public import TuranUniversality.Structural.CubeSymmetry

@[expose] public section

/-! # Product sets of bits inside the neutral pool

If two coordinate boxes cover both bit values in every coordinate, they
cannot both vary in one coordinate while remaining inside the prefix path
plus isolated words. This is the cube obstruction used for triple classes.
-/

namespace TuranUniversality.Structural.Cube

open scoped symmDiff

def InBox {b : ℕ} (D : Fin b → Finset Bool) (w : Word b) : Prop :=
  ∀ i, decide (i ∈ w) ∈ D i

def wordOfBits {b : ℕ} (f : Fin b → Bool) : Word b :=
  Finset.univ.filter fun i => f i = true

@[simp] theorem wordOfBits_bit {b : ℕ} (f : Fin b → Bool) (i : Fin b) :
    decide (i ∈ wordOfBits f) = f i := by
  cases h : f i <;> simp [wordOfBits, h]

theorem exists_inBox_with_bit {b : ℕ} (D : Fin b → Finset Bool)
    (hD : ∀ i, (D i).Nonempty) (j : Fin b) (a : Bool) (ha : a ∈ D j) :
    ∃ w : Word b, InBox D w ∧ decide (j ∈ w) = a := by
  classical
  choose f hf using hD
  let f' := Function.update f j a
  refine ⟨wordOfBits f', ?_, ?_⟩
  · intro i
    rw [wordOfBits_bit]
    by_cases hi : i = j
    · subst i
      simpa [f'] using ha
    · simpa [f', hi] using hf i
  · simp [f']

theorem inBox_erase {b : ℕ} {D : Fin b → Finset Bool} {w : Word b}
    (hw : InBox D w) (i : Fin b) (hi : false ∈ D i) : InBox D (w.erase i) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hi
  · simpa [Finset.mem_erase, hji] using hw j

theorem inBox_insert {b : ℕ} {D : Fin b → Finset Bool} {w : Word b}
    (hw : InBox D w) (i : Fin b) (hi : true ∈ D i) : InBox D (insert i w) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hi
  · simpa [Finset.mem_insert, hji] using hw j

theorem erase_symmDiff_insert {b : ℕ} (w : Word b) (i : Fin b) :
    w.erase i ∆ insert i w = {i} := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  by_cases hji : j = i <;> simp [hji]

/-- A box varying in coordinate i can use only the fixed prefix bit in
every other coordinate if it is contained in the neutral pool. -/
theorem box_other_bit_forced {b : ℕ} {extra : Finset (Word b)}
    (he : IsolatedExtras b extra) (D : Fin b → Finset Bool)
    (hD : ∀ i, (D i).Nonempty)
    (hbox : ∀ w, InBox D w → w ∈ prefixPath b ∪ extra)
    (i : Fin b) (hi : D i = Finset.univ) (j : Fin b) (hji : j ≠ i)
    (a : Bool) (ha : a ∈ D j) : a = decide (j.val < i.val) := by
  obtain ⟨w, hw, hwa⟩ := exists_inBox_with_bit D hD j a ha
  have hufree := inBox_erase hw i (by simp [hi])
  have hvfree := inBox_insert hw i (by simp [hi])
  have hp := parallel_edge he (hbox _ hufree) (hbox _ hvfree) i (erase_symmDiff_insert w i)
  have hueq : w.erase i = prefixWord b i.val := by
    rcases hp with h | h
    · exact h.1
    · have hin : i ∈ w.erase i := by
        rw [h.2]
        simp
      simp at hin
  have hbit : decide (j ∈ w.erase i) = decide (j.val < i.val) := by
    rw [hueq]
    simp
  simpa [Finset.mem_erase, hji, hwa] using hbit

theorem boxes_not_both_full {b : ℕ} (hb : 2 ≤ b) {extra : Finset (Word b)}
    (he : IsolatedExtras b extra) (D : Bool → Fin b → Finset Bool)
    (hD : ∀ a i, (D a i).Nonempty)
    (hcover : ∀ i, D false i ∪ D true i = Finset.univ)
    (hbox : ∀ a w, InBox (D a) w → w ∈ prefixPath b ∪ extra)
    (i : Fin b) : ¬ (D false i = Finset.univ ∧ D true i = Finset.univ) := by
  intro hi
  obtain ⟨j, hji⟩ : ∃ j : Fin b, j ≠ i := by
    by_cases hi0 : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
  have hforced (a : Bool) : a = decide (j.val < i.val) := by
    have hmem : a ∈ D false j ∪ D true j := by rw [hcover]; simp
    rcases Finset.mem_union.mp hmem with h | h
    · exact box_other_bit_forced he (D false) (hD false) (hbox false) i hi.1 j hji a h
    · exact box_other_bit_forced he (D true) (hD true) (hbox true) i hi.2 j hji a h
  have hft : false = true := (hforced false).trans (hforced true).symm
  cases hft

end TuranUniversality.Structural.Cube
