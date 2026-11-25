module

public import TuranUniversality.Structural.CubeBasic

@[expose] public section

/-! # Rigidity of the neutral binary pool

An isolated extension of the prefixWord path has at most one cube edge in each
coordinate direction. Its stabilizer among coordinate permutations and bit
flips consists precisely of the identity and reverse complementation when
the extra words are fixed by reverse complementation.
-/

namespace TuranUniversality.Structural.Cube

open scoped symmDiff

theorem adjacent_mem_prefixPath {b : ℕ} {extra : Finset (Word b)}
    (he : IsolatedExtras b extra) {u v : Word b}
    (hu : u ∈ prefixPath b ∪ extra) (hv : v ∈ prefixPath b ∪ extra)
    (hd : distance u v = 1) : u ∈ prefixPath b ∧ v ∈ prefixPath b := by
  constructor
  · rcases Finset.mem_union.mp hu with h | h
    · exact h
    · exact False.elim (he u h v hv hd)
  · rcases Finset.mem_union.mp hv with h | h
    · exact h
    · exact False.elim (he v h u hu (by rw [distance_comm]; exact hd))

theorem action_preserves_prefixPath {b : ℕ} (hb : 0 < b)
    {extra : Finset (Word b)} (he : IsolatedExtras b extra)
    (π : Equiv.Perm (Fin b)) (flips : Word b)
    (ha : ∀ w ∈ prefixPath b ∪ extra, wordAction π flips w ∈ prefixPath b ∪ extra) :
    ∀ w ∈ prefixPath b, wordAction π flips w ∈ prefixPath b := by
  intro w hw
  obtain ⟨v, hv, hd⟩ := prefix_has_neighbor b hb w hw
  exact (adjacent_mem_prefixPath he (ha w (Finset.mem_union_left _ hw))
    (ha v (Finset.mem_union_left _ hv))
    (by rw [wordAction_distance]; exact hd)).1

theorem perm_eq_refl_of_preserves_prefixPath {b : ℕ} (π : Equiv.Perm (Fin b))
    (ha : ∀ w ∈ prefixPath b, wordAction π ∅ w ∈ prefixPath b) :
    π = Equiv.refl (Fin b) := by
  have hfix (k : ℕ) (hk : k ≤ b) : (prefixWord b k).map π.toEmbedding = prefixWord b k := by
    obtain ⟨j, hj, he⟩ := (mem_prefixPath b _).mp
      (ha _ (prefix_mem_prefixPath b k hk))
    have hc := congrArg Finset.card he
    have hjk : j = k := by
      simpa [wordAction, prefix_card b j hj, prefix_card b k hk] using hc
    simpa [wordAction, hjk] using he.symm
  apply Equiv.ext
  intro i
  have hupper : (π i).val < i.val + 1 := by
    apply (mem_prefix b (i.val + 1) (π i)).mp
    rw [← hfix (i.val + 1) (by omega)]
    exact Finset.mem_map.mpr ⟨i, (mem_prefix _ _ _).mpr (by omega), rfl⟩
  have hlower : ¬ (π i).val < i.val := by
    intro hi
    have hm : π i ∈ (prefixWord b i.val).map π.toEmbedding := by
      rw [hfix i.val (by omega)]
      exact (mem_prefix _ _ _).mpr hi
    have hb := Finset.mem_map_equiv.mp hm
    simpa using hb
  apply Fin.ext
  change (π i).val = i.val
  omega

theorem complement_action_reverse {b : ℕ} (π : Equiv.Perm (Fin b)) (w : Word b) :
    wordAction (π.trans Fin.revPerm) ∅ w =
      reverseComplement (wordAction π Finset.univ w) := by
  ext i
  simp only [wordAction, empty_symmDiff, mem_reverseComplement, Finset.mem_symmDiff,
    Finset.mem_univ, true_and, not_true_eq_false, and_false, or_false, not_not,
    Finset.mem_map_equiv]
  rfl

theorem action_stabilizer {b : ℕ} (hb : 0 < b) {extra : Finset (Word b)}
    (he : IsolatedExtras b extra) (π : Equiv.Perm (Fin b)) (flips : Word b)
    (ha : ∀ w ∈ prefixPath b ∪ extra, wordAction π flips w ∈ prefixPath b ∪ extra) :
    (flips = ∅ ∧ π = Equiv.refl (Fin b)) ∨
      (flips = Finset.univ ∧ π = Fin.revPerm) := by
  have hp := action_preserves_prefixPath hb he π flips ha
  obtain ⟨k, hk, hke⟩ := (mem_prefixPath b _).mp
    (hp _ (prefix_mem_prefixPath b 0 (by omega)))
  obtain ⟨l, hl, hle⟩ := (mem_prefixPath b _).mp
    (hp _ (prefix_mem_prefixPath b b (le_refl _)))
  have hd : distance (prefixWord b k) (prefixWord b l) = b := by
    rw [hke, hle, wordAction_distance, distance_prefix_le b 0 b (by omega) (le_refl _)]
    omega
  rw [distance_prefix b k l hk hl] at hd
  have hends : (k = 0 ∧ l = b) ∨ (k = b ∧ l = 0) := by omega
  rcases hends with ⟨hk0, _⟩ | ⟨hkb, _⟩
  · have hf : flips = ∅ := by simpa [wordAction, hk0] using hke.symm
    refine Or.inl ⟨hf, perm_eq_refl_of_preserves_prefixPath π ?_⟩
    simpa only [hf] using hp
  · have hf : flips = Finset.univ := by simpa [wordAction, hkb] using hke.symm
    have hrev : π.trans Fin.revPerm = Equiv.refl (Fin b) := by
      apply perm_eq_refl_of_preserves_prefixPath
      intro w hw
      rw [complement_action_reverse]
      exact reverseComplement_mem_prefixPath (by simpa only [← hf] using hp w hw)
    refine Or.inr ⟨hf, ?_⟩
    apply Equiv.ext
    intro i
    have hi := congrArg (fun e : Equiv.Perm (Fin b) => e i) hrev
    have hh := congrArg Fin.rev hi
    simpa using hh

theorem reverseComplement_preserves_pool {b : ℕ} {extra : Finset (Word b)}
    (he : ∀ w ∈ extra, reverseComplement w = w) {w : Word b}
    (hw : w ∈ prefixPath b ∪ extra) : reverseComplement w ∈ prefixPath b ∪ extra := by
  rcases Finset.mem_union.mp hw with h | h
  · exact Finset.mem_union_left _ (reverseComplement_mem_prefixPath h)
  · rw [he w h]
    exact Finset.mem_union_right _ h

theorem action_stabilizer_iff {b : ℕ} (hb : 0 < b) {extra : Finset (Word b)}
    (hi : IsolatedExtras b extra) (he : ∀ w ∈ extra, reverseComplement w = w)
    (π : Equiv.Perm (Fin b)) (flips : Word b) :
    (∀ w ∈ prefixPath b ∪ extra, wordAction π flips w ∈ prefixPath b ∪ extra) ↔
      (flips = ∅ ∧ π = Equiv.refl (Fin b)) ∨
        (flips = Finset.univ ∧ π = Fin.revPerm) := by
  refine ⟨action_stabilizer hb hi π flips, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) w hw
  · simpa [wordAction] using hw
  · rw [← reverseComplement_eq_action]
    exact reverseComplement_preserves_pool he hw

/-- The only unit cube edge parallel to coordinate i is the i-th edge of
the prefixWord path, in either orientation. -/
theorem parallel_edge {b : ℕ} {extra : Finset (Word b)}
    (he : IsolatedExtras b extra) {u v : Word b}
    (hu : u ∈ prefixPath b ∪ extra) (hv : v ∈ prefixPath b ∪ extra)
    (i : Fin b) (hd : u ∆ v = {i}) :
    (u = prefixWord b i.val ∧ v = prefixWord b (i.val + 1)) ∨
      (v = prefixWord b i.val ∧ u = prefixWord b (i.val + 1)) := by
  have hdist : distance u v = 1 := by simp [distance, hd]
  obtain ⟨hup, hvp⟩ := adjacent_mem_prefixPath he hu hv hdist
  obtain ⟨k, hk, rfl⟩ := (mem_prefixPath b u).mp hup
  obtain ⟨l, hl, rfl⟩ := (mem_prefixPath b v).mp hvp
  have him : i ∈ prefixWord b k ∆ prefixWord b l := by rw [hd]; simp
  simp only [Finset.mem_symmDiff, mem_prefix] at him
  rw [distance_prefix b k l hk hl] at hdist
  rcases him with him | him
  · have hk' : k = i.val + 1 := by omega
    have hl' : l = i.val := by omega
    exact Or.inr ⟨by rw [hl'], by rw [hk']⟩
  · have hk' : k = i.val := by omega
    have hl' : l = i.val + 1 := by omega
    exact Or.inl ⟨by rw [hk'], by rw [hl']⟩

end TuranUniversality.Structural.Cube
