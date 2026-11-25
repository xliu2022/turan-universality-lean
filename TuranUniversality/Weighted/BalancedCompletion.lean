module

public import TuranUniversality.Weighted.CompletionValue

/-! # Balanced completed models from finite permutations -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Index : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Index] [Fintype Index]

theorem assignment_fiber (physical : Code → Kinds) (code : Kinds × Index → Code)
    (hc : ∀ d, physical (code d) = d.1) (k : Kinds) :
    (assignmentPartition physical code).block k = Finset.univ.image (fun i : Index => (k, i)) := by
  ext d
  rcases d with ⟨k', i⟩
  simp only [mem_assignmentPartition, hc, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · intro hk
    exact ⟨i, hk.symm, rfl⟩
  · rintro ⟨j, hj, hji⟩
    exact hj.symm

theorem assignment_fiber_card (physical : Code → Kinds) (code : Kinds × Index → Code)
    (hc : ∀ d, physical (code d) = d.1) (k : Kinds) :
    ((assignmentPartition physical code).block k).card = Fintype.card Index := by
  rw [assignment_fiber physical code hc]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_univ]

def fiberMatching (physical : Code → Kinds) (code : Kinds × Index → Code)
    (hc : ∀ d, physical (code d) = d.1) (s t : Kinds) (σ : Equiv.Perm Index) :
    PartialMatching ((assignmentPartition physical code).block s)
      ((assignmentPartition physical code).block t) where
  pairs := Finset.univ.image fun i => ((s, i), (t, σ i))
  left_mem := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_assignmentPartition physical code s (s, i)).mpr (hc (s, i))
  right_mem := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_assignmentPartition physical code t (t, σ i)).mpr (hc (t, σ i))
  left_injective := by
    intro p hp q hq heq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := congrArg Prod.snd heq
    subst j
    rfl
  right_injective := by
    intro p hp q hq heq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := σ.injective (congrArg Prod.snd heq)
    subst j
    rfl

@[simp] theorem mem_fiberMatching (physical : Code → Kinds) (code : Kinds × Index → Code)
    (hc : ∀ d, physical (code d) = d.1) (s t : Kinds) (σ : Equiv.Perm Index) (a b : Kinds × Index) :
    (a, b) ∈ (fiberMatching physical code hc s t σ).pairs ↔
      a.1 = s ∧ b.1 = t ∧ b.2 = σ a.2 := by
  rcases a with ⟨ka, ia⟩
  rcases b with ⟨kb, ib⟩
  simp only [fiberMatching, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨i, ⟨hs, hi⟩, ht, he⟩
    exact ⟨hs.symm, ht.symm, by simpa only [hi] using he.symm⟩
  · rintro ⟨hs, ht, he⟩
    exact ⟨ia, ⟨hs.symm, rfl⟩, ht.symm, he.symm⟩

theorem fiberMatching_full (physical : Code → Kinds) (code : Kinds × Index → Code)
    (hc : ∀ d, physical (code d) = d.1) (s t : Kinds) (σ : Equiv.Perm Index) :
    (fiberMatching physical code hc s t σ).Full := by
  constructor
  · ext a
    rw [mem_assignmentPartition]
    constructor
    · intro ha
      obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp ha
      have hmem := (mem_fiberMatching physical code hc s t σ p.1 p.2).mp hp
      simpa only [← hpa, hc] using hmem.1
    · intro ha
      apply Finset.mem_image.mpr
      refine ⟨(a, (t, σ a.2)), ?_, rfl⟩
      apply (mem_fiberMatching physical code hc s t σ a (t, σ a.2)).mpr
      exact ⟨(hc a).symm.trans ha, rfl, rfl⟩
  · ext b
    rw [mem_assignmentPartition]
    constructor
    · intro hb
      obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp hb
      have hmem := (mem_fiberMatching physical code hc s t σ p.1 p.2).mp hp
      simpa only [← hpb, hc] using hmem.2.1
    · intro hb
      apply Finset.mem_image.mpr
      refine ⟨((s, σ.symm b.2), b), ?_, rfl⟩
      apply (mem_fiberMatching physical code hc s t σ (s, σ.symm b.2) b).mpr
      exact ⟨rfl, (hc b).symm.trans hb, (σ.apply_symm_apply b.2).symm⟩

def balancedCompletion (S : CompilerSignature Roots Code Kinds L)
    (code : Kinds × Index → Code) (hc : ∀ d, S.physical (code d) = d.1)
    (σ : Fin 3 → Equiv.Perm Index) (markers : Finset (Finset (Kinds × Index)))
    (hmarkers : ∀ p ∈ markers, p.card = 3) (hone : markers.card ≤ 1)
    (hcell : ∀ p ∈ markers, ∀ d ∈ p, d.1 = S.cellKind) : Completion S (Kinds × Index) where
  code := code
  matching e := fiberMatching S.physical code hc (S.sourceKind e) (S.targetKind e) (σ e)
  markers := markers
  marker_uniform := hmarkers
  one_marker := hone
  marker_type := by
    intro p hp d hd
    exact (hc d).trans (hcell p hp d hd)

theorem balancedCompletion_card (S : CompilerSignature Roots Code Kinds L)
    (code : Kinds × Index → Code) (hc : ∀ d, S.physical (code d) = d.1)
    (σ : Fin 3 → Equiv.Perm Index) (markers : Finset (Finset (Kinds × Index)))
    (hmarkers : ∀ p ∈ markers, p.card = 3) (hone : markers.card ≤ 1)
    (hcell : ∀ p ∈ markers, ∀ d ∈ p, d.1 = S.cellKind) (k : Kinds) :
    ((balancedCompletion S code hc σ markers hmarkers hone hcell).partition.block k).card =
      Fintype.card Index := assignment_fiber_card S.physical code hc k

theorem balancedCompletion_full (S : CompilerSignature Roots Code Kinds L)
    (code : Kinds × Index → Code) (hc : ∀ d, S.physical (code d) = d.1)
    (σ : Fin 3 → Equiv.Perm Index) (markers : Finset (Finset (Kinds × Index)))
    (hmarkers : ∀ p ∈ markers, p.card = 3) (hone : markers.card ≤ 1)
    (hcell : ∀ p ∈ markers, ∀ d ∈ p, d.1 = S.cellKind) (e : Fin 3) :
    ((balancedCompletion S code hc σ markers hmarkers hone hcell).matching e).Full :=
  fiberMatching_full S.physical code hc _ _ _

end TuranUniversality.Weighted
