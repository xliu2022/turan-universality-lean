module

public import TuranUniversality.Weighted.GraphGrounded
public import TuranUniversality.Weighted.TypedLink
public import TuranUniversality.Computation.MatchingSystem

/-! # Actual matching defects ground every open component -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

def groundedWeight {D : Type*} (x : D → ℝ) : Option D → ℝ := fun a => a.elim 0 x

@[simp] theorem groundedWeight_none {D : Type*} (x : D → ℝ) : groundedWeight x none = 0 := rfl

@[simp] theorem groundedWeight_some {D : Type*} (x : D → ℝ) (a : D) :
    groundedWeight x (some a) = x a := rfl

namespace PartialMatching

variable {D : Type*} [DecidableEq D] {U V : Finset D}

def presentGroundEdges (P : PartialMatching U V) : Finset (Sym2 (Option D)) :=
  P.pairs.image fun p => s(some p.1, some p.2)

def leftGroundEdges (P : PartialMatching U V) : Finset (Sym2 (Option D)) :=
  (U \ P.leftMatched).image fun a => s(some a, none)

def rightGroundEdges (P : PartialMatching U V) : Finset (Sym2 (Option D)) :=
  (V \ P.rightMatched).image fun a => s(some a, none)

def groundEdges (P : PartialMatching U V) : Finset (Sym2 (Option D)) :=
  (P.presentGroundEdges ∪ P.leftGroundEdges) ∪ P.rightGroundEdges

theorem present_mem_groundEdges (P : PartialMatching U V) {a b : D} (hp : (a, b) ∈ P.pairs) :
    s(some a, some b) ∈ P.groundEdges :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩))

theorem missing_left_mem_groundEdges (P : PartialMatching U V) {a : D}
    (ha : a ∈ U) (hmiss : ¬ ∃ b, (a, b) ∈ P.pairs) : s(some a, none) ∈ P.groundEdges := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_sdiff.mpr ⟨ha, ?_⟩, rfl⟩
  intro hmatched
  obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp hmatched
  exact hmiss ⟨p.2, by simpa only [← hpa] using hp⟩

theorem missing_right_mem_groundEdges (P : PartialMatching U V) {b : D}
    (hb : b ∈ V) (hmiss : ¬ ∃ a, (a, b) ∈ P.pairs) : s(some b, none) ∈ P.groundEdges := by
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨b, Finset.mem_sdiff.mpr ⟨hb, ?_⟩, rfl⟩
  intro hmatched
  obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp hmatched
  exact hmiss ⟨p.1, by simpa only [← hpb] using hp⟩

theorem presentGroundEdges_energy (P : PartialMatching U V) (hUV : Disjoint U V) (x : D → ℝ) :
    (∑ e ∈ P.presentGroundEdges, pairEnergy (groundedWeight x) e) =
      ∑ p ∈ P.pairs, (x p.1 - x p.2) ^ 2 := by
  unfold presentGroundEdges
  rw [Finset.sum_image]
  · simp
  · intro p hp q hq heq
    rcases Sym2.eq_iff.mp heq with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Prod.ext (Option.some.inj hl) (Option.some.inj hr)
    · exact False.elim ((pair_endpoints_ne hUV (P.left_mem p hp) (P.right_mem q hq))
        (Option.some.inj hl))

theorem leftGroundEdges_energy (P : PartialMatching U V) (x : D → ℝ) :
    (∑ e ∈ P.leftGroundEdges, pairEnergy (groundedWeight x) e) =
      ∑ a ∈ U \ P.leftMatched, (x a) ^ 2 := by
  unfold leftGroundEdges
  rw [Finset.sum_image]
  · simp
  · intro a ha b hb heq
    rcases Sym2.eq_iff.mp heq with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Option.some.inj hl
    · cases hl

theorem rightGroundEdges_energy (P : PartialMatching U V) (x : D → ℝ) :
    (∑ e ∈ P.rightGroundEdges, pairEnergy (groundedWeight x) e) =
      ∑ a ∈ V \ P.rightMatched, (x a) ^ 2 := by
  unfold rightGroundEdges
  rw [Finset.sum_image]
  · simp
  · intro a ha b hb heq
    rcases Sym2.eq_iff.mp heq with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Option.some.inj hl
    · cases hl

/-- Parallel incidences and coincident ground edges are charged at most
once in the simple graph and retain all their charges in the defect. -/
theorem groundEdges_energy_le (P : PartialMatching U V) (hUV : Disjoint U V) (x : D → ℝ) :
    (∑ e ∈ P.groundEdges, pairEnergy (groundedWeight x) e) ≤ P.defect x x := by
  have h1 := nonneg_sum_union_le P.presentGroundEdges P.leftGroundEdges
    (pairEnergy (groundedWeight x)) (pairEnergy_nonneg _)
  have h2 := nonneg_sum_union_le (P.presentGroundEdges ∪ P.leftGroundEdges) P.rightGroundEdges
    (pairEnergy (groundedWeight x)) (pairEnergy_nonneg _)
  rw [P.presentGroundEdges_energy hUV, P.leftGroundEdges_energy] at h1
  rw [P.rightGroundEdges_energy] at h2
  change (∑ e ∈ P.groundEdges, pairEnergy (groundedWeight x) e) ≤ _ at h2
  unfold defect
  linarith

end PartialMatching

end TuranUniversality.Weighted

namespace TuranUniversality.Computation.MatchingSystem.Realization

open TuranUniversality.Weighted
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D Alphabet : Type*} [DecidableEq D]

def groundEdges (A : Realization D Alphabet) : Finset (Sym2 (Option D)) :=
  (A.J.groundEdges ∪ A.R.groundEdges) ∪ A.S.groundEdges

def groundGraph (A : Realization D Alphabet) : SimpleGraph (Option D) :=
  SimpleGraph.fromEdgeSet (A.groundEdges : Set (Sym2 (Option D)))

def totalDefect (A : Realization D Alphabet) (x : D → ℝ) : ℝ :=
  A.J.defect x x + A.R.defect x x + A.S.defect x x

theorem totalDefect_nonneg (A : Realization D Alphabet) (x : D → ℝ) :
    0 ≤ A.totalDefect x :=
  add_nonneg (add_nonneg (A.J.defect_nonneg x x) (A.R.defect_nonneg x x)) (A.S.defect_nonneg x x)

theorem J_groundEdges_subset (A : Realization D Alphabet) : A.J.groundEdges ⊆ A.groundEdges :=
  Finset.subset_union_left.trans Finset.subset_union_left

theorem R_groundEdges_subset (A : Realization D Alphabet) : A.R.groundEdges ⊆ A.groundEdges :=
  Finset.subset_union_right.trans Finset.subset_union_left

theorem S_groundEdges_subset (A : Realization D Alphabet) : A.S.groundEdges ⊆ A.groundEdges :=
  Finset.subset_union_right

theorem groundEdges_energy_le (A : Realization D Alphabet) (x : D → ℝ) :
    (∑ e ∈ A.groundEdges, pairEnergy (groundedWeight x) e) ≤ A.totalDefect x := by
  have h1 := nonneg_sum_union_le A.J.groundEdges A.R.groundEdges
    (pairEnergy (groundedWeight x)) (pairEnergy_nonneg _)
  have h2 := nonneg_sum_union_le (A.J.groundEdges ∪ A.R.groundEdges) A.S.groundEdges
    (pairEnergy (groundedWeight x)) (pairEnergy_nonneg _)
  have hJ := A.J.groundEdges_energy_le A.disjoint x
  have hR := A.R.groundEdges_energy_le A.disjoint.symm x
  have hS := A.S.groundEdges_energy_le A.disjoint.symm x
  change (∑ e ∈ A.groundEdges, pairEnergy (groundedWeight x) e) ≤ _ at h2
  unfold totalDefect
  linarith

theorem neighbor_ne (A : Realization D Alphabet) {a b : D} (h : A.Neighbor a b) : a ≠ b := by
  rcases h with h | h | h | h | h | h
  · exact pair_endpoints_ne A.disjoint (A.J.left_mem _ h) (A.J.right_mem _ h)
  · exact (pair_endpoints_ne A.disjoint (A.J.left_mem _ h) (A.J.right_mem _ h)).symm
  · exact pair_endpoints_ne A.disjoint.symm (A.R.left_mem _ h) (A.R.right_mem _ h)
  · exact (pair_endpoints_ne A.disjoint.symm (A.R.left_mem _ h) (A.R.right_mem _ h)).symm
  · exact pair_endpoints_ne A.disjoint.symm (A.S.left_mem _ h) (A.S.right_mem _ h)
  · exact (pair_endpoints_ne A.disjoint.symm (A.S.left_mem _ h) (A.S.right_mem _ h)).symm

theorem neighbor_groundAdj (A : Realization D Alphabet) {a b : D} (h : A.Neighbor a b) :
    A.groundGraph.Adj (some a) (some b) := by
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  constructor
  · change s(some a, some b) ∈ A.groundEdges
    rcases h with h | h | h | h | h | h
    · exact A.J_groundEdges_subset (A.J.present_mem_groundEdges h)
    · rw [Sym2.eq_swap]
      exact A.J_groundEdges_subset (A.J.present_mem_groundEdges h)
    · exact A.R_groundEdges_subset (A.R.present_mem_groundEdges h)
    · rw [Sym2.eq_swap]
      exact A.R_groundEdges_subset (A.R.present_mem_groundEdges h)
    · exact A.S_groundEdges_subset (A.S.present_mem_groundEdges h)
    · rw [Sym2.eq_swap]
      exact A.S_groundEdges_subset (A.S.present_mem_groundEdges h)
  · exact fun hab => A.neighbor_ne h (Option.some.inj hab)

theorem connected_groundReachable (A : Realization D Alphabet) {a b : D} (h : A.Connected a b) :
    A.groundGraph.Reachable (some a) (some b) := by
  apply (SimpleGraph.reachable_iff_reflTransGen _ _).mpr
  induction h with
  | refl => exact .refl
  | tail _ hn ih => exact ih.tail (A.neighbor_groundAdj hn)

/-- Failure of actual component closedness supplies a reachable missing
indexed incidence, hence an edge to the ground vertex. -/
theorem not_closed_groundReachable (A : Realization D Alphabet) (a : D) (h : ¬ A.ClosedAt a) :
    A.groundGraph.Reachable (some a) none := by
  classical
  have hmissing : ∃ b, A.Connected a b ∧ s(some b, none) ∈ A.groundEdges := by
    by_contra hnot
    apply h
    intro b hb
    have hn : s(some b, none) ∉ A.groundEdges := fun he => hnot ⟨b, hb, he⟩
    constructor
    · intro hcell
      refine ⟨?_, ?_, ?_⟩
      · by_contra hmiss
        exact hn (A.J_groundEdges_subset (A.J.missing_left_mem_groundEdges hcell hmiss))
      · by_contra hmiss
        exact hn (A.R_groundEdges_subset (A.R.missing_right_mem_groundEdges hcell hmiss))
      · by_contra hmiss
        exact hn (A.S_groundEdges_subset (A.S.missing_right_mem_groundEdges hcell hmiss))
    · intro hcolor
      refine ⟨?_, ?_, ?_⟩
      · by_contra hmiss
        exact hn (A.J_groundEdges_subset (A.J.missing_right_mem_groundEdges hcolor hmiss))
      · by_contra hmiss
        exact hn (A.R_groundEdges_subset (A.R.missing_left_mem_groundEdges hcolor hmiss))
      · by_contra hmiss
        exact hn (A.S_groundEdges_subset (A.S.missing_left_mem_groundEdges hcolor hmiss))
  obtain ⟨b, hb, hedge⟩ := hmissing
  have hadj : A.groundGraph.Adj (some b) none :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨hedge, by simp⟩
  exact (A.connected_groundReachable hb).trans hadj.reachable

/-- The actual sum of the three matching defects controls every marked
vertex whose actual relation component is open. -/
theorem open_grounded_bound [Fintype D] (A : Realization D Alphabet)
    (x : D → ℝ) (hx : ∀ d, 0 ≤ x d) (a : D) (hopen : ¬ A.ClosedAt a) :
    (x a) ^ 3 ≤ 4 * (∑ d, x d) * A.totalDefect x := by
  have h := graph_grounded_bound A.groundGraph A.groundEdges
    (fun v w hvw => ((SimpleGraph.fromEdgeSet_adj _).mp hvw).1)
    (groundedWeight x) (by intro v; cases v <;> simp [hx]) (some a) none rfl
    (A.not_closed_groundReachable a hopen)
  have hsum : (∑ v : Option D, groundedWeight x v) = ∑ d, x d := by
    simp [Fintype.sum_option]
  rw [hsum, groundedWeight_some] at h
  have hm : 0 ≤ 4 * (∑ d, x d) := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun d _ => hx d
  exact h.trans (mul_le_mul_of_nonneg_left (A.groundEdges_energy_le x) hm)

end TuranUniversality.Computation.MatchingSystem.Realization
