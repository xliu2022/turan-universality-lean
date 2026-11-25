module

public import TuranUniversality.Weighted.Model
public import TuranUniversality.Weighted.Pairing

/-! # Candidate codes in an actual rooted three-graph

The code test is precisely avoidance of the missing perfect matching in the
root-pair link. Its singleton and nonsingleton alternatives define declared
and ambiguous vertices as in H1. The final theorem bounds the actual two-root
part of the ordinary edge polynomial.
-/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v w

structure CodeSystem (Roots : Type u) (Code : Type v)
    [DecidableEq Roots] [Fintype Roots] where
  missing : Code → PerfectPairing (Finset.univ : Finset Roots)
  disjoint : ∀ c d, c ≠ d → Disjoint (missing c).pairs (missing d).pairs

namespace CodeSystem

variable {Roots : Type u} {Code : Type v} {Data : Type w}
  [DecidableEq Roots] [Fintype Roots] [Fintype Code] [DecidableEq Data]

def candidates (C : CodeSystem Roots Code) (M : RootedModel Roots Data) (d : Data) : Finset Code :=
  Finset.univ.filter fun c => Disjoint (M.rootLink d) (C.missing c).pairs

@[simp] theorem mem_candidates (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) (c : Code) :
    c ∈ C.candidates M d ↔ Disjoint (M.rootLink d) (C.missing c).pairs := by
  simp [candidates]

def Declared (C : CodeSystem Roots Code) (M : RootedModel Roots Data) (d : Data) (c : Code) : Prop :=
  C.candidates M d = {c}

instance [DecidableEq Code] (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) (c : Code) : Decidable (C.Declared M d c) :=
  inferInstanceAs (Decidable (C.candidates M d = {c}))

def Ambiguous (C : CodeSystem Roots Code) (M : RootedModel Roots Data) (d : Data) : Prop :=
  2 ≤ (C.candidates M d).card

instance (C : CodeSystem Roots Code) (M : RootedModel Roots Data) (d : Data) :
    Decidable (C.Ambiguous M d) := inferInstanceAs (Decidable (2 ≤ (C.candidates M d).card))

def HasCandidates (C : CodeSystem Roots Code) (M : RootedModel Roots Data) : Prop :=
  ∀ d, (C.candidates M d).Nonempty

theorem declared_unique (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) (c c' : Code) (hc : C.Declared M d c) (hc' : C.Declared M d c') : c = c' := by
  exact Finset.singleton_inj.mp (hc.symm.trans hc')

theorem declared_or_ambiguous (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) (h : (C.candidates M d).Nonempty) :
    (∃ c, C.Declared M d c) ∨ C.Ambiguous M d := by
  by_cases hamb : 2 ≤ (C.candidates M d).card
  · exact Or.inr hamb
  · have hpos := Finset.card_pos.mpr h
    have hone : (C.candidates M d).card = 1 := by omega
    exact Or.inl (Finset.card_eq_one.mp hone)

theorem rootLink_subset_complement (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (d : Data) (c : Code) (hc : c ∈ C.candidates M d) :
    M.rootLink d ⊆ Finset.univ.powersetCard 2 \ (C.missing c).pairs := by
  intro p hp
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, M.rootLink_uniform d p hp⟩
  · intro hpc
    exact Finset.disjoint_left.mp ((C.mem_candidates M d c).mp hc) hp hpc

theorem rootLink_bound (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (z : Roots → ℝ) (d : Data) (hcard : 0 < Fintype.card Roots)
    (hz : ∀ r, 0 ≤ z r) (hc : (C.candidates M d).Nonempty) :
    (∑ p ∈ M.rootLink d, ∏ r ∈ p, z r) ≤ coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 := by
  obtain ⟨c, hc⟩ := hc
  simpa using (C.missing c).link_bound z (M.rootLink d) (by simpa using hcard)
    (fun r _ => hz r) (C.rootLink_subset_complement M d c hc)

theorem ambiguous_rootLink_bound (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (z : Roots → ℝ) (d : Data) (hcard : 0 < Fintype.card Roots)
    (hz : ∀ r, 0 ≤ z r) (ha : C.Ambiguous M d) :
    (∑ p ∈ M.rootLink d, ∏ r ∈ p, z r) ≤
      coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 -
        (∑ r, z r) ^ 2 / (2 * (Fintype.card Roots : ℝ)) + rootVariance Finset.univ z / 2 := by
  obtain ⟨c, hc, c', hc', hne⟩ := Finset.one_lt_card.mp ha
  have hL : M.rootLink d ⊆
      (Finset.univ.powersetCard 2 \ (C.missing c).pairs) \ (C.missing c').pairs := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨C.rootLink_subset_complement M d c hc hp,
      fun hpc => Finset.disjoint_left.mp ((C.mem_candidates M d c').mp hc') hp hpc⟩
  simpa using PerfectPairing.ambiguous_link_bound (C.missing c) (C.missing c') z (M.rootLink d)
    (by simpa using hcard) (fun r _ => hz r) (C.disjoint c c' hne) hL

def ambiguousVertices [Fintype Data] (C : CodeSystem Roots Code) (M : RootedModel Roots Data) :
    Finset Data := Finset.univ.filter fun d => C.Ambiguous M d

def ambiguousWeight [Fintype Data] (C : CodeSystem Roots Code) (M : RootedModel Roots Data)
    (x : Data → ℝ) : ℝ := ∑ d ∈ C.ambiguousVertices M, x d

/-- The exact two-root contribution bound used in the unmarked estimate. -/
theorem two_root_contribution_bound [Fintype Data]
    (C : CodeSystem Roots Code) (M : RootedModel Roots Data) (z : Roots → ℝ) (x : Data → ℝ)
    (hcard : 0 < Fintype.card Roots) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d)
    (hH1 : C.HasCandidates M) :
    M.contribution 2 z x ≤ coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 * (∑ d, x d) -
      (∑ r, z r) ^ 2 * C.ambiguousWeight M x / (2 * (Fintype.card Roots : ℝ)) +
        C.ambiguousWeight M x / 2 * rootVariance Finset.univ z := by
  let B := coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2
  let loss := (∑ r, z r) ^ 2 / (2 * (Fintype.card Roots : ℝ)) - rootVariance Finset.univ z / 2
  have hpoint : ∀ d, (∑ p ∈ M.rootLink d, ∏ r ∈ p, z r) ≤
      B - if C.Ambiguous M d then loss else 0 := by
    intro d
    by_cases ha : C.Ambiguous M d
    · simp only [ha, ite_true]
      have h := C.ambiguous_rootLink_bound M z d hcard hz ha
      dsimp [B, loss]
      linarith
    · simp only [ha, ite_false, sub_zero]
      exact C.rootLink_bound M z d hcard hz (hH1 d)
  have hsum : M.contribution 2 z x ≤
      ∑ d, x d * (B - if C.Ambiguous M d then loss else 0) := by
    rw [M.contribution_two_eq]
    exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hpoint d) (hx d)
  have herase : (∑ d, x d * (if C.Ambiguous M d then loss else 0)) =
      loss * C.ambiguousWeight M x := by
    unfold ambiguousWeight ambiguousVertices
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> ring
  have htotal : (∑ d, x d * (B - if C.Ambiguous M d then loss else 0)) =
      coeffB (Fintype.card Roots) * (∑ r, z r) ^ 2 * (∑ d, x d) -
        (∑ r, z r) ^ 2 * C.ambiguousWeight M x / (2 * (Fintype.card Roots : ℝ)) +
          C.ambiguousWeight M x / 2 * rootVariance Finset.univ z := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, herase]
    dsimp [B, loss]
    ring
  exact hsum.trans_eq htotal

end CodeSystem

end TuranUniversality.Weighted
