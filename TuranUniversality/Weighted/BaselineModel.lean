module

public import TuranUniversality.Weighted.Model
public import TuranUniversality.Weighted.Codes
public import TuranUniversality.Weighted.IntegerWeights

/-! # The explicit unmarked baseline three-graph

There is one data vertex per physical type. Every one-root data link is
complete; its special cell/color pair is the singleton perfect matching.
The root-pair link of each data vertex is the complement of its code matching.
-/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v
variable {Roots : Type u} {Data : Type v}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Data] [Fintype Data]

def baselineModel (missing : Data → PerfectPairing (Finset.univ : Finset Roots)) :
    RootedModel Roots Data where
  edges := Finset.univ.filter fun p => p.1.card + p.2.card = 3 ∧
    (p.2 = ∅ ∨ (∃ d, p.2 = {d} ∧ p.1 ∉ (missing d).pairs) ∨ (p.1.card = 1 ∧ p.2.card = 2))
  uniform := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1

theorem baselineModel_rootTriples (missing : Data → PerfectPairing (Finset.univ : Finset Roots)) :
    (baselineModel missing).rootTriples = Finset.univ.powersetCard 3 := by
  ext p
  rw [RootedModel.mem_rootTriples]
  simp [baselineModel, Finset.mem_powersetCard]

theorem baselineModel_rootLink (missing : Data → PerfectPairing (Finset.univ : Finset Roots))
    (d : Data) :
    (baselineModel missing).rootLink d = Finset.univ.powersetCard 2 \ (missing d).pairs := by
  ext p
  rw [RootedModel.mem_rootLink]
  have hcard : p.card + 1 = 3 ↔ p.card = 2 := by omega
  simp [baselineModel, Finset.mem_powersetCard, hcard, Finset.singleton_inj]

theorem baselineModel_dataLink (missing : Data → PerfectPairing (Finset.univ : Finset Roots))
    (r : Roots) : (baselineModel missing).dataLink r = Finset.univ.powersetCard 2 := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (baselineModel missing).dataLink_uniform r p hp⟩
  · intro hp
    have hpc := (Finset.mem_powersetCard.mp hp).2
    rw [RootedModel.mem_dataLink]
    simp only [baselineModel, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by simp [hpc], Or.inr (Or.inr ⟨by simp, hpc⟩)⟩

theorem baselineModel_dataTriples (missing : Data → PerfectPairing (Finset.univ : Finset Roots)) :
    (baselineModel missing).dataTriples = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rw [RootedModel.mem_dataTriples] at hp
  simp only [baselineModel, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.card_empty, zero_add] at hp
  obtain ⟨hcard, he | ⟨d, hd, hnot⟩ | hbad⟩ := hp
  · simp [he] at hcard
  · simp [hd] at hcard
  · omega

theorem elementary_constant_two {V : Type*} [DecidableEq V] (I : Finset V) (a : ℝ) :
    elementary I (fun _ => a) 2 = ((I.card : ℝ) ^ 2 - (I.card : ℝ)) * a ^ 2 / 2 := by
  have h := elementary_second_identity I (fun _ => a)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  nlinarith

theorem elementary_constant_three {V : Type*} [DecidableEq V] (I : Finset V) (a : ℝ) :
    elementary I (fun _ => a) 3 =
      ((I.card : ℝ) ^ 3 - 3 * (I.card : ℝ) ^ 2 + 2 * (I.card : ℝ)) * a ^ 3 / 6 := by
  have h := elementary_third_identity I (fun _ => a)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  nlinarith

theorem pairing_constant_weight {V : Type*} [DecidableEq V] {I : Finset V}
    (C : PerfectPairing I) (a : ℝ) : C.weight (fun _ => a) = (C.pairs.card : ℝ) * a ^ 2 := by
  unfold PerfectPairing.weight
  simp only [Finset.prod_const]
  calc
    (∑ p ∈ C.pairs, a ^ p.card) = ∑ _p ∈ C.pairs, a ^ 2 :=
      Finset.sum_congr rfl (fun p hp => by rw [C.pair_card p hp])
    _ = _ := by simp

theorem complement_constant_weight {V : Type*} [DecidableEq V] {I : Finset V}
    (C : PerfectPairing I) (a : ℝ) :
    (∑ p ∈ I.powersetCard 2 \ C.pairs, ∏ _v ∈ p, a) =
      ((I.card : ℝ) ^ 2 - 2 * (I.card : ℝ)) * a ^ 2 / 2 := by
  have h := C.complement_weight (fun _ => a)
  rw [pairing_constant_weight, elementary_constant_two] at h
  have hc : (2 : ℝ) * (C.pairs.card : ℝ) = (I.card : ℝ) := by exact_mod_cast C.card_cover
  have hca := congrArg (fun b : ℝ => b * a ^ 2) hc
  nlinarith

/-- Exact polynomial of the concrete baseline graph at constant root/data
weights, before imposing probability normalization. -/
theorem baselineModel_polynomial (missing : Data → PerfectPairing (Finset.univ : Finset Roots))
    (a b : ℝ) :
    (baselineModel missing).toRGraph.edgePolynomial (Sum.elim (fun _ => a) (fun _ => b)) =
      ((Fintype.card Roots : ℝ) ^ 3 - 3 * (Fintype.card Roots : ℝ) ^ 2 +
        2 * (Fintype.card Roots : ℝ)) * a ^ 3 / 6 +
      (Fintype.card Data : ℝ) * ((Fintype.card Roots : ℝ) ^ 2 -
        2 * (Fintype.card Roots : ℝ)) * a ^ 2 * b / 2 +
      (Fintype.card Roots : ℝ) * ((Fintype.card Data : ℝ) ^ 2 -
        (Fintype.card Data : ℝ)) * a * b ^ 2 / 2 := by
  rw [RootedModel.edgePolynomial_links]
  simp_rw [baselineModel_rootTriples, baselineModel_rootLink,
    baselineModel_dataLink, baselineModel_dataTriples, Finset.sum_empty]
  change elementary Finset.univ (fun _ : Roots => a) 3 +
    (∑ d, b * (∑ p ∈ Finset.univ.powersetCard 2 \ (missing d).pairs, ∏ _v ∈ p, a)) +
    (∑ r : Roots, a * elementary Finset.univ (fun _ : Data => b) 2) + 0 = _
  simp_rw [elementary_constant_three, complement_constant_weight, elementary_constant_two]
  simp only [Finset.card_univ, Finset.sum_const, nsmul_eq_mul]
  ring

theorem baselineModel_value (missing : Data → PerfectPairing (Finset.univ : Finset Roots))
    (t : ℝ) (hq : 0 < Fintype.card Roots) (hm : 0 < Fintype.card Data) :
    (baselineModel missing).toRGraph.edgePolynomial
      (Sum.elim (fun _ => (1 - t) / (Fintype.card Roots : ℝ))
        (fun _ => t / (Fintype.card Data : ℝ))) =
      baseline (Fintype.card Data : ℝ) (Fintype.card Roots : ℝ) t := by
  have hq0 : (Fintype.card Roots : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hm0 : (Fintype.card Data : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [baselineModel_polynomial]
  unfold baseline cubic coeffA coeffB coeffC
  field_simp
  ring

theorem baselineModel_declared {Code : Type*} [Fintype Code]
    (C : CodeSystem Roots Code) (code : Data → Code) (hq : 0 < Fintype.card Roots) (d : Data) :
    C.Declared (baselineModel fun v => C.missing (code v)) d (code d) := by
  apply Finset.ext
  intro c
  rw [C.mem_candidates, baselineModel_rootLink, Finset.mem_singleton]
  constructor
  · intro hdisj
    by_contra hne
    have hcard := (C.missing c).card_cover
    have hq' : 0 < (Finset.univ : Finset Roots).card := by simpa using hq
    have hpnonempty : (C.missing c).pairs.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp⟩ := hpnonempty
    have hallowed : p ∈ Finset.univ.powersetCard 2 \ (C.missing (code d)).pairs :=
      Finset.mem_sdiff.mpr ⟨(C.missing c).subset_pairs hp,
        fun hc => Finset.disjoint_left.mp (C.disjoint (code d) c (fun he => hne he.symm)) hc hp⟩
    exact Finset.disjoint_left.mp hdisj hallowed hp
  · rintro rfl
    exact Finset.sdiff_disjoint

theorem baselineModel_hasCandidates {Code : Type*} [Fintype Code]
    (C : CodeSystem Roots Code) (code : Data → Code) (hq : 0 < Fintype.card Roots) :
    C.HasCandidates (baselineModel fun v => C.missing (code v)) := by
  intro d
  rw [baselineModel_declared C code hq d]
  exact Finset.singleton_nonempty _

def baselineSizes : Roots ⊕ Data → ℕ :=
  Sum.elim (fun _ => rootClones (Fintype.card Data) 1) (fun _ => dataClones (Fintype.card Data))

omit [DecidableEq Roots] [DecidableEq Data] in
theorem baselineSizes_total :
    (∑ v : Roots ⊕ Data, baselineSizes v) =
      totalClones (Fintype.card Roots) (Fintype.card Data) 1 := by
  simp [baselineSizes, Fintype.sum_sum_type, totalClones]

omit [DecidableEq Roots] [DecidableEq Data] in
theorem baselineSizes_total_pos (hq : 0 < Fintype.card Roots) (hm : 3 ≤ Fintype.card Data) :
    0 < ∑ v : Roots ⊕ Data, baselineSizes v := by
  rw [baselineSizes_total]
  exact totalClones_pos _ _ 1 hq hm (by omega)

/-- The concrete graph realizes `B(t₀)` with explicit natural clone sizes,
ready for the ordinary Turán-density lower bridge. -/
theorem baselineModel_integer_value (missing : Data → PerfectPairing (Finset.univ : Finset Roots))
    (hq : 0 < Fintype.card Roots) (hm : 3 ≤ Fintype.card Data) :
    (baselineModel missing).toRGraph.edgePolynomial
      (fun v => (baselineSizes v : ℝ) / ((∑ w : Roots ⊕ Data, baselineSizes w : ℕ) : ℝ)) =
      baselineMax (Fintype.card Data : ℝ) (Fintype.card Roots : ℝ) := by
  have hweights : (fun v => (baselineSizes v : ℝ) /
        ((∑ w : Roots ⊕ Data, baselineSizes w : ℕ) : ℝ)) =
      Sum.elim
        (fun _ : Roots => (1 - criticalMass (Fintype.card Data : ℝ) (Fintype.card Roots : ℝ)) /
          (Fintype.card Roots : ℝ))
        (fun _ : Data => criticalMass (Fintype.card Data : ℝ) (Fintype.card Roots : ℝ) /
          (Fintype.card Data : ℝ)) := by
    funext v
    rw [baselineSizes_total]
    cases v with
    | inl r => exact root_clone_weight _ _ 1 hq hm (by omega)
    | inr d =>
      simpa only [Nat.mul_one, baselineSizes, Sum.elim_inr] using
        (data_clone_weight (Fintype.card Roots) (Fintype.card Data) 1 hq hm (by omega))
  rw [hweights, baselineModel_value missing _ hq (by omega)]
  rfl

end TuranUniversality.Weighted
