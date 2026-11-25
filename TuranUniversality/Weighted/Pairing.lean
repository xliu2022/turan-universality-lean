module

public import TuranUniversality.Weighted.Symmetric

/-! # Perfect missing-code matchings and their weighted complements -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u
variable {V : Type u} [DecidableEq V]

/-- A genuine partition of a vertex set into unordered pairs. -/
structure PerfectPairing (I : Finset V) where
  pairs : Finset (Finset V)
  pair_card : ∀ p ∈ pairs, p.card = 2
  disjoint : Set.PairwiseDisjoint (pairs : Set (Finset V)) id
  cover : pairs.biUnion id = I

namespace PerfectPairing

variable {I : Finset V}

def weight (C : PerfectPairing I) (z : V → ℝ) : ℝ :=
  ∑ p ∈ C.pairs, ∏ v ∈ p, z v

theorem pair_subset (C : PerfectPairing I) (p : Finset V) (hp : p ∈ C.pairs) : p ⊆ I := by
  intro v hv
  rw [← C.cover]
  exact Finset.mem_biUnion.mpr ⟨p, hp, hv⟩

theorem subset_pairs (C : PerfectPairing I) : C.pairs ⊆ I.powersetCard 2 := by
  intro p hp
  exact Finset.mem_powersetCard.mpr ⟨C.pair_subset p hp, C.pair_card p hp⟩

theorem sum_cover (C : PerfectPairing I) (f : V → ℝ) :
    (∑ p ∈ C.pairs, ∑ v ∈ p, f v) = ∑ v ∈ I, f v := by
  calc
    (∑ p ∈ C.pairs, ∑ v ∈ p, f v) = ∑ v ∈ C.pairs.biUnion id, f v :=
      (Finset.sum_biUnion C.disjoint).symm
    _ = _ := congrArg (fun J : Finset V => ∑ v ∈ J, f v) C.cover

theorem card_cover (C : PerfectPairing I) : 2 * C.pairs.card = I.card := by
  calc
    2 * C.pairs.card = ∑ _p ∈ C.pairs, (2 : ℕ) := by simp [Nat.mul_comm]
    _ = ∑ p ∈ C.pairs, p.card := Finset.sum_congr rfl (fun p hp => (C.pair_card p hp).symm)
    _ = (C.pairs.biUnion id).card := (Finset.card_biUnion C.disjoint).symm
    _ = I.card := congrArg Finset.card C.cover

theorem pair_square_identity (C : PerfectPairing I) (z : V → ℝ)
    (p : Finset V) (hp : p ∈ C.pairs) :
    (∑ v ∈ p, z v) ^ 2 = (∑ v ∈ p, (z v) ^ 2) + 2 * ∏ v ∈ p, z v := by
  have he : elementary p z 2 = ∏ v ∈ p, z v := by
    unfold elementary
    rw [← C.pair_card p hp, Finset.powersetCard_self]
    simp
  have h := elementary_second_identity p z
  rw [he] at h
  linarith

theorem sum_pair_squares (C : PerfectPairing I) (z : V → ℝ) :
    (∑ p ∈ C.pairs, (∑ v ∈ p, z v) ^ 2) =
      (∑ v ∈ I, (z v) ^ 2) + 2 * C.weight z := by
  calc
    (∑ p ∈ C.pairs, (∑ v ∈ p, z v) ^ 2) =
        ∑ p ∈ C.pairs, ((∑ v ∈ p, (z v) ^ 2) + 2 * ∏ v ∈ p, z v) :=
      Finset.sum_congr rfl (fun p hp => C.pair_square_identity z p hp)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, C.sum_cover]
      rfl

/-- The missing matching has a lower weighted bound for arbitrary real weights.
Nonnegativity is not required for this Cauchy--Schwarz step. -/
theorem weight_lower (C : PerfectPairing I) (z : V → ℝ) (hcard : 0 < I.card) :
    (∑ v ∈ I, z v) ^ 2 / (I.card : ℝ) - (∑ v ∈ I, (z v) ^ 2) / 2 ≤ C.weight z := by
  have hq0 : (0 : ℝ) < (I.card : ℝ) := by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq C.pairs
    (fun p => ∑ v ∈ p, z v) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
  rw [C.sum_cover, C.sum_pair_squares] at hcs
  have hcardEq : (I.card : ℝ) = 2 * (C.pairs.card : ℝ) := by
    exact_mod_cast C.card_cover.symm
  have hmid : (∑ v ∈ I, z v) ^ 2 / (I.card : ℝ) ≤
      C.weight z + (∑ v ∈ I, (z v) ^ 2) / 2 := by
    apply (div_le_iff₀ hq0).mpr
    rw [hcardEq]
    nlinarith
  linarith

theorem complement_weight (C : PerfectPairing I) (z : V → ℝ) :
    (∑ p ∈ I.powersetCard 2 \ C.pairs, ∏ v ∈ p, z v) + C.weight z = elementary I z 2 := by
  exact Finset.sum_sdiff C.subset_pairs

/-- A root-pair link avoiding one perfect code matching has weight at most
`b s²`, with exactly the manuscript's coefficient `b = (q-2)/(2q)`. -/
theorem complement_bound (C : PerfectPairing I) (z : V → ℝ) (hcard : 0 < I.card) :
    (∑ p ∈ I.powersetCard 2 \ C.pairs, ∏ v ∈ p, z v) ≤
      coeffB I.card * (∑ v ∈ I, z v) ^ 2 := by
  have hlow := C.weight_lower z hcard
  have hcomp := C.complement_weight z
  have hsecond := elementary_second_identity I z
  have hq0 : (I.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
  have hb : coeffB I.card = 1 / 2 - 1 / (I.card : ℝ) := by
    unfold coeffB
    field_simp
  rw [hb]
  simp only [div_eq_mul_inv] at hlow ⊢
  nlinarith

/-- The centered form of the missing-matching lower bound. -/
theorem weight_lower_variance (C : PerfectPairing I) (z : V → ℝ) (hcard : 0 < I.card) :
    (∑ v ∈ I, z v) ^ 2 / (2 * (I.card : ℝ)) - rootVariance I z / 2 ≤ C.weight z := by
  have hlow := C.weight_lower z hcard
  have hq0 : (I.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
  have hsecond := second_moment_shift I z ((∑ v ∈ I, z v) / (I.card : ℝ))
  change (∑ v ∈ I, (z v) ^ 2) = rootVariance I z +
    2 * ((∑ v ∈ I, z v) / (I.card : ℝ)) * (∑ v ∈ I, z v) -
      (I.card : ℝ) * ((∑ v ∈ I, z v) / (I.card : ℝ)) ^ 2 at hsecond
  have hidentity : (∑ v ∈ I, (z v) ^ 2) = rootVariance I z +
      (∑ v ∈ I, z v) ^ 2 / (I.card : ℝ) := by
    rw [hsecond]
    field_simp
    ring
  rw [hidentity] at hlow
  convert hlow using 1
  ring

theorem link_bound (C : PerfectPairing I) (z : V → ℝ) (L : Finset (Finset V))
    (hcard : 0 < I.card) (hz : ∀ v ∈ I, 0 ≤ z v)
    (hL : L ⊆ I.powersetCard 2 \ C.pairs) :
    (∑ p ∈ L, ∏ v ∈ p, z v) ≤ coeffB I.card * (∑ v ∈ I, z v) ^ 2 := by
  apply le_trans _ (C.complement_bound z hcard)
  apply Finset.sum_le_sum_of_subset_of_nonneg hL
  intro p hp hnot
  have hpI := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hp).1).1
  exact Finset.prod_nonneg fun v hv => hz v (hpI hv)

theorem double_complement_bound (C D : PerfectPairing I) (z : V → ℝ)
    (hcard : 0 < I.card) (hCD : Disjoint C.pairs D.pairs) :
    (∑ p ∈ (I.powersetCard 2 \ C.pairs) \ D.pairs, ∏ v ∈ p, z v) ≤
      coeffB I.card * (∑ v ∈ I, z v) ^ 2 -
        (∑ v ∈ I, z v) ^ 2 / (2 * (I.card : ℝ)) + rootVariance I z / 2 := by
  have hDsub : D.pairs ⊆ I.powersetCard 2 \ C.pairs := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨D.subset_pairs hp,
      fun hpc => Finset.disjoint_left.mp hCD hpc hp⟩
  have hsplit := Finset.sum_sdiff hDsub (f := fun p : Finset V => ∏ v ∈ p, z v)
  change (∑ p ∈ (I.powersetCard 2 \ C.pairs) \ D.pairs, ∏ v ∈ p, z v) + D.weight z =
    (∑ p ∈ I.powersetCard 2 \ C.pairs, ∏ v ∈ p, z v) at hsplit
  have hfirst := C.complement_bound z hcard
  have hsecond := D.weight_lower_variance z hcard
  linarith

theorem ambiguous_link_bound (C D : PerfectPairing I) (z : V → ℝ) (L : Finset (Finset V))
    (hcard : 0 < I.card) (hz : ∀ v ∈ I, 0 ≤ z v) (hCD : Disjoint C.pairs D.pairs)
    (hL : L ⊆ (I.powersetCard 2 \ C.pairs) \ D.pairs) :
    (∑ p ∈ L, ∏ v ∈ p, z v) ≤ coeffB I.card * (∑ v ∈ I, z v) ^ 2 -
      (∑ v ∈ I, z v) ^ 2 / (2 * (I.card : ℝ)) + rootVariance I z / 2 := by
  apply le_trans _ (double_complement_bound C D z hcard hCD)
  apply Finset.sum_le_sum_of_subset_of_nonneg hL
  intro p hp hnot
  have hpI := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1).1
  exact Finset.prod_nonneg fun v hv => hz v (hpI hv)

end PerfectPairing

end TuranUniversality.Weighted
