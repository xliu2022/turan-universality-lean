module

public import TuranUniversality.Weighted.Symmetric

/-! # Physical type classes and complete cross-type links -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v
variable {V : Type u} [DecidableEq V] {Types : Type v} [Fintype Types]

/-- The declared vertices partitioned into physical types. Empty classes are
allowed, as required for partial legal rootings. -/
structure TypePartition (I : Finset V) (Types : Type v) [Fintype Types] where
  block : Types → Finset V
  disjoint : Set.PairwiseDisjoint (Set.univ : Set Types) block
  cover : Finset.univ.biUnion block = I

namespace TypePartition

variable {I : Finset V}

def mass (P : TypePartition I Types) (x : V → ℝ) (t : Types) : ℝ := ∑ v ∈ P.block t, x v

def withinPairs (P : TypePartition I Types) : Finset (Finset V) :=
  Finset.univ.biUnion fun t => (P.block t).powersetCard 2

def crossPairs (P : TypePartition I Types) : Finset (Finset V) := I.powersetCard 2 \ P.withinPairs

def crossWeight (P : TypePartition I Types) (x : V → ℝ) : ℝ :=
  ∑ p ∈ P.crossPairs, ∏ v ∈ p, x v

theorem block_subset (P : TypePartition I Types) (t : Types) : P.block t ⊆ I := by
  intro v hv
  have hmem : v ∈ Finset.univ.biUnion P.block :=
    Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hv⟩
  simpa only [P.cover] using hmem

theorem sum_blocks (P : TypePartition I Types) (f : V → ℝ) :
    (∑ t, ∑ v ∈ P.block t, f v) = ∑ v ∈ I, f v := by
  calc
    (∑ t, ∑ v ∈ P.block t, f v) = ∑ v ∈ Finset.univ.biUnion P.block, f v :=
      (Finset.sum_biUnion (by simpa using P.disjoint)).symm
    _ = _ := congrArg (fun J : Finset V => ∑ v ∈ J, f v) P.cover

theorem pair_classes_disjoint (P : TypePartition I Types) :
    Set.PairwiseDisjoint (Set.univ : Set Types) (fun t => (P.block t).powersetCard 2) := by
  intro s hs t ht hst
  apply Finset.disjoint_left.mpr
  intro p hps hpt
  obtain ⟨hpsub, hpcard⟩ := Finset.mem_powersetCard.mp hps
  have hptsub := (Finset.mem_powersetCard.mp hpt).1
  have hpnonempty : p.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hpnonempty
  exact Finset.disjoint_left.mp (P.disjoint hs ht hst) (hpsub hv) (hptsub hv)

theorem withinPairs_subset (P : TypePartition I Types) : P.withinPairs ⊆ I.powersetCard 2 := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hpt
  exact Finset.mem_powersetCard.mpr ⟨hsub.trans (P.block_subset t), hcard⟩

theorem within_weight (P : TypePartition I Types) (x : V → ℝ) :
    (∑ p ∈ P.withinPairs, ∏ v ∈ p, x v) = ∑ t, elementary (P.block t) x 2 := by
  unfold withinPairs elementary
  exact Finset.sum_biUnion (by simpa using P.pair_classes_disjoint)

theorem cross_weight_partition (P : TypePartition I Types) (x : V → ℝ) :
    P.crossWeight x + (∑ t, elementary (P.block t) x 2) = elementary I x 2 := by
  rw [← P.within_weight]
  exact Finset.sum_sdiff P.withinPairs_subset

/-- The complete cross-type link has the elementary symmetric polynomial of
the type masses as its actual edge polynomial. -/
theorem crossWeight_eq [DecidableEq Types] (P : TypePartition I Types) (x : V → ℝ) :
    P.crossWeight x = elementary Finset.univ (P.mass x) 2 := by
  have hpartition := P.cross_weight_partition x
  have hI := elementary_second_identity I x
  have hTypes := elementary_second_identity Finset.univ (P.mass x)
  have hmass : (∑ t, P.mass x t) = ∑ v ∈ I, x v := P.sum_blocks x
  rw [hmass] at hTypes
  have hblocks : 2 * (∑ t, elementary (P.block t) x 2) =
      (∑ t, (P.mass x t) ^ 2) - ∑ v ∈ I, (x v) ^ 2 := by
    calc
      2 * (∑ t, elementary (P.block t) x 2) =
          ∑ t, 2 * elementary (P.block t) x 2 := Finset.mul_sum _ _ _
      _ = ∑ t, ((P.mass x t) ^ 2 - ∑ v ∈ P.block t, (x v) ^ 2) :=
        Finset.sum_congr rfl (fun t _ => elementary_second_identity (P.block t) x)
      _ = _ := by rw [Finset.sum_sub_distrib, P.sum_blocks]
  linarith

end TypePartition

/-- The type-level complete cross-link and the variance of type masses. -/
theorem type_polynomial_variance [DecidableEq Types] (y : Types → ℝ)
    (hcard : 0 < Fintype.card Types) :
    elementary Finset.univ y 2 = coeffC (Fintype.card Types) * (∑ t, y t) ^ 2 -
      rootVariance Finset.univ y / 2 := by
  have hm0 : (Fintype.card Types : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
  have hsecond := second_moment_shift Finset.univ y ((∑ t, y t) / (Fintype.card Types : ℝ))
  have hidentity : (∑ t, (y t) ^ 2) = rootVariance Finset.univ y +
      (∑ t, y t) ^ 2 / (Fintype.card Types : ℝ) := by
    simp only [Finset.card_univ] at hsecond
    change (∑ t, (y t) ^ 2) = rootVariance Finset.univ y +
      2 * ((∑ t, y t) / (Fintype.card Types : ℝ)) * (∑ t, y t) -
        (Fintype.card Types : ℝ) * ((∑ t, y t) / (Fintype.card Types : ℝ)) ^ 2 at hsecond
    rw [hsecond]
    field_simp
    ring
  have he := elementary_second_identity Finset.univ y
  rw [hidentity] at he
  have hc : coeffC (Fintype.card Types) = 1 / 2 - 1 / (2 * (Fintype.card Types : ℝ)) := by
    unfold coeffC
    field_simp
  rw [hc]
  simp only [div_eq_mul_inv, mul_inv_rev] at he ⊢
  norm_num at he ⊢
  nlinarith

theorem type_difference_bound (a b center : ℝ) :
    (a - b) ^ 2 / 2 ≤ (a - center) ^ 2 + (b - center) ^ 2 := by
  nlinarith [sq_nonneg (a + b - 2 * center)]

def incidenceWeight {Edges : Type*} {Kinds : Type*} [Fintype Edges] [DecidableEq Kinds]
    (source target : Edges → Kinds) (z : Edges → ℝ) (t : Kinds) : ℝ :=
  ∑ e, ((if source e = t then z e else 0) + (if target e = t then z e else 0))

theorem sum_incidence_mul {Edges : Type*} {Kinds : Type*}
    [Fintype Edges] [Fintype Kinds] [DecidableEq Kinds]
    (source target : Edges → Kinds) (z : Edges → ℝ) (f : Kinds → ℝ) :
    (∑ t, incidenceWeight source target z t * f t) =
      ∑ e, z e * (f (source e) + f (target e)) := by
  unfold incidenceWeight
  simp_rw [Finset.sum_mul, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_add_distrib]
  simp [eq_comm, mul_add]

/-- Summing the physical-type correction over indexed relation roots costs at
most the maximum weighted incidence times the type variance. -/
theorem type_correction_bound {Edges : Type*} {Kinds : Type*}
    [Fintype Edges] [Fintype Kinds] [DecidableEq Kinds]
    (source target : Edges → Kinds) (z : Edges → ℝ) (y : Kinds → ℝ) (center Δ : ℝ)
    (hz : ∀ e, 0 ≤ z e) (hΔ : ∀ t, incidenceWeight source target z t ≤ Δ) :
    (∑ e, z e / 2 * (y (source e) - y (target e)) ^ 2) ≤
      Δ * ∑ t, (y t - center) ^ 2 := by
  calc
    (∑ e, z e / 2 * (y (source e) - y (target e)) ^ 2) ≤
        ∑ e, z e * ((y (source e) - center) ^ 2 + (y (target e) - center) ^ 2) := by
      apply Finset.sum_le_sum
      intro e he
      have h := mul_le_mul_of_nonneg_left
        (type_difference_bound (y (source e)) (y (target e)) center) (hz e)
      nlinarith
    _ = ∑ t, incidenceWeight source target z t * (y t - center) ^ 2 :=
      (sum_incidence_mul source target z (fun t => (y t - center) ^ 2)).symm
    _ ≤ ∑ t, Δ * (y t - center) ^ 2 :=
      Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right (hΔ t) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end TuranUniversality.Weighted
