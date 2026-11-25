module

public import TuranUniversality.Weighted.Completion

/-! # Exact value and natural clone sizes of balanced completed models -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace PartialMatching

variable {D : Type*} [DecidableEq D] {U V : Finset D}

def Full (P : PartialMatching U V) : Prop := P.leftMatched = U ∧ P.rightMatched = V

theorem full_defect_constant (P : PartialMatching U V) (h : P.Full) (β : ℝ) :
    P.defect (fun _ => β) (fun _ => β) = 0 := by
  simp [defect, h.1, h.2]

end PartialMatching

namespace Completion

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]
  {S : CompilerSignature Roots Code Kinds L}

omit [DecidableEq Code] [Fintype Code] in
theorem balanced_card (C : Completion S Data) (N : ℕ) (hN : ∀ k, (C.partition.block k).card = N) :
    Fintype.card Data = Fintype.card Kinds * N := by
  have h := C.partition.sum_blocks (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, hN] at h
  exact_mod_cast h.symm

omit [DecidableEq Code] [Fintype Code] in
theorem balanced_mass (C : Completion S Data) (N : ℕ) (hN : ∀ k, (C.partition.block k).card = N)
    (β : ℝ) (k : Kinds) : C.partition.mass (fun _ => β) k = (N : ℝ) * β := by
  simp [TypePartition.mass, hN]

theorem balanced_dataLink_weight (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) (hfull : ∀ e, (C.matching e).Full)
    (β : ℝ) (r : Roots) :
    (∑ p ∈ C.dataLink r, ∏ _d ∈ p, β) =
      (Fintype.card Kinds : ℝ) * ((Fintype.card Kinds : ℝ) - 1) / 2 * ((N : ℝ) * β) ^ 2 := by
  have hmass : C.partition.mass (fun _ => β) = fun _ => (N : ℝ) * β := by
    funext k
    exact C.balanced_mass N hN β k
  by_cases hr : ∃ p : Fin 3 × Fin L, S.copyRoot p = r
  · obtain ⟨⟨e, j⟩, rfl⟩ := hr
    rw [C.dataLink_copy]
    change (∑ p ∈ C.partition.matchedLink _ _ (C.matching e), ∏ d ∈ p, (fun _ : Data => β) d) = _
    rw [C.partition.matchedLink_weight _ _ (S.source_ne_target e), hmass,
      (C.matching e).full_defect_constant (hfull e)]
    simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero, sub_zero]
    rw [elementary_constant_two]
    simp only [Finset.card_univ]
    ring
  · rw [C.dataLink_additional r hr]
    change C.partition.crossWeight (fun _ => β) = _
    rw [C.partition.crossWeight_eq, hmass]
    rw [elementary_constant_two]
    simp only [Finset.card_univ]
    ring

/-- The completed graph attains the baseline plus precisely the contributions
of its actual data-only marker triples. -/
theorem balanced_polynomial (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) (hfull : ∀ e, (C.matching e).Full)
    (α β : ℝ) :
    C.model.toRGraph.edgePolynomial (Sum.elim (fun _ => α) (fun _ => β)) =
      (Fintype.card Roots : ℝ) * ((Fintype.card Roots : ℝ) - 1) *
        ((Fintype.card Roots : ℝ) - 2) / 6 * α ^ 3 +
      (Fintype.card Data : ℝ) * β *
        ((Fintype.card Roots : ℝ) * ((Fintype.card Roots : ℝ) - 2) / 2 * α ^ 2) +
      (Fintype.card Roots : ℝ) * α *
        ((Fintype.card Kinds : ℝ) * ((Fintype.card Kinds : ℝ) - 1) / 2 * ((N : ℝ) * β) ^ 2) +
      (C.markers.card : ℝ) * β ^ 3 := by
  rw [C.model.edgePolynomial_links, C.model_rootTriples, C.model_dataTriples]
  simp_rw [C.model_rootLink, complement_constant_weight, C.model_dataLink,
    C.balanced_dataLink_weight N hN hfull]
  have hmarkers : (∑ p ∈ C.markers, ∏ _d ∈ p, β) = (C.markers.card : ℝ) * β ^ 3 := by
    have hterm : ∀ p ∈ C.markers, (∏ _d ∈ p, β) = β ^ 3 := by
      intro p hp
      simp only [Finset.prod_const, C.marker_uniform p hp]
    rw [Finset.sum_congr rfl hterm]
    simp
  rw [hmarkers]
  change elementary Finset.univ (fun _ : Roots => α) 3 + _ + _ + _ = _
  rw [elementary_constant_three]
  simp only [Finset.card_univ, Finset.sum_const, nsmul_eq_mul]
  ring

theorem balanced_value (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) (hfull : ∀ e, (C.matching e).Full)
    (t : ℝ) (hq : 0 < Fintype.card Roots) (hm : 0 < Fintype.card Kinds) (hNpos : 0 < N) :
    C.model.toRGraph.edgePolynomial
      (Sum.elim (fun _ => (1 - t) / (Fintype.card Roots : ℝ))
        (fun _ => t / ((Fintype.card Kinds : ℝ) * (N : ℝ)))) =
      baseline (Fintype.card Kinds) (Fintype.card Roots) t +
        (C.markers.card : ℝ) * (t / ((Fintype.card Kinds : ℝ) * (N : ℝ))) ^ 3 := by
  have hq0 : (Fintype.card Roots : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hm0 : (Fintype.card Kinds : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
  rw [C.balanced_polynomial N hN hfull, C.balanced_card N hN, Nat.cast_mul]
  unfold baseline cubic coeffA coeffB coeffC
  field_simp

def cloneSizes (N : ℕ) : Roots ⊕ Data → ℕ :=
  Sum.elim (fun _ => rootClones (Fintype.card Kinds) N) (fun _ => dataClones (Fintype.card Kinds))

theorem cloneSizes_total (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) :
    (∑ v : Roots ⊕ Data, cloneSizes (Kinds := Kinds) N v) =
      totalClones (Fintype.card Roots) (Fintype.card Kinds) N := by
  simp [cloneSizes, Fintype.sum_sum_type, totalClones, C.balanced_card N hN]

theorem cloneSizes_total_pos (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) (hq : 0 < Fintype.card Roots)
    (hm : 3 ≤ Fintype.card Kinds) (hNpos : 0 < N) :
    0 < ∑ v : Roots ⊕ Data, cloneSizes (Kinds := Kinds) N v := by
  rw [C.cloneSizes_total N hN]
  exact totalClones_pos _ _ _ hq hm hNpos

theorem balanced_integer_value (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) (hfull : ∀ e, (C.matching e).Full)
    (hq : 0 < Fintype.card Roots) (hm : 3 ≤ Fintype.card Kinds) (hNpos : 0 < N) :
    C.model.toRGraph.edgePolynomial
      (fun v => (cloneSizes (Kinds := Kinds) N v : ℝ) /
        ((∑ w : Roots ⊕ Data, cloneSizes (Kinds := Kinds) N w : ℕ) : ℝ)) =
      baselineMax (Fintype.card Kinds) (Fintype.card Roots) +
        (C.markers.card : ℝ) *
          (criticalMass (Fintype.card Kinds) (Fintype.card Roots) /
            ((Fintype.card Kinds : ℝ) * (N : ℝ))) ^ 3 := by
  have hw : (fun v => (cloneSizes (Kinds := Kinds) N v : ℝ) /
        ((∑ w : Roots ⊕ Data, cloneSizes (Kinds := Kinds) N w : ℕ) : ℝ)) =
      Sum.elim
        (fun _ : Roots => (1 - criticalMass (Fintype.card Kinds) (Fintype.card Roots)) /
          (Fintype.card Roots : ℝ))
        (fun _ : Data => criticalMass (Fintype.card Kinds) (Fintype.card Roots) /
          ((Fintype.card Kinds : ℝ) * (N : ℝ))) := by
    funext v
    rw [C.cloneSizes_total N hN]
    cases v with
    | inl r => exact root_clone_weight _ _ N hq hm hNpos
    | inr d =>
      simpa only [cloneSizes, Sum.elim_inr, Nat.cast_mul] using
        (data_clone_weight (Fintype.card Roots) (Fintype.card Kinds) N hq hm hNpos)
  rw [hw, C.balanced_value N hN hfull _ hq (by omega) hNpos]
  rfl

theorem balanced_integer_strict (C : Completion S Data) (N : ℕ)
    (hN : ∀ k, (C.partition.block k).card = N) (hfull : ∀ e, (C.matching e).Full)
    (hq : 0 < Fintype.card Roots) (hm : 3 ≤ Fintype.card Kinds) (hNpos : 0 < N)
    (hmarker : 0 < C.markers.card) :
    baselineMax (Fintype.card Kinds) (Fintype.card Roots) <
      C.model.toRGraph.edgePolynomial
        (fun v => (cloneSizes (Kinds := Kinds) N v : ℝ) /
          ((∑ w : Roots ⊕ Data, cloneSizes (Kinds := Kinds) N w : ℕ) : ℝ)) := by
  rw [C.balanced_integer_value N hN hfull hq hm hNpos]
  have hm2 : (2 : ℝ) < Fintype.card Kinds := by exact_mod_cast (by omega : 2 < Fintype.card Kinds)
  have hqr : (0 : ℝ) < Fintype.card Roots := by exact_mod_cast hq
  have hmr : (0 : ℝ) < Fintype.card Kinds := by exact_mod_cast (by omega : 0 < Fintype.card Kinds)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmarkerR : (0 : ℝ) < C.markers.card := by exact_mod_cast hmarker
  have ht0 : 0 < criticalMass (Fintype.card Kinds) (Fintype.card Roots) := by
    unfold criticalMass
    have hk := kappa_pos (Fintype.card Kinds : ℝ) hm2
    positivity
  exact lt_add_of_pos_right _ (mul_pos hmarkerR (pow_pos (div_pos ht0 (mul_pos hmr hNr)) 3))

end Completion

end TuranUniversality.Weighted
