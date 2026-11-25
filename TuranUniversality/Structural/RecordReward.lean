module

public import TuranUniversality.Structural.RecordMoments

@[expose] public section

/-! # The witnessed-edge reward on all ordered four-samples

The reward counts a neutral position whose other three positions form an
actual inner edge.  At most one position can qualify.  Its mean is exactly
`24 * neutralMass * innerPolynomial`, and on an injective sample it agrees
with the nonzero phase label of the complete legal object.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem image_removeNth {n : ℕ} (i : Fin (n + 1)) (f : Fin (n + 1) → V) :
    Finset.univ.image f = insert (f i) (Finset.univ.image (i.removeNth f)) := by
  ext v
  simp [Fin.exists_iff_succAbove i, Fin.removeNth_apply, eq_comm]

theorem activeCount_injective {n : ℕ} (A : Finset V) (f : Fin n → V)
    (hf : Function.Injective f) : activeCount A f = (Finset.univ.image f ∩ A).card := by
  classical
  have him : ((Finset.univ : Finset (Fin n)).filter (fun i => f i ∈ A)).image f =
      Finset.univ.image f ∩ A := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    aesop
  rw [activeCount_eq_card, ← him, Finset.card_image_of_injective _ hf]

theorem edge_indicator_mean {r : ℕ} (G : RGraph V r) (x : V → ℝ) :
    weightedMean x (fun f : Fin r → V => truth (Finset.univ.image f ∈ G.edges)) =
      (r.factorial : ℝ) * G.edgePolynomial x := by
  calc
    _ = weightedMean x ((RGraph.oneEdge r).homIndicator G) := by
      apply weightedMean_congr
      intro f
      unfold truth RGraph.homIndicator
      congr 1
      exact propext (G.oneEdge_isHom f).symm
    _ = _ := G.weightedMean_oneEdge x

namespace LegalObject

variable {B : Finset (FiniteGraph 3)}

def WitnessAt (O : LegalObject B V) (i : Fin 4) (f : Fin 4 → V) : Prop :=
  f i ∉ O.active ∧ Finset.univ.image (i.removeNth f) ∈ O.projection.edges

noncomputable def reward (O : LegalObject B V) (f : Fin 4 → V) : ℝ :=
  ∑ i : Fin 4, truth (O.WitnessAt i f)

theorem WitnessAt.active_others {O : LegalObject B V} {i : Fin 4} {f : Fin 4 → V}
    (h : O.WitnessAt i f) (j : Fin 4) (hji : j ≠ i) : f j ∈ O.active := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
  have hm : i.removeNth f k ∈ Finset.univ.image (i.removeNth f) :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  simpa only [Fin.removeNth_apply, hk] using O.projection_supported _ h.2 hm

theorem WitnessAt.count_three {O : LegalObject B V} {i : Fin 4} {f : Fin 4 → V}
    (h : O.WitnessAt i f) : activeCount O.active f = 3 :=
  (activeCount_three_iff O.active f).mpr ⟨i, h.1, h.active_others⟩

theorem WitnessAt.unique {O : LegalObject B V} {i j : Fin 4} {f : Fin 4 → V}
    (hi : O.WitnessAt i f) (hj : O.WitnessAt j f) : i = j := by
  by_contra hij
  exact hi.1 (hj.active_others i hij)

theorem reward_eq_one {O : LegalObject B V} {i : Fin 4} {f : Fin 4 → V}
    (hi : O.WitnessAt i f) : O.reward f = 1 := by
  classical
  unfold reward
  rw [Finset.sum_eq_single i]
  · simp [truth, hi]
  · intro j _ hji
    have hn : ¬ O.WitnessAt j f := fun hj => hji (hj.unique hi)
    simp [truth, hn]
  · exact fun hn => False.elim (hn (Finset.mem_univ i))

theorem reward_eq_truth_exists (O : LegalObject B V) (f : Fin 4 → V) :
    O.reward f = truth (∃ i, O.WitnessAt i f) := by
  classical
  by_cases h : ∃ i, O.WitnessAt i f
  · obtain ⟨i, hi⟩ := h
    rw [reward_eq_one hi]
    simp [truth, show ∃ i, O.WitnessAt i f from ⟨i, hi⟩]
  · have hn (i : Fin 4) : ¬ O.WitnessAt i f := fun hi => h ⟨i, hi⟩
    simp [reward, truth, h, hn]

theorem reward_nonneg (O : LegalObject B V) (f : Fin 4 → V) : 0 ≤ O.reward f := by
  rw [O.reward_eq_truth_exists]
  exact truth_nonneg _

theorem reward_le_one (O : LegalObject B V) (f : Fin 4 → V) : O.reward f ≤ 1 := by
  rw [O.reward_eq_truth_exists]
  exact truth_le_one _

theorem image_active_of_neutral (O : LegalObject B V) (i : Fin 4) (f : Fin 4 → V)
    (hi : f i ∉ O.active) (hothers : ∀ j, j ≠ i → f j ∈ O.active) :
    Finset.univ.image f ∩ O.active = Finset.univ.image (i.removeNth f) := by
  have hsub : Finset.univ.image (i.removeNth f) ⊆ O.active := by
    intro v hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
    exact hothers (i.succAbove k) (Fin.succAbove_ne i k)
  rw [image_removeNth i f]
  ext v
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hv, hva⟩
    · exact False.elim (hi hva)
    · exact hv
  · intro hv
    exact ⟨Or.inr hv, hsub hv⟩

theorem exists_witness_iff (O : LegalObject B V) (f : Fin 4 → V) :
    (∃ i, O.WitnessAt i f) ↔ activeCount O.active f = 3 ∧
      (Finset.univ.image f ∩ O.active) ∈ O.projection.edges := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨hi.count_three, ?_⟩
    rw [O.image_active_of_neutral i f hi.1 hi.active_others]
    exact hi.2
  · rintro ⟨hc, he⟩
    obtain ⟨i, hi, ho⟩ := (activeCount_three_iff O.active f).mp hc
    refine ⟨i, hi, ?_⟩
    rwa [O.image_active_of_neutral i f hi ho] at he

theorem reward_eq_zero_of_count_ne (O : LegalObject B V) (f : Fin 4 → V)
    (hc : activeCount O.active f ≠ 3) : O.reward f = 0 := by
  rw [O.reward_eq_truth_exists, O.exists_witness_iff]
  simp [truth, hc]

theorem WitnessAt.injective {O : LegalObject B V} {i : Fin 4} {f : Fin 4 → V}
    (h : O.WitnessAt i f) : Function.Injective f := by
  have hnot : f i ∉ Finset.univ.image (i.removeNth f) :=
    fun hf => h.1 (O.projection_supported _ h.2 hf)
  have hc : (Finset.univ.image f).card = 4 := by
    rw [image_removeNth i f, Finset.card_insert_of_notMem hnot,
      O.projection.uniform _ h.2]
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin 4)) :=
    Finset.card_image_iff.mp (by simpa using hc)
  exact fun a b hab => hinj (Finset.mem_univ a) (Finset.mem_univ b) hab

/-- In particular, the reward vanishes on every repeated sample. -/
theorem reward_eq_zero_of_not_injective (O : LegalObject B V) (f : Fin 4 → V)
    (hf : ¬ Function.Injective f) : O.reward f = 0 := by
  have hn : ¬ ∃ i, O.WitnessAt i f := by rintro ⟨i, hi⟩; exact hf hi.injective
  rw [O.reward_eq_truth_exists]
  simp [truth, hn]

theorem reward_eq_of_injective (O : LegalObject B V) (f : Fin 4 → V)
    (hf : Function.Injective f) :
    O.reward f = truth ((Finset.univ.image f ∩ O.active) ∈ O.projection.edges) := by
  rw [O.reward_eq_truth_exists, O.exists_witness_iff, activeCount_injective _ _ hf]
  by_cases he : (Finset.univ.image f ∩ O.active) ∈ O.projection.edges
  · simp [he, O.projection.uniform _ he]
  · simp [he]

theorem Labels.phase_nonzero_iff {O : LegalObject B V} {X : Finset V} {l : Label}
    (h : O.Labels X l) : l.phase ≠ none ↔ X ∩ O.active ∈ O.projection.edges := by
  constructor
  · intro hn
    cases hp : l.phase with
    | none => exact False.elim (hn hp)
    | some a =>
      have he := (h.2 a).mpr hp
      cases a
      · exact (O.mem_projection _).mpr (Or.inl he)
      · exact (O.mem_projection _).mpr (Or.inr he)
  · intro he
    rcases (O.mem_projection _).mp he with hf | ht
    · rw [(h.2 false).mp hf]
      simp
    · rw [(h.2 true).mp ht]
      simp

theorem reward_eq_label (O : LegalObject B V) (f : Fin 4 → V)
    (hf : Function.Injective f) {l : Label} (hl : O.Labels (Finset.univ.image f) l) :
    O.reward f = truth (l.phase ≠ none) := by
  rw [O.reward_eq_of_injective f hf]
  congr 1
  exact propext hl.phase_nonzero_iff.symm

theorem witnessAt_mean (O : LegalObject B V) (x : V → ℝ) (hx : ProbabilityWeights x)
    (i : Fin 4) :
    weightedMean x (fun f : Fin 4 → V => truth (O.WitnessAt i f)) =
      (1 - ∑ v ∈ O.active, x v) * (6 * O.projection.edgePolynomial x) := by
  rw [weightedMean_insertNth x i]
  have hp (f : Fin 3 → V) :
      (∑ v, x v * truth (O.WitnessAt i (i.insertNth v f))) =
        (1 - ∑ v ∈ O.active, x v) * truth (Finset.univ.image f ∈ O.projection.edges) := by
    simp only [WitnessAt, Fin.insertNth_apply_same, Fin.removeNth_insertNth, truth_and]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, sum_neutral_weights x hx O.active]
  simp_rw [hp]
  rw [weightedMean_scale, edge_indicator_mean]
  norm_num

theorem reward_mean (O : LegalObject B V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    weightedMean x O.reward =
      24 * (1 - ∑ v ∈ O.active, x v) * O.projection.edgePolynomial x := by
  unfold reward
  rw [weightedMean_sum]
  simp_rw [O.witnessAt_mean x hx]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end LegalObject
end TuranUniversality.Structural
