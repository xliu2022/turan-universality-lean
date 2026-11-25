module

public import TuranUniversality.Density.SetFamilyBasic
public import TuranUniversality.Density.FamilyExtremal

@[expose] public section

/-! # Ordinary Turán density of an arbitrary forbidden family

The extremal number is the maximum edge count of ordinary free labelled
graphs, with zero as the convention when no such graph exists. The deletion
inequality and the ordinary limit are proved without an edge-nonemptiness
assumption on the forbidden family.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.SetFamily

noncomputable section

variable {r : ℕ}

def extremalNumber (F : Set (FiniteGraph r)) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ G : RGraph (Fin n) r,
    Free F G ∧ G.edges.card = k) (n.choose r)

def extremalDensity (F : Set (FiniteGraph r)) (n : ℕ) : ℝ :=
  (extremalNumber F n : ℝ) / (n.choose r : ℝ)

def turanDensity (F : Set (FiniteGraph r)) : ℝ :=
  ⨅ n : ℕ, extremalDensity F (n + r)

@[simp] theorem extremalNumber_finset (F : Finset (FiniteGraph r)) (n : ℕ) :
    extremalNumber (F : Set (FiniteGraph r)) n = familyExtremalNumber F n := by
  classical
  simp only [extremalNumber, familyExtremalNumber, free_finset]

@[simp] theorem extremalDensity_finset (F : Finset (FiniteGraph r)) (n : ℕ) :
    extremalDensity (F : Set (FiniteGraph r)) n = familyExtremalDensity F n := by
  rw [extremalDensity, familyExtremalDensity, extremalNumber_finset]

@[simp] theorem turanDensity_finset (F : Finset (FiniteGraph r)) :
    turanDensity (F : Set (FiniteGraph r)) = familyTuranDensity F := by
  simp only [turanDensity, familyTuranDensity, extremalDensity_finset]

theorem extremalNumber_truncate (F : Set (FiniteGraph r)) (n : ℕ) :
    familyExtremalNumber (truncate F n) n = extremalNumber F n := by
  classical
  simp only [familyExtremalNumber, extremalNumber, free_truncate_iff]

theorem edge_card_le_extremalNumber (F : Set (FiniteGraph r))
    {n : ℕ} (G : RGraph (Fin n) r) (hG : Free F G) :
    G.edges.card ≤ extremalNumber F n := by
  classical
  exact Nat.le_findGreatest G.edge_card_le_choose ⟨G, hG, rfl⟩

theorem extremalNumber_le_choose (F : Set (FiniteGraph r)) (n : ℕ) :
    extremalNumber F n ≤ n.choose r := by
  classical
  exact Nat.findGreatest_le _

theorem exists_extremal_of_ne_zero (F : Set (FiniteGraph r)) (n : ℕ)
    (h : extremalNumber F n ≠ 0) :
    ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = extremalNumber F n := by
  classical
  exact Nat.findGreatest_of_ne_zero
    (P := fun k => ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = k)
    (n := n.choose r) (m := extremalNumber F n) rfl h

theorem exists_extremal (F : Set (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = extremalNumber F n := by
  classical
  unfold extremalNumber
  exact Nat.findGreatest_spec
    (P := fun k => ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = k)
    (Nat.zero_le (n.choose r))
    ⟨RGraph.empty (Fin n) r, free_emptyGraph F hedges n, rfl⟩

theorem extremalNumber_le_iff (F : Set (FiniteGraph r)) (n k : ℕ) :
    extremalNumber F n ≤ k ↔
      ∀ G : RGraph (Fin n) r, Free F G → G.edges.card ≤ k := by
  constructor
  · intro h G hG
    exact (edge_card_le_extremalNumber F G hG).trans h
  · intro h
    by_cases hz : extremalNumber F n = 0
    · simp [hz]
    · obtain ⟨G, hG, hc⟩ := exists_extremal_of_ne_zero F n hz
      rw [← hc]
      exact h G hG

theorem extremalNumber_antitone {F H : Set (FiniteGraph r)} (h : F ⊆ H) (n : ℕ) :
    extremalNumber H n ≤ extremalNumber F n := by
  apply (extremalNumber_le_iff H n _).mpr
  intro G hG
  exact edge_card_le_extremalNumber F G (hG.mono h)

theorem extremalDensity_nonneg (F : Set (FiniteGraph r)) (n : ℕ) :
    0 ≤ extremalDensity F n := by
  unfold extremalDensity
  positivity

theorem extremalDensity_le_one (F : Set (FiniteGraph r)) {n : ℕ} (hn : r ≤ n) :
    extremalDensity F n ≤ 1 := by
  have hp : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  apply (div_le_iff₀ hp).mpr
  simpa using (Nat.cast_le.mpr (extremalNumber_le_choose F n) :
    (extremalNumber F n : ℝ) ≤ n.choose r)

theorem extremalDensity_antitone {F H : Set (FiniteGraph r)} (h : F ⊆ H) (n : ℕ) :
    extremalDensity H n ≤ extremalDensity F n :=
  div_le_div_of_nonneg_right (Nat.cast_le.mpr (extremalNumber_antitone h n))
    (Nat.cast_nonneg _)

theorem density_range_bddBelow (F : Set (FiniteGraph r)) :
    BddBelow (Set.range (fun n : ℕ => extremalDensity F (n + r))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact extremalDensity_nonneg F _⟩

theorem turanDensity_nonneg (F : Set (FiniteGraph r)) : 0 ≤ turanDensity F :=
  le_ciInf fun n => extremalDensity_nonneg F (n + r)

theorem turanDensity_le_extremalDensity (F : Set (FiniteGraph r))
    {n : ℕ} (hn : r ≤ n) : turanDensity F ≤ extremalDensity F n := by
  have h := ciInf_le (density_range_bddBelow F) (n - r)
  simpa [turanDensity, Nat.sub_add_cancel hn] using h

theorem turanDensity_le_one (F : Set (FiniteGraph r)) : turanDensity F ≤ 1 :=
  (turanDensity_le_extremalDensity F (le_refl r)).trans (extremalDensity_le_one F le_rfl)

theorem turanDensity_antitone {F H : Set (FiniteGraph r)} (h : F ⊆ H) :
    turanDensity H ≤ turanDensity F := by
  apply le_ciInf
  intro n
  exact (turanDensity_le_extremalDensity H (show r ≤ n + r by omega)).trans
    (extremalDensity_antitone h (n + r))

theorem delete_vertex_card_le (F : Set (FiniteGraph r)) {n : ℕ}
    (G : RGraph (Fin (n + 1)) r) (hG : Free F G) (v : Fin (n + 1)) :
    (G.edges.filter (fun e => v ∉ e)).card ≤ extremalNumber F n := by
  classical
  have hc : (G.pullback (Fin.succAboveEmb v)).edges.card =
      (G.edges.filter (fun e => v ∉ e)).card := by
    rw [G.pullback_edges_card]
    congr 1
    ext e
    simp only [Finset.mem_filter, Fin.succAboveEmb]
    aesop
  rw [← hc]
  exact edge_card_le_extremalNumber F _ (Free.pullback F G (Fin.succAboveEmb v) hG)

theorem extremalNumber_delete_bound (F : Set (FiniteGraph r)) (n : ℕ) :
    (n + 1 - r) * extremalNumber F (n + 1) ≤ (n + 1) * extremalNumber F n := by
  classical
  by_cases hz : extremalNumber F (n + 1) = 0
  · simp [hz]
  obtain ⟨G, hG, hc⟩ := exists_extremal_of_ne_zero F (n + 1) hz
  rw [← hc, ← G.sum_deleted_edge_counts]
  calc
    _ ≤ ∑ _v : Fin (n + 1), extremalNumber F n :=
      Finset.sum_le_sum (fun v _ => delete_vertex_card_le F G hG v)
    _ = _ := by simp

theorem extremalDensity_succ_le (F : Set (FiniteGraph r)) {n : ℕ} (hn : r ≤ n) :
    extremalDensity F (n + 1) ≤ extremalDensity F n := by
  have hp0 : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hp1 : (0 : ℝ) < (n + 1).choose r := by
    exact_mod_cast Nat.choose_pos (show r ≤ n + 1 by omega)
  have ha : (0 : ℝ) < (n + 1 - r : ℕ) := by
    exact_mod_cast (show 0 < n + 1 - r by omega)
  have hc : (n + 1 - r : ℕ) * (extremalNumber F (n + 1) : ℝ) ≤
      (n + 1 : ℕ) * (extremalNumber F n : ℝ) := by
    exact_mod_cast extremalNumber_delete_bound F n
  have hchoose : (n.choose r : ℝ) * (n + 1 : ℕ) =
      ((n + 1).choose r : ℝ) * (n + 1 - r : ℕ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n r
  have hmul := mul_le_mul_of_nonneg_right hc hp0.le
  have hchoose' := congrArg (fun x : ℝ => x * (extremalNumber F n : ℝ)) hchoose
  apply (div_le_div_iff₀ hp1 hp0).mpr
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith [hmul, hchoose']

/-- The ordinary binomial-normalized extremal sequence converges, including
the degenerate case when some forbidden graph is edgeless. -/
theorem extremalDensity_tendsto (F : Set (FiniteGraph r)) :
    Tendsto (extremalDensity F) atTop (𝓝 (turanDensity F)) := by
  have hanti : Antitone (fun n : ℕ => extremalDensity F (n + r)) :=
    antitone_nat_of_succ_le fun n => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        extremalDensity_succ_le F (show r ≤ n + r by omega)
  exact (tendsto_add_atTop_iff_nat r).mp
    (tendsto_atTop_ciInf hanti (density_range_bddBelow F))

theorem extremalNumber_eq_zero_of_edgeless (F : Set (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (he : A.2.edges = ∅)
    {n : ℕ} (hn : A.1 ≤ n) : extremalNumber F n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (extremalNumber_le_iff F n 0).mpr
  intro G hG
  exact (not_free_of_edgeless F hA he hn G hG).elim

theorem turanDensity_eq_zero_of_edgeless (F : Set (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (he : A.2.edges = ∅) : turanDensity F = 0 := by
  apply le_antisymm _ (turanDensity_nonneg F)
  calc
    turanDensity F ≤ extremalDensity F (A.1 + r) :=
      turanDensity_le_extremalDensity F (by omega)
    _ = 0 := by
      rw [extremalDensity, extremalNumber_eq_zero_of_edgeless F hA he (by omega)]
      simp

theorem turanDensity_eq_zero_of_not_nonempty (F : Set (FiniteGraph r))
    (h : ¬ ∀ A ∈ F, A.2.edges.Nonempty) : turanDensity F = 0 := by
  classical
  push Not at h
  obtain ⟨A, hA, he⟩ := h
  exact turanDensity_eq_zero_of_edgeless F hA he

end
end TuranUniversality.SetFamily
