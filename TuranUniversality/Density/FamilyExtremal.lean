module

public import TuranUniversality.Density.FamilyBasic

@[expose] public section

/-! # Ordinary extremal numbers and Turán density of finite forbidden families -/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality

noncomputable section

/-- The largest edge count of an actual ordinary family-free graph. -/
def familyExtremalNumber {r : ℕ} (F : Finset (FiniteGraph r)) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ∃ G : RGraph (Fin n) r,
    familyFree F G ∧ G.edges.card = m) (n.choose r)

def familyExtremalDensity {r : ℕ} (F : Finset (FiniteGraph r)) (n : ℕ) : ℝ :=
  (familyExtremalNumber F n : ℝ) / (n.choose r : ℝ)

/-- The infimum of ordinary binomial-normalized extremal numbers for n ≥ r.
The limit theorem below identifies this with their ordinary limit. -/
def familyTuranDensity {r : ℕ} (F : Finset (FiniteGraph r)) : ℝ :=
  ⨅ n : ℕ, familyExtremalDensity F (n + r)

variable {r : ℕ}

theorem edge_card_le_familyExtremalNumber (F : Finset (FiniteGraph r))
    {n : ℕ} (G : RGraph (Fin n) r) (hfree : familyFree F G) :
    G.edges.card ≤ familyExtremalNumber F n := by
  classical
  exact Nat.le_findGreatest G.edge_card_le_choose ⟨G, hfree, rfl⟩

theorem exists_family_extremal (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    ∃ G : RGraph (Fin n) r, familyFree F G ∧
      G.edges.card = familyExtremalNumber F n := by
  classical
  unfold familyExtremalNumber
  exact Nat.findGreatest_spec
    (P := fun m => ∃ G : RGraph (Fin n) r, familyFree F G ∧ G.edges.card = m)
    (Nat.zero_le (n.choose r))
    ⟨RGraph.empty (Fin n) r, familyFree_empty F hedges n, rfl⟩

theorem familyExtremalNumber_le_choose (F : Finset (FiniteGraph r)) (n : ℕ) :
    familyExtremalNumber F n ≤ n.choose r := by
  classical
  exact Nat.findGreatest_le _

theorem familyExtremalDensity_nonneg (F : Finset (FiniteGraph r)) (n : ℕ) :
    0 ≤ familyExtremalDensity F n := by
  unfold familyExtremalDensity
  positivity

theorem familyExtremalDensity_le_one (F : Finset (FiniteGraph r))
    {n : ℕ} (hn : r ≤ n) : familyExtremalDensity F n ≤ 1 := by
  have hp : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  apply (div_le_iff₀ hp).mpr
  simpa using (Nat.cast_le.mpr (familyExtremalNumber_le_choose F n) :
    (familyExtremalNumber F n : ℝ) ≤ n.choose r)

theorem familyTuranDensity_nonneg (F : Finset (FiniteGraph r)) :
    0 ≤ familyTuranDensity F :=
  le_ciInf fun n => familyExtremalDensity_nonneg F (n + r)

theorem familyTuranDensity_le_extremalDensity (F : Finset (FiniteGraph r))
    {n : ℕ} (hn : r ≤ n) : familyTuranDensity F ≤ familyExtremalDensity F n := by
  have hbdd : BddBelow (Set.range (fun n : ℕ => familyExtremalDensity F (n + r))) :=
    ⟨0, by rintro _ ⟨m, rfl⟩; exact familyExtremalDensity_nonneg F _⟩
  have h := ciInf_le hbdd (n - r)
  simpa [familyTuranDensity, Nat.sub_add_cancel hn] using h

theorem familyTuranDensity_le_one (F : Finset (FiniteGraph r)) :
    familyTuranDensity F ≤ 1 :=
  (familyTuranDensity_le_extremalDensity F (le_refl r)).trans
    (familyExtremalDensity_le_one F (le_refl r))

theorem family_delete_vertex_card_le (F : Finset (FiniteGraph r)) {n : ℕ}
    (G : RGraph (Fin (n + 1)) r) (hfree : familyFree F G) (v : Fin (n + 1)) :
    (G.edges.filter (fun e => v ∉ e)).card ≤ familyExtremalNumber F n := by
  classical
  have hcard : (G.pullback (Fin.succAboveEmb v)).edges.card =
      (G.edges.filter (fun e => v ∉ e)).card := by
    rw [G.pullback_edges_card]
    congr 1
    ext e
    simp only [Finset.mem_filter, Fin.succAboveEmb]
    aesop
  rw [← hcard]
  exact edge_card_le_familyExtremalNumber F _
    (familyFree_pullback F G (Fin.succAboveEmb v) hfree)

theorem familyExtremalNumber_delete_bound (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    (n + 1 - r) * familyExtremalNumber F (n + 1) ≤
      (n + 1) * familyExtremalNumber F n := by
  classical
  obtain ⟨G, hfree, hcard⟩ := exists_family_extremal F hedges (n + 1)
  rw [← hcard, ← G.sum_deleted_edge_counts]
  calc
    _ ≤ ∑ _v : Fin (n + 1), familyExtremalNumber F n :=
      Finset.sum_le_sum (fun v _ => family_delete_vertex_card_le F G hfree v)
    _ = _ := by simp

theorem familyExtremalDensity_succ_le (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) {n : ℕ} (hn : r ≤ n) :
    familyExtremalDensity F (n + 1) ≤ familyExtremalDensity F n := by
  have hp0 : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hp1 : (0 : ℝ) < (n + 1).choose r := by
    exact_mod_cast Nat.choose_pos (show r ≤ n + 1 by omega)
  have ha : (0 : ℝ) < (n + 1 - r : ℕ) := by
    exact_mod_cast (show 0 < n + 1 - r by omega)
  have hc : (n + 1 - r : ℕ) * (familyExtremalNumber F (n + 1) : ℝ) ≤
      (n + 1 : ℕ) * (familyExtremalNumber F n : ℝ) := by
    exact_mod_cast familyExtremalNumber_delete_bound F hedges n
  have hchoose : (n.choose r : ℝ) * (n + 1 : ℕ) =
      ((n + 1).choose r : ℝ) * (n + 1 - r : ℕ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n r
  have hmul := mul_le_mul_of_nonneg_right hc hp0.le
  have hchoose' := congrArg (fun x : ℝ => x * (familyExtremalNumber F n : ℝ)) hchoose
  apply (div_le_div_iff₀ hp1 hp0).mpr
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith [hmul, hchoose']

/-- The usual Katona--Nemetz--Simonovits limit for a finite forbidden family.
An empty forbidden family is also allowed. -/
theorem familyExtremalDensity_tendsto (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    Tendsto (familyExtremalDensity F) atTop (𝓝 (familyTuranDensity F)) := by
  have hanti : Antitone (fun n : ℕ => familyExtremalDensity F (n + r)) :=
    antitone_nat_of_succ_le fun n => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        familyExtremalDensity_succ_le F hedges (show r ≤ n + r by omega)
  have hbdd : BddBelow (Set.range (fun n : ℕ => familyExtremalDensity F (n + r))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact familyExtremalDensity_nonneg F _⟩
  exact (tendsto_add_atTop_iff_nat r).mp (tendsto_atTop_ciInf hanti hbdd)

@[simp] theorem familyExtremalNumber_singleton (A : FiniteGraph r) (n : ℕ) :
    familyExtremalNumber {A} n = extremalNumber A.2 n := by
  simp [familyExtremalNumber, extremalNumber]

@[simp] theorem familyExtremalDensity_singleton (A : FiniteGraph r) (n : ℕ) :
    familyExtremalDensity {A} n = extremalDensity A.2 n := by
  simp [familyExtremalDensity, extremalDensity]

@[simp] theorem familyTuranDensity_singleton (A : FiniteGraph r) :
    familyTuranDensity {A} = turanDensity A.2 := by
  simp [familyTuranDensity, turanDensity]

end
end TuranUniversality
