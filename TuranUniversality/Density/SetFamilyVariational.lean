module

public import TuranUniversality.Density.SetHomomorphicClosure

@[expose] public section

/-! # Weighted variational formula for arbitrary forbidden families

The density is the ordinary extremal limit. Actual finite hom-free templates
with arbitrary real probability weights give all values in the supremum.
In the completely unrestricted statement, zero is adjoined to account for
families containing an edgeless obstruction. For families of graphs with an
edge, zero is itself realized and the paper's unmodified supremum follows.
-/

open Filter Topology

namespace TuranUniversality.SetFamily

universe u
variable {r : ℕ}

noncomputable section

def normalizedExtremalDensity (F : Set (FiniteGraph r)) (n : ℕ) : ℝ :=
  (r.factorial : ℝ) * extremalNumber F n / (n : ℝ) ^ r

theorem normalizedExtremalDensity_eq_factor (F : Set (FiniteGraph r))
    {n : ℕ} (hn : r ≤ n) :
    normalizedExtremalDensity F n = samplingFactor r n * extremalDensity F n := by
  have hc : (n.choose r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hn)
  unfold normalizedExtremalDensity samplingFactor extremalDensity
  field_simp

theorem normalizedExtremalDensity_tendsto (F : Set (FiniteGraph r)) :
    Tendsto (normalizedExtremalDensity F) atTop (𝓝 (turanDensity F)) := by
  have h := (samplingFactor_tendsto r).mul (extremalDensity_tendsto F)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  exact (normalizedExtremalDensity_eq_factor F hn).symm

theorem turanDensity_lower_of_homFree {V : Type u} [Fintype V] [DecidableEq V]
    (F : Set (FiniteGraph r)) (G : RGraph V r) (hG : HomFree F G)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ turanDensity F := by
  rw [turanDensity_eq_sInf_finite]
  apply le_csInf (finiteDensityValues_nonempty F)
  rintro z ⟨E, hE, rfl⟩
  exact familyTuranDensity_lower_of_homFree E G (hG.mono hE) x hx

theorem turanDensity_lower_uniform {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (F : Set (FiniteGraph r)) (G : RGraph V r) (hG : HomFree F G) :
    (RGraph.oneEdge r).homDensity G ≤ turanDensity F := by
  rw [G.oneEdge_homDensity_polynomial]
  exact turanDensity_lower_of_homFree F G hG _ probabilityWeights_uniform

/-- Any uniform-density bound on ordinary free hosts bounds the ordinary
limit. The nonnegative bound also covers empty feasible classes. -/
theorem turanDensity_upper_of_free (F : Set (FiniteGraph r)) (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ n (G : RGraph (Fin n) r),
      Free F G → (RGraph.oneEdge r).homDensity G ≤ c) :
    turanDensity F ≤ c := by
  apply le_of_tendsto (normalizedExtremalDensity_tendsto F)
  apply Filter.Eventually.of_forall
  intro n
  by_cases hz : extremalNumber F n = 0
  · simpa [normalizedExtremalDensity, hz] using hc
  · obtain ⟨G, hG, hcard⟩ := exists_extremal_of_ne_zero F n hz
    simpa [RGraph.oneEdge_homDensity, normalizedExtremalDensity, hcard] using hclass n G hG

/-- The upper bridge for arbitrary families follows from their actual
homomorphic closure, not from a postulated variational identity. -/
theorem turanDensity_upper_of_homFree (F : Set (FiniteGraph r)) (hr : 0 < r)
    (c : ℝ) (hc : 0 ≤ c)
    (hclass : ∀ n (G : RGraph (Fin n) r),
      HomFree F G → (RGraph.oneEdge r).homDensity G ≤ c) :
    turanDensity F ≤ c := by
  rw [← turanDensity_homomorphicClosure F hr]
  apply turanDensity_upper_of_free _ c hc
  intro n G hG
  exact hclass n G ((free_homomorphicClosure_iff F G).mp hG)

def rawWeightedValues (F : Set (FiniteGraph r)) : Set ℝ :=
  {z | ∃ (n : ℕ) (G : RGraph (Fin n) r) (x : Fin n → ℝ),
    HomFree F G ∧ ProbabilityWeights x ∧ z = (r.factorial : ℝ) * G.edgePolynomial x}

def weightedValues (F : Set (FiniteGraph r)) : Set ℝ := insert 0 (rawWeightedValues F)

theorem zero_mem_rawWeightedValues (F : Set (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) : 0 ∈ rawWeightedValues F := by
  refine ⟨1, RGraph.empty (Fin 1) r, _, homFree_emptyGraph F hedges 1,
    probabilityWeights_uniform, ?_⟩
  simp [RGraph.edgePolynomial, RGraph.empty]

theorem weightedValues_eq_raw (F : Set (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) : weightedValues F = rawWeightedValues F :=
  Set.insert_eq_of_mem (zero_mem_rawWeightedValues F hedges)

theorem weightedValues_bddAbove (F : Set (FiniteGraph r)) :
    BddAbove (weightedValues F) := by
  refine ⟨turanDensity F, ?_⟩
  rintro z (rfl | ⟨n, G, x, hG, hx, rfl⟩)
  · exact turanDensity_nonneg F
  · exact turanDensity_lower_of_homFree F G hG x hx

/-- Unconditional variational identity, with zero explicitly included when
there are no hom-free probability-weighted templates. -/
theorem turanDensity_eq_sSup_weighted (F : Set (FiniteGraph r)) (hr : 0 < r) :
    turanDensity F = sSup (weightedValues F) := by
  have hzero : 0 ∈ weightedValues F := Set.mem_insert 0 _
  have hbdd := weightedValues_bddAbove F
  have hnonneg : 0 ≤ sSup (weightedValues F) := le_csSup hbdd hzero
  apply le_antisymm
  · apply turanDensity_upper_of_homFree F hr _ hnonneg
    intro n G hG
    by_cases hn : n = 0
    · subst n
      simpa [RGraph.oneEdge_homDensity, zero_pow (Nat.ne_of_gt hr)] using hnonneg
    · let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      rw [G.oneEdge_homDensity_polynomial]
      apply le_csSup hbdd
      exact Set.mem_insert_of_mem _ ⟨n, G, _, hG, probabilityWeights_uniform, rfl⟩
  · apply csSup_le ⟨0, hzero⟩
    rintro z (rfl | ⟨n, G, x, hG, hx, rfl⟩)
    · exact turanDensity_nonneg F
    · exact turanDensity_lower_of_homFree F G hG x hx

/-- The exact supremum stated in Lemma 2.2 for families of graphs having an
edge: every member of the supremum is an actual finite hom-free template. -/
theorem turanDensity_eq_sSup_rawWeighted (F : Set (FiniteGraph r)) (hr : 0 < r)
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    turanDensity F = sSup (rawWeightedValues F) := by
  rw [← weightedValues_eq_raw F hedges]
  exact turanDensity_eq_sSup_weighted F hr

end
end TuranUniversality.SetFamily
