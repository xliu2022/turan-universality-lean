module

public import TuranUniversality.Density.FamilyLower
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Ordinary finite-family density upper bounds in every uniformity

These bounds use ordinary family-free extremal graphs. They do not require
a finite-family homomorphism-density supremum identity.
-/

open Filter Topology

namespace TuranUniversality

theorem samplingFactor_descFactorial (r n : ℕ) :
    samplingFactor r n = (n.descFactorial r : ℝ) / (n : ℝ) ^ r := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp [samplingFactor]

theorem samplingFactor_succ {r n : ℕ} (hr : r ≤ n) (hn : n ≠ 0) :
    samplingFactor (r + 1) n = samplingFactor r n * (1 - (r : ℝ) / (n : ℝ)) := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [samplingFactor_descFactorial, Nat.descFactorial_succ, Nat.cast_mul,
    Nat.cast_sub hr, pow_succ]
  field_simp

/-- The binomial and ordered-edge normalizations are asymptotically equal
for every fixed uniformity. -/
theorem samplingFactor_tendsto (r : ℕ) :
    Tendsto (samplingFactor r) atTop (𝓝 1) := by
  induction r with
  | zero =>
    have heq : samplingFactor 0 = (fun _n : ℕ => (1 : ℝ)) := by
      funext n
      simp [samplingFactor]
    rw [heq]
    exact tendsto_const_nhds
  | succ r ih =>
    have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlim : Tendsto
        (fun n : ℕ => samplingFactor r n * (1 - (r : ℝ) * (n : ℝ)⁻¹))
        atTop (𝓝 1) := by
      simpa using ih.mul (hone.sub (hz.const_mul (r : ℝ)))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (r + 1)] with n hn
    simpa [div_eq_mul_inv] using
      (samplingFactor_succ (show r ≤ n by omega) (show n ≠ 0 by omega)).symm

/-- An actual ordinary family-free extremal graph on a nonempty vertex set. -/
noncomputable def familyExtremalHost {r : ℕ} (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) : RGraph (Fin (n + 1)) r :=
  Classical.choose (exists_family_extremal F hedges (n + 1))

theorem familyExtremalHost_free {r : ℕ} (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    familyFree F (familyExtremalHost F hedges n) :=
  (Classical.choose_spec (exists_family_extremal F hedges (n + 1))).1

theorem familyExtremalHost_card {r : ℕ} (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (n : ℕ) :
    (familyExtremalHost F hedges n).edges.card = familyExtremalNumber F (n + 1) :=
  (Classical.choose_spec (exists_family_extremal F hedges (n + 1))).2

theorem familyExtremalHost_edgeDensity_tendsto {r : ℕ} (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    Tendsto (fun n => (RGraph.oneEdge r).homDensity (familyExtremalHost F hedges n))
      atTop (𝓝 (familyTuranDensity F)) := by
  have ha : Tendsto (fun n => samplingFactor r (n + 1)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr (samplingFactor_tendsto r)
  have hb : Tendsto (fun n => familyExtremalDensity F (n + 1))
      atTop (𝓝 (familyTuranDensity F)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (familyExtremalDensity_tendsto F hedges)
  have h := ha.mul hb
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  rw [RGraph.oneEdge_homDensity, familyExtremalHost_card]
  unfold samplingFactor familyExtremalDensity
  have hc : ((n + 1).choose r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (show r ≤ n + 1 by omega))
  simp only [Fintype.card_fin]
  field_simp

/-- A common uniform-density bound for ordinary family-free graphs bounds
their ordinary Turán density. -/
theorem familyTuranDensity_upper_of_free {r : ℕ} (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (c : ℝ)
    (hclass : ∀ n (G : RGraph (Fin n) r),
      familyFree F G → (RGraph.oneEdge r).homDensity G ≤ c) :
    familyTuranDensity F ≤ c := by
  apply le_of_tendsto (familyExtremalHost_edgeDensity_tendsto F hedges)
  exact Filter.Eventually.of_forall fun n =>
    hclass (n + 1) (familyExtremalHost F hedges n) (familyExtremalHost_free F hedges n)

/-- A pointwise weighted bound on every ordinary family-free graph implies
the desired ordinary Turán upper bound. No hom-free upper bridge is assumed. -/
theorem familyTuranDensity_upper_of_weighted_free {r : ℕ}
    (F : Finset (FiniteGraph r)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (c : ℝ)
    (hclass : ∀ n (G : RGraph (Fin n) r) (x : Fin n → ℝ),
      familyFree F G → ProbabilityWeights x → (r.factorial : ℝ) * G.edgePolynomial x ≤ c) :
    familyTuranDensity F ≤ c := by
  apply le_of_tendsto (familyExtremalHost_edgeDensity_tendsto F hedges)
  apply Filter.Eventually.of_forall
  intro n
  rw [RGraph.oneEdge_homDensity_polynomial]
  exact hclass (n + 1) (familyExtremalHost F hedges n) _
    (familyExtremalHost_free F hedges n) probabilityWeights_uniform

end TuranUniversality
