module

public import TuranUniversality.Structural.OrdinaryStability
public import TuranUniversality.Structural.CanonicalClassification
public import TuranUniversality.Structural.ExtremalProfileSequences
public import TuranUniversality.Density.WeightedHomDeletion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Ordinary extremal profiles transfer to actual canonical profiles

An ordinary extremal point is realized by positive-order finite free
graphs with orders tending to infinity. The finite Ψ theorem, once its
one-vertex extension input is available, deletes a vanishing proportion
of low-degree vertices. Independent sampling proves that every profile
coordinate is preserved by this deletion and normalization.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Stability Density

variable {b t : ℕ}

theorem extremal_subset_canonical (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{0} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N) :
    SetFamily.extremalProfiles (forbidden F Ω t) ⊆ CanonicalProfiles.extremal F Ω t p q := by
  classical
  intro W hW
  obtain ⟨G, hpos, hG, hsize, hprof, hedge⟩ :=
    SetFamily.exists_extremal_homFree_sequence (forbidden F Ω t) W hW
  have hfac : ((t + (3 * b + 4)).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hval : Tendsto (fun n => ((G n).2.edges.card : ℝ) /
      (Fintype.card (Fin (G n).1) : ℝ) ^ (t + (3 * b + 4))) atTop
      (𝓝 (optimum F b t p q)) := by
    dsimp only [optimum]
    have h := hedge.div_const ((t + (3 * b + 4)).factorial : ℝ)
    rw [density_eq F hedges Ω hdis t p q hp hpq hq hz hΩ,
      mul_div_cancel_left₀ _ hfac] at h
    convert h using 1
    funext n
    rw [RGraph.oneEdge_homDensity, div_right_comm, mul_div_cancel_left₀ _ hfac]
  obtain ⟨δ, _, hsmall, hcan⟩ := eventually_canonical_induced F hedges Ω hdis t
    p q hp hpq hq hz hΩ hext (fun n => (G n).2)
    (fun n => familyHomFree_free _ _ (hG n))
    (by simpa only [Fintype.card_fin] using hpos) atTop
    (by simpa only [Fintype.card_fin] using hsize) hval
  let S n := goodVertices (G n).2 (optimum F b t p q) δ
  have hcomp n : Finset.univ \ S n = (G n).2.lowDegreeSet (optimum F b t p q) δ :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
  have hprofS : Tendsto (fun n => SetFamily.weightedProfile ((G n).2.induced (S n))
      (fun _ => (Fintype.card (S n) : ℝ)⁻¹)) atTop (𝓝 W) := by
    apply tendsto_pi_nhds.mpr
    intro A
    have hd := A.2.homDensity_induced_sub_tendsto_zero (fun n => (G n).2)
      (by simpa only [Fintype.card_fin] using hpos) S atTop
      (by simpa only [hcomp] using hsmall)
    have hc := ((tendsto_pi_nhds.mp hprof) A).sub hd
    simpa only [SetFamily.profile, SetFamily.weightedProfile,
      RGraph.weightedHomDensity_uniform, sub_sub_cancel, sub_zero] using hc
  refine ⟨?_, ?_⟩
  · apply isClosed_closure.mem_of_tendsto hprofS
    filter_upwards [hcan] with n hn
    apply subset_closure
    have hn0 : (0 : ℝ) < Fintype.card (S n) := by
      exact_mod_cast (show 0 < Fintype.card (S n) by simpa only [Fintype.card_coe] using hn.1)
    exact CanonicalProfiles.weightedProfile_mem F Ω ((G n).2.induced (S n)) hn.2
      (fun _ => (Fintype.card (S n) : ℝ)⁻¹)
      ⟨fun _ => inv_nonneg.mpr hn0.le, by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        exact mul_inv_cancel₀ (ne_of_gt hn0)⟩
  · exact hW.2.trans (density_eq F hedges Ω hdis t p q hp hpq hq hz hΩ)

/-- Equality with the ordinary extremal space, conditional solely on the
explicit finite one-vertex extension theorem. -/
theorem extremal_eq_canonical (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{0} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N) :
    SetFamily.extremalProfiles (forbidden F Ω t) = CanonicalProfiles.extremal F Ω t p q :=
  Set.Subset.antisymm (extremal_subset_canonical F hedges Ω hdis t p q hp hpq hq hz hΩ hext)
    (CanonicalProfiles.subset_ordinary F hedges Ω hdis p q hp hpq hq hz hΩ)

theorem positive_profile_classification (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q < familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{0} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N) :
    SetFamily.extremalProfiles (forbidden F Ω t) =
      (PhaseRoles.extremalPhaseMap (t := t) Ω false p q (familyTuranDensity F) ''
        SetFamily.extremalProfiles F) ∪
      (PhaseRoles.extremalPhaseMap (t := t) Ω true p q (familyTuranDensity F) ''
        SetFamily.extremalProfiles F) := by
  rw [extremal_eq_canonical F hedges Ω hdis t p q hp hpq hq hz.le hΩ hext]
  exact CanonicalProfiles.positive_classification F hedges Ω p q hp hpq hq hz hΩ

theorem zero_profile_classification (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : familyTuranDensity F = p / q)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{0} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N) :
    SetFamily.extremalProfiles (forbidden F Ω t) = {NeutralRoles.neutralProfile Ω t} := by
  rw [extremal_eq_canonical F hedges Ω hdis t p q hp hpq hq hz.ge hΩ hext]
  exact CanonicalProfiles.zero_classification F hedges Ω p q hp hpq hq hz hΩ

end TuranUniversality.Structural.Ordinary
