module

public import TuranUniversality.Structural.FrameThreshold
public import TuranUniversality.Structural.CommonFrameSequence
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Vertex extendability and degree stability of the actual ordinary family

All common-frame inputs are discharged by genuine sampling. The only
assumptions are the original finite inner forbidden family and rational
threshold conditions of the structural construction.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Rooted Roles Stability

universe u

theorem uniform_replacementFrames
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t K : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      UniformReplacementFrames.{u} F p q hpq t K
        (((t + (3 * CodePools.blockCount q + 4) : ℕ) : ℝ) *
          optimum F (CodePools.blockCount q) t p q - ε) N := by
  classical
  apply uniformReplacementFrames_of_sequences
  intro X _ _ G ρ S hρ hsize hmin hS
  have hn n : 0 < Fintype.card (X n) := by have h := hsize n; omega
  let x n (_ : X n) : ℝ := (Fintype.card (X n) : ℝ)⁻¹
  have hx n : ProbabilityWeights (x n) := by
    have hn' : (0 : ℝ) < Fintype.card (X n) := by exact_mod_cast hn n
    exact ⟨fun _ => inv_nonneg.mpr hn'.le, by simp [x, ne_of_gt hn']⟩
  choose R _hrecord hR hh using (fun n => extract_records (homomorphicClosure F)
    (CodePools.pool p q hpq) (fun _ _ h => CodePools.pools_disjoint p q hpq h)
    (G n) (ρ n) (hρ n))
  have hcan n : Canonical (homomorphicClosure F) (CodePools.pool p q hpq) (G n) :=
    ⟨ρ n, R n, hR n, hh n⟩
  have hbound n : (G n).edgePolynomial (x n) ≤ optimum F (CodePools.blockCount q) t p q :=
    Canonical.polynomial_upper F hedges (CodePools.pool p q hpq) (G n) (hcan n)
      p q (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
      (CodePools.pool_card_cast p q hpq hq) (x n) (hx n)
  have heps : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpoly := polynomial_tendsto_of_minimumDegree G (by omega) hn hbound atTop
    (fun n => ((n : ℝ) + 1)⁻¹) heps hmin
  have hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v,
      (((t + (3 * CodePools.blockCount q + 4) : ℕ) : ℝ) *
          optimum F (CodePools.blockCount q) t p q) - ε ≤
        (G n).linkPolynomial (x n) v := by
    intro ε hε
    have he := (tendsto_order.mp heps).2 ε hε
    filter_upwards [he] with n hnε v
    exact (sub_le_sub_left hnε.le _).trans ((hmin n).uniform_link_lower (hn n) v)
  have h := eventually_replacementFrames F hedges p q hpq hq t hz G ρ R hR hh
    x hx hpoly hlower K
  filter_upwards [h] with n hn
  exact hn (S n) (hS n)

/-- The actual Section 9 vertex-extension conclusion, with every frame
and rigidity hypothesis discharged. -/
theorem vertex_extendable
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{u} F (CodePools.pool p q hpq) t)
        (canonicalClass F (CodePools.pool p q hpq) t)
        (((t + (3 * CodePools.blockCount q + 4) : ℕ) : ℝ) *
          optimum F (CodePools.blockCount q) t p q - ζ) N := by
  apply vertexExtendable_of_uniform_frames F p q hpq hq t
  · exact mul_pos (by positivity) (optimum_pos F _ t p q (Nat.cast_pos.mpr hq) hz)
  · exact uniform_replacementFrames F hedges p q hpq hq t
      (replacementSupportBound (homomorphicClosure F) (CodePools.blockCount q) t) hz

/-- Genuine degree stability for the actual finite ordinary forbidden
family, using the proved finite Psi theorem and proved vertex extension. -/
theorem degree_stable_actual
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F) :
    DegreeStable (freeClass.{u} F (CodePools.pool p q hpq) t)
      (canonicalClass F (CodePools.pool p q hpq) t)
      (optimum F (CodePools.blockCount q) t p q) := by
  exact degree_stable F hedges (CodePools.pool p q hpq)
    (fun _ _ h => CodePools.pools_disjoint p q hpq h) t p q
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) (vertex_extendable F hedges p q hpq hq t hz)

end TuranUniversality.Structural.Ordinary
