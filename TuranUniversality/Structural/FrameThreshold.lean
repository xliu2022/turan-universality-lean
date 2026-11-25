module

public import TuranUniversality.Structural.VertexExtensionThreshold
public import TuranUniversality.Stability.MinimumDegreeConvergence

@[expose] public section

/-! # Extracting a uniform common-frame threshold from sequential sampling

Failure of every tolerance and order threshold gives actual finite
counterexamples of order at least n+1 and minimum degree within 1/(n+1)
of the limiting threshold. An eventual sampling theorem rules these out.
-/

open Filter Topology

namespace TuranUniversality.Structural.Roles

open Rooted Stability

universe u

theorem uniformReplacementFrames_of_sequences
    (F : Finset (FiniteGraph 3)) (p q : ℕ) (hpq : p ≤ q) (t K : ℕ) (d : ℝ)
    (hseq : ∀ {X : ℕ → Type u} [∀ n, DecidableEq (X n)] [∀ n, Fintype (X n)]
      (G : ∀ n, RGraph (X n) (t + (3 * CodePools.blockCount q + 4)))
      (ρ : ∀ n, X n → Option (Roots (CodePools.blockCount q) t))
      (S : ∀ n, Finset (X n)),
      (∀ n, Admissible (homomorphicClosure F) (CodePools.pool p q hpq) (G n) (ρ n)) →
      (∀ n, n + 1 ≤ Fintype.card (X n)) →
      (∀ n, MinimumDegree (G n) (d - ((n : ℝ) + 1)⁻¹)) →
      (∀ n, (S n).card ≤ K) →
      ∀ᶠ n in atTop, HasReplacementFrame p q hpq (G n) (ρ n) (S n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, UniformReplacementFrames.{u} F p q hpq t K (d - ε) N := by
  classical
  by_contra h
  simp only [UniformReplacementFrames] at h
  push_neg at h
  have hcounter (n : ℕ) := h (((n : ℝ) + 1)⁻¹) (by positivity) (n + 1)
  choose X decX finX G ρ hρ hsize hmin S hS hbad using hcounter
  letI : ∀ n, DecidableEq (X n) := decX
  letI : ∀ n, Fintype (X n) := finX
  obtain ⟨n, hn⟩ := (hseq G ρ S hρ hsize hmin hS).exists
  exact hbad n hn

end TuranUniversality.Structural.Roles
