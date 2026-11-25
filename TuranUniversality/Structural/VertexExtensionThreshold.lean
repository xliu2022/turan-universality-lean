module

public import TuranUniversality.Structural.VertexExtensionInduced
public import TuranUniversality.Structural.OrdinaryStability
public import TuranUniversality.Stability.OneVertexDegree

@[expose] public section

/-! # From uniform common-frame thresholds to vertex extendability

This finite implication isolates the common-frame sampling input. It
shrinks the degree tolerance explicitly, absorbs the deletion of one
vertex, and applies the small actual forbidden-subgraph contradiction.
-/

namespace TuranUniversality.Structural.Roles

open Rooted Stability

universe u

def UniformReplacementFrames (F : Finset (FiniteGraph 3)) (p q : ℕ)
    (hpq : p ≤ q) (t K : ℕ) (d : ℝ) (N : ℕ) : Prop :=
  ∀ {V : Type u} [DecidableEq V] [Fintype V]
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (ρ : V → Option (Roots (CodePools.blockCount q) t)),
    Admissible (homomorphicClosure F) (CodePools.pool p q hpq) G ρ →
    N ≤ Fintype.card V → MinimumDegree G d →
    ∀ S : Finset V, S.card ≤ K → HasReplacementFrame p q hpq G ρ S

theorem vertexExtendable_of_uniform_frames
    (F : Finset (FiniteGraph 3)) (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (d : ℝ) (hd : 0 < d)
    (hframes : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      UniformReplacementFrames.{u} F p q hpq t
        (replacementSupportBound (homomorphicClosure F) (CodePools.blockCount q) t)
        (d - ε) N) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (Ordinary.freeClass.{u} F (CodePools.pool p q hpq) t)
        (Ordinary.canonicalClass F (CodePools.pool p q hpq) t) (d - ζ) N := by
  classical
  obtain ⟨ε, hε, Nf, hframes⟩ := hframes
  let δ : ℝ := min ε (d / 2)
  have hδ : 0 < δ := lt_min hε (half_pos hd)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδd : δ ≤ d / 2 := min_le_right _ _
  have hdδ : 0 < d - δ := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / δ)
  let N := max (Nf + 1) (k + 2)
  refine ⟨δ / 2, half_pos hδ, N, ?_⟩
  intro V _ _ G hG hN hmin v hcan
  have hn : 2 ≤ Fintype.card V := by
    have h := (le_max_right _ _).trans hN
    omega
  have hNf : Nf ≤ Fintype.card ↥(Finset.univ.erase v : Finset V) := by
    have h := (le_max_left _ _).trans hN
    simp only [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ]
    omega
  have hscale : 1 ≤ (δ / 2) * Fintype.card V := by
    have hkN : k ≤ Fintype.card V := by
      have h := (le_max_right _ _).trans hN
      omega
    have hkNR : (k : ℝ) ≤ Fintype.card V := by exact_mod_cast hkN
    have hkδ := (div_lt_iff₀ hδ).mp hk
    have hmul := mul_le_mul_of_nonneg_right hkNR hδ.le
    nlinarith
  have hminOld : MinimumDegree (G.induced (Finset.univ.erase v)) (d - δ) := by
    have h := hmin.induced_erase (by omega) (by linarith : 0 ≤ d - δ / 2 - δ / 2)
      hscale v
    convert h using 1 <;> ring
  have hnonempty : Nonempty ↥(Finset.univ.erase v : Finset V) :=
    Fintype.card_pos_iff.mp (by
      simp only [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
        Finset.card_univ]
      omega)
  obtain ⟨z⟩ := hnonempty
  obtain ⟨ρ, hρ⟩ := (canonical_iff (homomorphicClosure F) (CodePools.pool p q hpq)
    (fun _ _ h => CodePools.pools_disjoint p q hpq h) _).mp hcan
  apply canonical_of_induced_frames F p q hpq hq G v z ρ hρ hG
    (incident_edge_of_minimumDegree hdδ hminOld)
  exact hframes _ ρ hρ hNf (hminOld.mono (by linarith))

end TuranUniversality.Structural.Roles
