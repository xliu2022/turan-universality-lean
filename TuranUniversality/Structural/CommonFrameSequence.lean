module

public import TuranUniversality.Structural.CommonFrameSampling
public import TuranUniversality.Structural.FrameDensity
public import TuranUniversality.Density.LinkDefects

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Common replacement frames in high minimum-link canonical sequences

The role presentation is the specified actual presentation of each graph.
The same eventual index works for every set of at most `K` vertices. Real
probability weights are allowed; uniform weights give the ordinary minimum
degree statement used for vertex extension.
-/

open Filter Topology

namespace TuranUniversality.Structural.Roles

open Rooted

variable {X : ℕ → Type*} [∀ n, DecidableEq (X n)] [∀ n, Fintype (X n)]

theorem eventually_replacementFrames
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    (G : ∀ n, RGraph (X n) (t + (3 * CodePools.blockCount q + 4)))
    (ρ : ∀ n, X n → Option (Roots (CodePools.blockCount q) t))
    (R : ∀ n, RecordSystem (X n))
    (hR : ∀ n, (R n).LocallyLegal (homomorphicClosure F))
    (hh : ∀ n, (G n).IsHom (Compiled.graph t (CodePools.pool p q hpq) (R n)) (place (ρ n)))
    (x : ∀ n, X n → ℝ) (hx : ∀ n, ProbabilityWeights (x n))
    (hpoly : Tendsto (fun n => (G n).edgePolynomial (x n)) atTop
      (𝓝 (OuterWeights.chi (CodePools.blockCount q) t *
        SwitchScalar.phaseScore p q (familyTuranDensity F))))
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v,
      ((t + (3 * CodePools.blockCount q + 4) : ℕ) : ℝ) *
          (OuterWeights.chi (CodePools.blockCount q) t *
            SwitchScalar.phaseScore p q (familyTuranDensity F)) - ε ≤
        (G n).linkPolynomial (x n) v)
    (K : ℕ) :
    ∀ᶠ n in atTop, ∀ S : Finset (X n), S.card ≤ K →
      HasReplacementFrame p q hpq (G n) (ρ n) S := by
  let H n := (Compiled.graph t (CodePools.pool p q hpq) (R n)).inverseImage (place (ρ n))
  have hsub n : (G n).edges ⊆ (H n).edges := by
    intro e he
    exact (RGraph.mem_inverseImage _ _ _).mpr ⟨(G n).uniform e he, hh n e he⟩
  have hCan n : Canonical (homomorphicClosure F) (CodePools.pool p q hpq) (G n) :=
    ⟨ρ n, R n, hR n, hh n⟩
  have hCanH n : Canonical (homomorphicClosure F) (CodePools.pool p q hpq) (H n) :=
    Canonical.of_hom F (CodePools.pool p q hpq)
      ((Compiled.graph t (CodePools.pool p q hpq) (R n)).inverseImage_projection (place (ρ n)))
      (Compiled.canonical (homomorphicClosure F) (CodePools.pool p q hpq) (R n) (hR n))
  let Λ := OuterWeights.chi (CodePools.blockCount q) t * SwitchScalar.phaseScore p q (familyTuranDensity F)
  have hbound n y (hy : ProbabilityWeights y) : (H n).edgePolynomial y ≤ Λ :=
    Canonical.polynomial_upper F hedges (CodePools.pool p q hpq) (H n) (hCanH n) p q
      (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
      (CodePools.pool_card_cast p q hpq hq) y hy
  let J := Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)
  let A : ℝ := (K : ℝ) * Fintype.card (Compiled.Vertex (CodePools.blockCount q) t (Fin 5)) *
    J.edges.card * (t + (3 * CodePools.blockCount q + 4) - 1).factorial
  let c := FrameDensity.limitValue q t (familyTuranDensity F - (p : ℝ) / q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 < c := FrameDensity.limitValue_pos q t _ (sub_nonneg.mpr hz)
  let ε := c / (4 * (A + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : A * ε < c / 2 := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show 0 < 4 * (A + 1) by positivity)).mpr
    nlinarith [mul_nonneg hA hc.le]
  have hmiss := Density.eventually_uniform_missing_link_bound G H hsub x hx hbound hpoly hlower hε
  have hframe := FrameDensity.eventually_frame_density_lower F hedges p q hpq hq t hz G hCan x hx atTop hpoly
  filter_upwards [hmiss, hframe] with n hn hfn S hS
  apply hasReplacementFrame_of_link_bounds p q hpq hq (G n) (ρ n) (R n) (hh n) S (x n) (hx n) ε
  · intro y _hy
    exact hn y
  · have hcoef : (S.card : ℝ) * Fintype.card (Compiled.Vertex (CodePools.blockCount q) t (Fin 5)) *
          J.edges.card * (t + (3 * CodePools.blockCount q + 4) - 1).factorial * ε ≤ A * ε := by
      dsimp [A]
      gcongr
    exact hcoef.trans_lt (hsmall.trans hfn)

end TuranUniversality.Structural.Roles
