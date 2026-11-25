module

public import TuranUniversality.Structural.OrdinaryTransfer
public import TuranUniversality.Structural.CanonicalEditCompletion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual compiled presentations approximating every ordinary near-extremal sequence

This theorem exposes the root-role map and locally legal record system on
the original carrier. Completing the root supports is an `o(n^r)` edit,
and the completed quotient is near optimal with its actual fiber weights.
Record repair and exact class-size rounding can therefore be applied to
these concrete presentations.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Density

universe u v

theorem completed_edit_approximation_actual
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * CodePools.blockCount q + 4)))
    (hG : ∀ i, familyFree (forbidden F (CodePools.pool p q hpq) t) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l
      (𝓝 (optimum F (CodePools.blockCount q) t p q))) :
    ∃ (ρ : ∀ i, V i → Option (Rooted.Roots (CodePools.blockCount q) t))
      (R : ∀ i, RecordSystem (V i)),
      (∀ i, (R i).LocallyLegal (homomorphicClosure F)) ∧
      let Ω := CodePools.pool p q hpq
      let y i := pushforwardWeight (Rooted.place (ρ i))
        (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹)
      let K i := (Compiled.graph t Ω (R i)).inverseImage (Rooted.place (ρ i))
      (∀ i, ProbabilityWeights (y i)) ∧
      Tendsto (fun i => (G i).normalizedEditDistance (K i)) l (𝓝 0) ∧
      Tendsto (fun i => (Compiled.graph t Ω (R i)).edgePolynomial (y i)) l
        (𝓝 (optimum F (CodePools.blockCount q) t p q)) ∧
      ∀ i n (A : RGraph (Fin n) (t + (3 * CodePools.blockCount q + 4))),
        A.homDensity (K i) = A.weightedHomDensity (Compiled.graph t Ω (R i)) (y i) := by
  classical
  let Ω := CodePools.pool p q hpq
  obtain ⟨H, _, hGH, hHlim, hH⟩ := near_extremal_edit_approximation_actual F hedges
    p q hpq hq t hz G hG hn l hsize hlim
  let J i := if Canonical (homomorphicClosure F) Ω (H i) then H i
    else RGraph.empty (V i) (t + (3 * CodePools.blockCount q + 4))
  have hJ i : Canonical (homomorphicClosure F) Ω (J i) := by
    dsimp only [J]
    split_ifs with h
    · exact h
    · let O := LegalObject.empty (homomorphicClosure F) (homomorphicClosure_has_edges F hedges)
        (∅ : Finset (V i))
      refine ⟨fun _ => none, O.records, O.records_locallyLegal, ?_⟩
      intro e he
      simpa only [RGraph.empty, Finset.notMem_empty] using he
  have hJeq : ∀ᶠ i in l, J i = H i := hH.mono (fun i hi => if_pos hi)
  have hJlim : Tendsto (fun i => ((J i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * CodePools.blockCount q + 4))) l
      (𝓝 (optimum F (CodePools.blockCount q) t p q)) :=
    hHlim.congr' (hJeq.mono (fun i hi =>
      congrArg (fun K : RGraph (V i) (t + (3 * CodePools.blockCount q + 4)) =>
        (K.edges.card : ℝ) / (Fintype.card (V i) : ℝ) ^
          (t + (3 * CodePools.blockCount q + 4))) hi.symm))
  have hGJ : Tendsto (fun i => (G i).normalizedEditDistance (J i)) l (𝓝 0) :=
    hGH.congr' (hJeq.mono (fun i hi => by
      change (G i).normalizedEditDistance (H i) = (G i).normalizedEditDistance (J i)
      rw [hi]))
  obtain ⟨ρ, R, hR, hy, _, hJK, hmodel, hcoords⟩ := Canonical.edit_completion F hedges Ω
    p q (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
    (CodePools.pool_card_cast p q hpq hq) J hJ hn l hJlim
  refine ⟨ρ, R, hR, hy, ?_, hmodel, hcoords⟩
  exact RGraph.normalizedEditDistance_tendsto_zero_trans G J _ l hGJ hJK

end TuranUniversality.Structural.Ordinary
