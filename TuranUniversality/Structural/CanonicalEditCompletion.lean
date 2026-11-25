module

public import TuranUniversality.Structural.CanonicalWeights
public import TuranUniversality.Density.EditDistance

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Same-carrier completion of canonical near-extremal sequences

The completed graph is explicitly the complete inverse image of its
compiled record system. Its root-class quotient uses the pushforward of
the original uniform weights, and its actual edge-edit distance from the
canonical input tends to zero.
-/

open Filter Topology

namespace TuranUniversality.Structural.Canonical

open Density

universe u v
variable {b t : ℕ}

theorem edit_completion
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * b + 4)))
    (hG : ∀ i, Canonical (homomorphicClosure F) Ω (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * b + 4))) l
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    ∃ (ρ : ∀ i, V i → Option (Rooted.Roots b t)) (R : ∀ i, RecordSystem (V i)),
      (∀ i, (R i).LocallyLegal (homomorphicClosure F)) ∧
      let y i := pushforwardWeight (Rooted.place (ρ i))
        (fun _ : V i => (Fintype.card (V i) : ℝ)⁻¹)
      let K i := (Compiled.graph t Ω (R i)).inverseImage (Rooted.place (ρ i))
      (∀ i, ProbabilityWeights (y i)) ∧
      (∀ i, (G i).edges ⊆ (K i).edges) ∧
      Tendsto (fun i => (G i).normalizedEditDistance (K i)) l (𝓝 0) ∧
      Tendsto (fun i => (Compiled.graph t Ω (R i)).edgePolynomial (y i)) l
        (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) ∧
      ∀ i n (A : RGraph (Fin n) (t + (3 * b + 4))),
        A.homDensity (K i) = A.weightedHomDensity (Compiled.graph t Ω (R i)) (y i) := by
  classical
  choose ρ R hR hhom using hG
  let x i (_ : V i) : ℝ := (Fintype.card (V i) : ℝ)⁻¹
  let y i := pushforwardWeight (Rooted.place (ρ i)) (x i)
  let K i := (Compiled.graph t Ω (R i)).inverseImage (Rooted.place (ρ i))
  have hx i : ProbabilityWeights (x i) := by
    have hp : (0 : ℝ) < Fintype.card (V i) := by exact_mod_cast hn i
    exact ⟨fun _ => inv_nonneg.mpr hp.le, by simp [x, ne_of_gt hp]⟩
  have hy i : ProbabilityWeights (y i) := pushforwardWeight_probability _ _ (hx i)
  have hsub i : (G i).edges ⊆ (K i).edges := by
    intro e he
    exact ((Compiled.graph t Ω (R i)).mem_inverseImage _ e).mpr
      ⟨(G i).uniform e he, hhom i e he⟩
  have heq i : (K i).edgePolynomial (x i) =
      (Compiled.graph t Ω (R i)).edgePolynomial (y i) :=
    (Compiled.graph t Ω (R i)).edgePolynomial_inverseImage _ _
  have hupper i : (K i).edgePolynomial (x i) ≤
      OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) := by
    rw [heq i]
    exact Compiled.polynomial_upper F hedges Ω (R i) (hR i)
      p q hp hpq hq hz hΩ (y i) (hy i)
  have hGlim : Tendsto (fun i => (G i).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) := by
    simpa only [x, RGraph.edgePolynomial_uniform, inv_pow, ← div_eq_mul_inv] using hlim
  have hKlim : Tendsto (fun i => (K i).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hGlim tendsto_const_nhds
      (fun i => (G i).edgePolynomial_mono (K i) (hsub i) (hx i).1) hupper
  refine ⟨ρ, R, hR, hy, hsub, ?_, ?_, ?_⟩
  · change Tendsto (fun i => (G i).normalizedEditDistance (K i)) l (𝓝 0)
    simp_rw [RGraph.normalizedEditDistance_eq_sub (hsub _)]
    simpa only [x, sub_self] using hKlim.sub hGlim
  · simpa only [heq] using hKlim
  · intro i n A
    rw [← A.weightedHomDensity_uniform]
    exact A.weightedHomDensity_inverseImage _ _ _

end TuranUniversality.Structural.Canonical
