module

public import TuranUniversality.Structural.CanonicalProfiles
public import TuranUniversality.Structural.PhaseReadback
public import TuranUniversality.Structural.ReadbackConvergence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A positive neutral-frame density in every near-optimal canonical model

The empty-inner readback test uses only the actual neutral frame. Its exact
factorization has positive limiting root and neutral factors in both phase
regimes. Actual completion and record repair preserve the test density.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.RGraph

open Density

variable {A U V : Type*} [DecidableEq A] [DecidableEq U] [DecidableEq V]
variable [Fintype A] [Fintype U] [Fintype V] {r : ℕ}

theorem weightedHomDensity_le_of_sourceEmbedding (J : RGraph A r) (K : RGraph U r)
    {i : A → U} (hi : J.IsEmbedding K i) (G : RGraph V r)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    K.weightedHomDensity G x ≤ J.weightedHomDensity G x := by
  calc
    _ ≤ weightedMean x (fun f : U → V => J.homIndicator G (f ∘ i)) := by
      apply weightedMean_mono x hx.1
      intro f
      by_cases hf : K.IsHom G f
      · simp [hf, hf.comp hi.2]
      · rw [K.homIndicator_of_not_hom G hf]
        exact J.homIndicator_nonneg G _
    _ = _ := weightedMean_restrict_injective x hx.2 i hi.1 _

theorem weightedHomDensity_emptySource (G : RGraph V r) (x : V → ℝ) :
    (RGraph.empty (Fin 0) r).weightedHomDensity G x = 1 := by
  classical
  simp [weightedHomDensity, weightedMean, productWeight, homIndicator, IsHom, RGraph.empty]

end TuranUniversality.RGraph

namespace TuranUniversality.Structural.FrameDensity

variable {I : Type*} {X : I → Type*}
variable [∀ i, DecidableEq (X i)] [∀ i, Fintype (X i)] {b t : ℕ}

theorem rootProduct_tendsto (x : ∀ i, Compiled.Vertex b t (X i) → ℝ) (l : Filter I)
    (hs : ∀ j, Tendsto (fun i => Compiled.suspensionWeight (x i) j) l
      (𝓝 (1 / (OuterWeights.arity b t : ℝ))))
    (hb : ∀ v, Tendsto (fun i => Compiled.rootWeight (x i) v) l
      (𝓝 (3 / (5 * (OuterWeights.arity b t : ℝ))))) :
    Tendsto (fun i => Readback.rootProduct (x i)) l (𝓝 (PhaseRoles.rootMassProduct b t)) := by
  have h := (tendsto_finsetProd Finset.univ (fun j _ => hs j)).mul
    (tendsto_finsetProd Finset.univ (fun v _ => hb v))
  simpa only [Readback.rootProduct, PhaseRoles.rootMassProduct, Compiled.suspensionWeight,
    Compiled.rootWeight, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Support.Vertex, Fintype.card_sigma, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using h

noncomputable def test (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    RGraph (Readback.Vertex (CodePools.blockCount q) t (Fin 0))
      (t + (3 * CodePools.blockCount q + 4)) :=
  Readback.test t (CodePools.pool p q hpq CodePools.neutralLabel)
    (PhaseRoles.testSupport p q hpq hq false)
    ((Support.poolGraph _).uniform _ (PhaseRoles.testSupport_mem p q hpq hq false))
    (RGraph.empty (Fin 0) 3)

theorem frame_inclusion (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ) :
    (Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsEmbedding
      (test p q hpq hq t) Sum.inl := Readback.frame_inclusion _ _ _ _ _

noncomputable def limitValue (q t : ℕ) (δ : ℝ) : ℝ :=
  (2 * 10 ^ CodePools.blockCount q * t.factorial : ℕ) *
    PhaseRoles.rootMassProduct (CodePools.blockCount q) t *
      Compiled.neutralLimit (CodePools.blockCount q) t δ ^ 5

theorem limitValue_pos (q t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) : 0 < limitValue q t δ := by
  have hr : 0 < (OuterWeights.arity (CodePools.blockCount q) t : ℝ) :=
    Nat.cast_pos.mpr (OuterWeights.arity_pos _ _)
  have hn : 0 < Compiled.neutralLimit (CodePools.blockCount q) t δ := by
    unfold Compiled.neutralLimit
    positivity
  unfold limitValue
  exact mul_pos (mul_pos (Nat.cast_pos.mpr (by positivity))
    (PhaseRoles.rootMassProduct_pos _ _)) (pow_pos hn _)

theorem compiled_test_tendsto
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    (R : ∀ i, RecordSystem (X i))
    (hR : ∀ i, (R i).LocallyLegal (homomorphicClosure F))
    (x : ∀ i, Compiled.Vertex (CodePools.blockCount q) t (X i) → ℝ)
    (hx : ∀ i, ProbabilityWeights (x i)) (l : Filter I)
    (hpoly : Tendsto (fun i => (Compiled.graph t (CodePools.pool p q hpq) (R i)).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi (CodePools.blockCount q) t *
        SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (test p q hpq hq t).weightedHomDensity
      (Compiled.graph t (CodePools.pool p q hpq) (R i)) (x i)) l
      (𝓝 (limitValue q t (familyTuranDensity F - (p : ℝ) / q))) := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hpq' : (p : ℝ) ≤ q := Nat.cast_le.mpr hpq
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hΩ := CodePools.pool_card_cast p q hpq hq
  obtain ⟨O, _, hd, _, _, _, hn, _⟩ := Compiled.exists_decoded_models X F hedges
    (CodePools.pool p q hpq) R hR p q hp hpq' hq' hz hΩ x hx hpoly
  have hT := Compiled.eventually_positive_dataMass X F hedges
    (CodePools.pool p q hpq) R hR p q hp hpq' hq' hz hΩ x hx hpoly
  have hroots := Compiled.near_optimal_root_limits X F hedges
    (CodePools.pool p q hpq) R hR p q hp hpq' hq' hz hΩ x hx hpoly
  have hs := Compiled.data_squares_tendsto X F hedges
    (CodePools.pool p q hpq) R hR p q hp hpq' hq' hz hΩ x hx hpoly
  have hrp := rootProduct_tendsto x l hroots.1 (fun v => hroots.2.1 v.1 v.2)
  have hdata i : ∑ v, Compiled.dataWeight (x i) v ≤ 1 := by
    have h := Compiled.mass_sum (x i) (hx i)
    have hs : 0 ≤ ∑ j, Compiled.suspensionWeight (x i) j :=
      Finset.sum_nonneg (fun j _ => (hx i).1 _)
    have hb : 0 ≤ ∑ j, Compiled.blockMass (x i) j :=
      Finset.sum_nonneg (fun j _ => Compiled.blockMass_nonneg (x i) (hx i).1 j)
    change _ + _ + (∑ v, Compiled.dataWeight (x i) v) = 1 at h
    linarith
  have hnq := Readback.neutral_quintic_tendsto O (fun i => Compiled.dataWeight (x i))
    (fun i v => (hx i).1 _) hdata l _ hn hs
  have ho : Tendsto (fun i => (test p q hpq hq t).weightedHomDensity
      (Compiled.graph t (CodePools.pool p q hpq) (O i).records) (x i)) l
      (𝓝 (limitValue q t (familyTuranDensity F - (p : ℝ) / q))) := by
    have h := (hrp.const_mul ((2 * 10 ^ CodePools.blockCount q * t.factorial : ℕ) : ℝ)).mul hnq
    apply h.congr'
    apply Eventually.of_forall
    intro i
    have hraw := Readback.weighted_readback_raw p q hpq hq t (RGraph.empty (Fin 0) 3)
      (fun v => Fin.elim0 v) (O i) false (PhaseRoles.testSupport p q hpq hq false)
      (PhaseRoles.testSupport_mem p q hpq hq false) (x i)
    rw [RGraph.weightedHomDensity_emptySource, mul_one, Readback.neutralAssignment_weight] at hraw
    have hw : (fun v : X i => x i (Readback.dataVertex v)) = Compiled.dataWeight (x i) := rfl
    rw [hw] at hraw
    simpa only [test] using hraw.symm
  have hm := Compiled.mismatch_tendsto l (CodePools.pool p q hpq) R O x hx hT hd
  have hdiff := (test p q hpq hq t).weightedHomDensity_sub_tendsto_zero_of_mismatch
    (fun i => Compiled.graph t (CodePools.pool p q hpq) (R i))
    (fun i => Compiled.graph t (CodePools.pool p q hpq) (O i).records) x hx l hm
  simpa only [sub_add_cancel, zero_add] using hdiff.add ho

theorem canonical_test_tendsto
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    (G : ∀ i, RGraph (X i) (t + (3 * CodePools.blockCount q + 4)))
    (hG : ∀ i, Canonical (homomorphicClosure F) (CodePools.pool p q hpq) (G i))
    (x : ∀ i, X i → ℝ) (hx : ∀ i, ProbabilityWeights (x i)) (l : Filter I)
    (hpoly : Tendsto (fun i => (G i).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi (CodePools.blockCount q) t *
        SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    Tendsto (fun i => (test p q hpq hq t).weightedHomDensity (G i) (x i)) l
      (𝓝 (limitValue q t (familyTuranDensity F - (p : ℝ) / q))) := by
  classical
  choose ρ R H hR hsub hvalue hhom using
    (fun i => Canonical.completion (homomorphicClosure F) (CodePools.pool p q hpq) (G i) (hG i) (x i))
  let y i := Density.pushforwardWeight (Rooted.place (ρ i)) (x i)
  have hy i : ProbabilityWeights (y i) := Density.pushforwardWeight_probability _ _ (hx i)
  let Λ := OuterWeights.chi (CodePools.blockCount q) t * SwitchScalar.phaseScore p q (familyTuranDensity F)
  have hub i : (H i).edgePolynomial (x i) ≤ Λ := by
    rw [hvalue i]
    exact Compiled.polynomial_upper F hedges (CodePools.pool p q hpq) (R i) (hR i)
      p q (Nat.cast_nonneg _) (Nat.cast_le.mpr hpq) (Nat.cast_pos.mpr hq) hz
      (CodePools.pool_card_cast p q hpq hq) (y i) (hy i)
  have hHp : Tendsto (fun i => (H i).edgePolynomial (x i)) l (𝓝 Λ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hpoly tendsto_const_nhds
      (fun i => (G i).edgePolynomial_mono (H i) (hsub i) (hx i).1) hub
  have hcp : Tendsto (fun i => (Compiled.graph t (CodePools.pool p q hpq) (R i)).edgePolynomial (y i))
      l (𝓝 Λ) := by simpa only [hvalue] using hHp
  have ht := compiled_test_tendsto F hedges p q hpq hq t hz R hR y hy l hcp
  have hHtest : Tendsto (fun i => (test p q hpq hq t).weightedHomDensity (H i) (x i)) l
      (𝓝 (limitValue q t (familyTuranDensity F - (p : ℝ) / q))) := by
    apply ht.congr'
    apply Eventually.of_forall
    intro i
    have he := hhom i _ (FiniteGraph.ofRGraph (test p q hpq hq t)).2
    rw [RGraph.weightedHomDensity_source_ofRGraph _ _ _ (hx i).2,
      RGraph.weightedHomDensity_source_ofRGraph _ _ _ (hy i).2] at he
    exact he.symm
  have hd := (test p q hpq hq t).weightedHomDensity_sub_tendsto_zero_of_completion G H hsub x hx l Λ hub hpoly
  simpa only [sub_sub_cancel, sub_zero] using hHtest.sub hd

theorem eventually_frame_density_lower
    (F : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ F, A.2.edges.Nonempty)
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (hz : (p : ℝ) / q ≤ familyTuranDensity F)
    (G : ∀ i, RGraph (X i) (t + (3 * CodePools.blockCount q + 4)))
    (hG : ∀ i, Canonical (homomorphicClosure F) (CodePools.pool p q hpq) (G i))
    (x : ∀ i, X i → ℝ) (hx : ∀ i, ProbabilityWeights (x i)) (l : Filter I)
    (hpoly : Tendsto (fun i => (G i).edgePolynomial (x i)) l
      (𝓝 (OuterWeights.chi (CodePools.blockCount q) t *
        SwitchScalar.phaseScore p q (familyTuranDensity F)))) :
    ∀ᶠ i in l, limitValue q t (familyTuranDensity F - (p : ℝ) / q) / 2 <
      (Frame.graph (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)).weightedHomDensity (G i) (x i) := by
  have hc := limitValue_pos q t _ (sub_nonneg.mpr hz)
  have ht := canonical_test_tendsto F hedges p q hpq hq t hz G hG x hx l hpoly
  have he := (tendsto_order.mp ht).1
    (limitValue q t (familyTuranDensity F - (p : ℝ) / q) / 2) (by linarith)
  filter_upwards [he] with i hi
  exact hi.trans_le (RGraph.weightedHomDensity_le_of_sourceEmbedding _ _
    (frame_inclusion p q hpq hq t) (G i) (x i) (hx i))

end TuranUniversality.Structural.FrameDensity
