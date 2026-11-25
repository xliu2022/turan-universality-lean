module

public import TuranUniversality.Construction.Signature
public import TuranUniversality.Construction.GuardNumerics
public import TuranUniversality.Selector.RootedMonotonicity
public import TuranUniversality.Weighted.Nonhalting
public import TuranUniversality.Hypergraph.WeightTransport

@[expose] public section

/-! # The concrete input-dependent class and its nonhalting weighted bound -/

namespace TuranUniversality.Reduction

open Construction Weighted Selector Computation Computation.MatchingSystem Turing
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {Γ Λ : Type*} [DecidableEq Γ] [Fintype Γ] [Inhabited Γ]
  [DecidableEq Λ] [Fintype Λ] [Inhabited Λ]

noncomputable def alphabetSize (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] : ℕ :=
  Fintype.card (LocalSystem.Label Γ Λ)

def Legal {V : Type*} [Fintype V] [DecidableEq V]
    (M : TM0.Machine Γ Λ) (input : List Γ) (G : RGraph V 3) : Prop :=
  Admissible (compilerSignature (LocalSystem.Label Γ Λ))
    (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ))) (LocalSystem.specification M input) G

theorem Legal.of_embedding {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {M : TM0.Machine Γ Λ} {input : List Γ}
    (F : RGraph V 3) (G : RGraph W 3) (hG : Legal M input G)
    (f : V → W) (hf : F.IsEmbedding G f) : Legal M input F :=
  Admissible.of_embedding _ _ _ F G hG f hf

/-- The unrooted class admits every partial rooting, including ones missing
root labels. Injective transport assigns zero weight to all added isolated
roots and data copies, so the actual original graph obeys the same bound. -/
theorem Legal.nonhalting_bound {V : Type*} [Fintype V] [DecidableEq V]
    {M : TM0.Machine Γ Λ} {input : List Γ} (G : RGraph V 3)
    (hG : Legal M input G) (hn : ¬ (TM0.eval M input).Dom)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    6 * G.edgePolynomial x ≤ (threshold (alphabetSize Γ Λ) : ℝ) := by
  classical
  obtain ⟨ρ, hρ⟩ := hG
  let A := alphabetSize Γ Λ
  let S := compilerSignature (LocalSystem.Label Γ Λ)
  let Q := rootedImage G ρ.val ρ.property
  let f := rootedVertex ρ.val
  let y := pushWeights f x
  have hemb : G.IsEmbedding Q.toRGraph f := by
    simpa only [Q, rootedImage_toRGraph] using rootedGraph_embedding G ρ.val ρ.property
  have htrans := G.embedding_weight_transport Q.toRGraph f hemb x hx.1
  have hy : ProbabilityWeights y := pushWeights_probability f x hx
  let z : RootLabels A → ℝ := fun r => y (Sum.inl r)
  let w : V → ℝ := fun v => y (Sum.inr v)
  have hweights : Sum.elim z w = y := by funext a; cases a <;> rfl
  have hnorm : (∑ r, z r) + (∑ v, w v) = 1 := by
    calc
      _ = ∑ a, y a := (Fintype.sum_sum_type y).symm
      _ = 1 := hy.2
  have hm : 30 ≤ Fintype.card (PhysicalKinds A) := by
    rw [physicalKinds_card]
    exact physicalCount_ge _
  have hq : (Fintype.card (RootLabels A) : ℝ) =
      rootCount (Fintype.card (PhysicalKinds A) : ℝ) := by
    rw [rootLabels_card, physicalKinds_card, rootNumber_cast]
  have hqu : (Fintype.card (RootLabels A) : ℝ) =
      Real.sqrt (rootNumber (chosenParameter A)) ^ 2 := by
    rw [rootLabels_card, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hbound := S.nonhalting_edgePolynomial_le_baseline Q
    (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ))) M input hρ hn z w
    (Real.sqrt (rootNumber (chosenParameter A))) hm (rootSqrt_large A) hq hqu
    (copyCount_bounds A).1 (copyCount_bounds A).2 (fun r => hy.1 _) (fun v => hy.1 _) hnorm
  have hpolyEq : Q.toRGraph.edgePolynomial (Sum.elim z w) = Q.toRGraph.edgePolynomial y := by
    congr 1
  have hbound' : Q.toRGraph.edgePolynomial y ≤
      baselineMax (physicalCount (chosenParameter A)) (rootNumber (chosenParameter A)) := by
    rw [← hpolyEq]
    simpa only [physicalKinds_card, rootLabels_card, A, alphabetSize] using hbound
  have hτ := threshold_cast A
  change 6 * G.edgePolynomial x ≤ (threshold A : ℝ)
  change G.edgePolynomial x ≤ Q.toRGraph.edgePolynomial y at htrans
  linarith only [htrans, hbound', hτ]

def GuardedLegal {V : Type*} [Fintype V] [DecidableEq V]
    (M : TM0.Machine Γ Λ) (input : List Γ) (G : RGraph V 3) : Prop :=
  Legal M input G ∨ ¬ ∃ f, (fixedGuard (alphabetSize Γ Λ)).IsEmbedding G f

theorem GuardedLegal.nonhalting_bound {V : Type*} [Fintype V] [DecidableEq V]
    {M : TM0.Machine Γ Λ} {input : List Γ} (G : RGraph V 3)
    (hG : GuardedLegal M input G) (hn : ¬ (TM0.eval M input).Dom)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    6 * G.edgePolynomial x ≤ (threshold (alphabetSize Γ Λ) : ℝ) := by
  rcases hG with hG | hG
  · exact hG.nonhalting_bound G hn x hx
  · exact (guard_free_below_threshold _ G hG x hx).le

end TuranUniversality.Reduction
