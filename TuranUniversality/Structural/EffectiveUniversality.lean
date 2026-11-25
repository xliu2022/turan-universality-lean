module

public import TuranUniversality.Structural.FixedThreshold
public import TuranUniversality.Effective.StructuralCompiler
public import TuranUniversality.Structural.LegalOrdinaryData

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

/-! # The actual jointly primitive-recursive structural compiler

Ranks at least the fixed structural threshold are parametrized by their
nonnegative suspension count. The input singleton is literally the compiler
of Theorem 1.1; the output is exactly the finite ordinary forbidden family.
-/

open Filter Topology

namespace TuranUniversality.Structural.Fixed

open TuranUniversality.Computation Effective

noncomputable def compiler (r : ℕ) (β : BinaryWord) : List Uniform.Code :=
  StructuralCodes.compiler pools (r - uniformityThreshold)
    [Uniform.liftThree (forbiddenCompiler β)]

theorem compiler_primrec : Primrec₂ compiler := by
  have hi : Primrec (fun p : ℕ × BinaryWord =>
      [Uniform.liftThree (forbiddenCompiler p.2)]) :=
    Primrec.list_cons.comp (Uniform.liftThree_primrec.comp
      (forbiddenCompiler_primrec.comp Primrec.snd)) (Primrec.const [])
  exact (StructuralCodes.compiler_primrec pools).comp
    (Primrec.nat_sub.comp Primrec.fst (Primrec.const uniformityThreshold)) hi

theorem compiler_computable : Computable₂ compiler := compiler_primrec.to_comp

theorem uniformityThreshold_ge_four : 4 ≤ uniformityThreshold := by
  unfold uniformityThreshold
  omega

theorem compiler_decode_offset (t : ℕ) (β : BinaryWord) :
    Uniform.decodeFamily (t + uniformityThreshold) (compiler (t + uniformityThreshold) β) =
      outerFamily t β := by
  unfold compiler
  rw [Nat.add_sub_cancel]
  change Uniform.decodeFamily (t + (3 * blockCount + 4))
    (StructuralCodes.compiler pools t [Uniform.liftThree (forbiddenCompiler β)]) = _
  rw [StructuralCodes.compiler_decode pools
    (fun _ _ h => CodePools.pools_disjoint numerator denominator numerator_le_denominator h),
    Uniform.decodeFamily_singleton, Uniform.decodeFinite_liftThree]
  rfl

theorem outer_density (t : ℕ) (β : BinaryWord) :
    familyTuranDensity (outerFamily t β) =
      ((t + uniformityThreshold).factorial : ℝ) *
        Ordinary.optimum (innerFamily β) blockCount t numerator denominator := by
  apply Ordinary.density_eq (innerFamily β) (inner_has_edges β) pools
    (fun _ _ h => CodePools.pools_disjoint numerator denominator numerator_le_denominator h)
    t numerator denominator (by positivity)
    (by exact_mod_cast numerator_le_denominator) (by exact_mod_cast denominator_pos)
    (inner_density_ge β)
  exact CodePools.pool_card_cast numerator denominator numerator_le_denominator denominator_pos

theorem near_extremal_polynomial
    (t : ℕ) (β : BinaryWord) {I : Type*} {V : I → Type*}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + uniformityThreshold)) (l : Filter I)
    (h : Tendsto (fun i => (RGraph.oneEdge (t + uniformityThreshold)).homDensity (G i)) l
      (𝓝 (familyTuranDensity (outerFamily t β)))) :
    Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + uniformityThreshold)) l
      (𝓝 (Ordinary.optimum (innerFamily β) blockCount t numerator denominator)) := by
  have hfac : ((t + uniformityThreshold).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hh := h.div_const ((t + uniformityThreshold).factorial : ℝ)
  rw [outer_density, mul_div_cancel_left₀ _ hfac] at hh
  convert hh using 1
  funext i
  rw [RGraph.oneEdge_homDensity, div_right_comm, mul_div_cancel_left₀ _ hfac]

theorem nonhalting_finite_profile
    (t : ℕ) (β : BinaryWord) (hβ : ¬ WordHalts β)
    {I : Type*} {V : I → Type*}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + uniformityThreshold))
    (hG : ∀ i, familyFree (outerFamily t β) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => (RGraph.oneEdge (t + uniformityThreshold)).homDensity (G i)) l
      (𝓝 (familyTuranDensity (outerFamily t β)))) :
    ∃ θ : ∀ i, V i → NeutralRoles.Role blockCount t,
      (∀ i a, PartitionRounding.fiberSize (θ i) a =
        NeutralRoles.targetCounts blockCount t (Fintype.card (V i)) a) ∧
      Tendsto (fun i => (G i).normalizedEditDistance ((neutralPattern t).graph (θ i))) l (𝓝 0) := by
  exact Ordinary.zero_finite_profile_rounded (innerFamily β) (inner_has_edges β)
    numerator denominator numerator_le_denominator denominator_pos t
    ((inner_density_eq_iff β).mpr hβ) G hG hn l hsize
    (near_extremal_polynomial t β G l hlim)

end TuranUniversality.Structural.Fixed
