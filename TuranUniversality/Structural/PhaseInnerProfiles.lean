module

public import TuranUniversality.Structural.PhaseReadbackWeights
public import TuranUniversality.Structural.ExtremalProfiles

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual inner profiles and finite phase extraction

The active normalized graph is hom-free for the original family. Its edge
coordinate is the same cubic ratio used in the scalar optimization. Phase
selection is an ordinary subsequence argument on the actual two inner graphs.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.Structural.LegalObject

variable {V : Type*} [DecidableEq V] [Fintype V] {B : Finset (FiniteGraph 3)}

theorem projection_eq_phase (O : LegalObject B V) (phase : Bool)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅) : O.projection = O.inner phase := by
  cases phase
  · apply RGraph.ext
    simp [projection, hphase true (by decide : true ≠ false)]
  · apply RGraph.ext
    simp [projection, hphase false Bool.false_ne_true]

theorem active_inner_homFree (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (phase : Bool) :
    familyHomFree F (Readback.activeGraph O phase) := by
  apply (familyFree_homomorphicClosure_iff F _).mp
  intro A hA
  rintro ⟨f, hf⟩
  have hemb : (Readback.activeGraph O phase).IsEmbedding (O.inner phase) Subtype.val :=
    ⟨Subtype.val_injective, (O.inner phase).pullback_isHom (Function.Embedding.subtype _)⟩
  exact O.free phase A hA (Subtype.val ∘ f) (fun u => (f u).property) (hemb.comp hf)

theorem innerDensity_scale (O : LegalObject B V) (x : V → ℝ) (c : ℝ) (hc : c ≠ 0) :
    O.innerDensity (fun v => c * x v) = O.innerDensity x := by
  have hm : O.activeMass (fun v => c * x v) = c * O.activeMass x := by
    simp only [activeMass, Finset.mul_sum]
  rw [innerDensity, O.projection.edgePolynomial_scale, hm, innerDensity, mul_pow]
  calc
    6 * (c ^ 3 * O.projection.edgePolynomial x) / (c ^ 3 * O.activeMass x ^ 3) =
        (c ^ 3 * (6 * O.projection.edgePolynomial x)) / (c ^ 3 * O.activeMass x ^ 3) := by ring
    _ = _ := mul_div_mul_left _ _ (pow_ne_zero 3 hc)

end TuranUniversality.Structural.LegalObject

namespace TuranUniversality.Structural.PhaseRoles

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}
variable {B : Finset (FiniteGraph 3)}

theorem innerProfile_mem_free (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (phase : Bool)
    (x : Compiled.Vertex b t V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (ha : 0 < roleWeight O x (.inr false)) :
    innerProfile O phase x ∈ SetFamily.freeLimitProfiles (F : Set _) := by
  have hp := activeWeight_probability O x hx ha
  refine ⟨SetFamily.isLimitProfile_weighted _ _ hp, ?_⟩
  intro A hA
  exact A.2.weightedHomDensity_eq_zero_of_homFree _ (O.active_inner_homFree F phase A hA) _

theorem innerProfile_edge_eq_data (O : LegalObject B V) (phase : Bool)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (x : Compiled.Vertex b t V → ℝ) :
    innerProfile O phase x (SetFamily.edgeTest 3) = O.innerDensity (Compiled.dataWeight x) := by
  rw [innerProfile_eq_readback]
  change (RGraph.oneEdge 3).weightedHomDensity (Readback.activeGraph O phase)
    (Readback.normalizedActiveWeight O (Compiled.dataWeight x)) = _
  rw [RGraph.weightedHomDensity_oneEdge]
  have hp := O.projection_eq_phase phase hphase
  change (Nat.factorial 3 : ℝ) *
    ((O.inner phase).pullback (Function.Embedding.subtype _)).edgePolynomial
      (Readback.normalizedActiveWeight O (Compiled.dataWeight x)) = _
  rw [← hp]
  change (Nat.factorial 3 : ℝ) * O.activeProjection.edgePolynomial
    (Readback.normalizedActiveWeight O (Compiled.dataWeight x)) = _
  have hw : Readback.normalizedActiveWeight O (Compiled.dataWeight x) =
      (fun v : O.active => (O.activeMass (Compiled.dataWeight x))⁻¹ * Compiled.dataWeight x v.val) := by
    funext v
    simp only [Readback.normalizedActiveWeight, div_eq_mul_inv, mul_comm]
  rw [hw, RGraph.edgePolynomial_scale, O.activeProjection_polynomial]
  norm_num only [Nat.factorial]
  simp only [LegalObject.innerDensity, div_eq_mul_inv, inv_pow]
  ring

theorem innerDensity_normalizedData (O : LegalObject B V)
    (x : Compiled.Vertex b t V → ℝ) (hT : 0 < Compiled.dataMass x) :
    O.innerDensity (Compiled.dataWeight x) = O.innerDensity (Compiled.normalizedData x) := by
  have he : Compiled.dataWeight x = fun v =>
      Compiled.dataMass x * Compiled.normalizedData x v := by
    funext v
    simp [Compiled.normalizedData, ne_of_gt hT, mul_div_cancel₀]
  rw [he, O.innerDensity_scale _ _ (ne_of_gt hT)]

theorem innerProfile_edge_eq (O : LegalObject B V) (phase : Bool)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (x : Compiled.Vertex b t V → ℝ) (hT : 0 < Compiled.dataMass x) :
    innerProfile O phase x (SetFamily.edgeTest 3) = O.innerDensity (Compiled.normalizedData x) := by
  rw [innerProfile_edge_eq_data O phase hphase, innerDensity_normalizedData O x hT]

theorem exists_fixed_phase_subsequence {X : ℕ → Type*}
    [∀ n, DecidableEq (X n)] [∀ n, Fintype (X n)]
    (O : ∀ n, LegalObject B (X n)) (P : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) :
    ∃ (phase : Bool) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ n, P (φ n)) ∧ (∀ n s, s ≠ phase → ((O (φ n)).inner s).edges = ∅) := by
  by_cases hf : ∃ᶠ n in atTop, ((O n).inner false).edges = ∅
  · obtain ⟨φ, hφ, hh⟩ := extraction_of_frequently_atTop (hf.and_eventually hP)
    refine ⟨true, φ, hφ, fun n => (hh n).2, ?_⟩
    intro n s hs
    cases s
    · exact (hh n).1
    · exact (hs rfl).elim
  · have hn : ∀ᶠ n in atTop, ((O n).inner false).edges ≠ ∅ := not_frequently.mp hf
    have ht : ∀ᶠ n in atTop, ((O n).inner true).edges = ∅ ∧ P n := by
      filter_upwards [hn, hP] with n hn hp
      exact ⟨(O n).onePhase.resolve_left hn, hp⟩
    obtain ⟨φ, hφ, hh⟩ := extraction_of_eventually_atTop ht
    refine ⟨false, φ, hφ, fun n => (hh n).2, ?_⟩
    intro n s hs
    cases s
    · exact (hs rfl).elim
    · exact (hh n).1

end TuranUniversality.Structural.PhaseRoles
