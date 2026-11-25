module

public import TuranUniversality.Structural.RecordProjection
public import TuranUniversality.Density.HomomorphicClosure
public import TuranUniversality.Uniformity.MassOptimization

@[expose] public section

/-! # The actual inner projection and its weighted density bound

All inner edges lie on the active vertices. Restriction to that finite
carrier therefore preserves the polynomial even if neutral vertices carry
positive weight. Ordinary avoidance of the homomorphic closure then gives
the genuine inner-family density bound after cubic mass normalization.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

theorem edgePolynomial_pullback_of_supported [Fintype V]
    (G : RGraph W r) (f : V ↪ W) (hs : ∀ e ∈ G.edges, ∀ w ∈ e, w ∈ Set.range f)
    (x : W → ℝ) : (G.pullback f).edgePolynomial (x ∘ f) = G.edgePolynomial x := by
  classical
  unfold edgePolynomial
  calc
    (∑ e ∈ (G.pullback f).edges, ∏ v ∈ e, (x ∘ f) v) =
        ∑ e ∈ (G.pullback f).edges, ∏ w ∈ e.map f, x w := by
      simp only [Finset.prod_map, Function.comp_apply]
    _ = ∑ e ∈ (G.pullback f).edges.image (fun e => e.map f), ∏ w ∈ e, x w := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact Finset.map_injective f hab
    _ = ∑ e ∈ G.edges.filter (fun e => ∀ w ∈ e, w ∈ Set.range f), ∏ w ∈ e, x w := by
      rw [G.pullback_edges_image f]
    _ = _ := by rw [Finset.filter_true_of_mem hs]

end TuranUniversality.RGraph

namespace TuranUniversality.Structural.LegalObject

variable {V : Type*} [DecidableEq V] {B : Finset (FiniteGraph 3)}

theorem activeProjection_polynomial (O : LegalObject B V) (x : V → ℝ) :
    O.activeProjection.edgePolynomial (fun v => x v.val) = O.projection.edgePolynomial x := by
  apply O.projection.edgePolynomial_pullback_of_supported (Function.Embedding.subtype _)
  intro e he v hv
  exact ⟨⟨v, O.projection_supported e he hv⟩, rfl⟩

theorem projection_normalizedPolynomial_le (F : Finset (FiniteGraph 3))
    (O : LegalObject (homomorphicClosure F) V) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * O.projection.edgePolynomial x ≤
      familyTuranDensity F * (∑ v ∈ O.active, x v) ^ 3 := by
  have hhom : familyHomFree F O.activeProjection :=
    (familyFree_homomorphicClosure_iff F O.activeProjection).mp O.activeProjection_free
  have hb (y : O.active → ℝ) (hy : ProbabilityWeights y) :
      O.activeProjection.edgePolynomial y ≤ familyTuranDensity F / 6 := by
    have h := familyTuranDensity_lower_of_homFree F O.activeProjection hhom y hy
    norm_num at h
    linarith
  have h := O.activeProjection.three_polynomial_bound_of_mass (familyTuranDensity F / 6)
    hb (fun v => x v.val) (fun v => hx v.val)
  rw [O.activeProjection_polynomial x] at h
  have hsum : (∑ v : O.active, x v.val) = ∑ v ∈ O.active, x v :=
    Finset.sum_coe_sort O.active x
  rw [hsum] at h
  nlinarith

end TuranUniversality.Structural.LegalObject
