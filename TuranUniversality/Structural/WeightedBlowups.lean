module

public import TuranUniversality.Density.WeightedHomRestriction
public import TuranUniversality.Hypergraph.Labeled
public import TuranUniversality.Hypergraph.Blowup
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Weighted homomorphism profiles and actual integer blowups

The blowup equality holds for every finite source, including sources with
isolated vertices, and for arbitrary real weights. It supplies the exact
finite identity needed to compare weighted and ordinary limit profiles.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density

variable {U V W : Type*} [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable [Fintype U] [Fintype V] [Fintype W] {r : ℕ}

theorem continuous_weightedHomDensity (F : RGraph U r) (G : RGraph V r) :
    Continuous (fun x : V → ℝ => F.weightedHomDensity G x) := by
  unfold weightedHomDensity weightedMean productWeight
  fun_prop

theorem isHom_blowup_iff (F : RGraph U r) (G : RGraph V r) (sizes : V → ℕ)
    (f : U → BlowupVertex sizes) :
    F.IsHom (G.blowup sizes) f ↔ F.IsHom G (Sigma.fst ∘ f) := by
  constructor
  · intro hf
    exact (G.blowup_projection sizes).comp hf
  · intro hf e he
    apply (G.mem_blowup sizes _).mpr
    constructor
    · have hi : Set.InjOn f e := by
        intro a ha b hb hab
        exact hf.injOn_edge he ha hb (congrArg Sigma.fst hab)
      rw [Finset.card_image_of_injOn hi]
      exact F.uniform e he
    · simpa only [Finset.image_image] using hf e he

private def cloneFunctionEquiv (U V : Type*) (sizes : V → ℕ) :
    (U → BlowupVertex sizes) ≃ Σ f : U → V, ∀ u, Fin (sizes (f u)) where
  toFun f := ⟨fun u => (f u).1, fun u => (f u).2⟩
  invFun f := fun u => ⟨f.1 u, f.2 u⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem weightedHomDensity_blowup (F : RGraph U r) (G : RGraph V r)
    (sizes : V → ℕ) (x : V → ℝ) :
    F.weightedHomDensity (G.blowup sizes) (fun v => x v.1) =
      F.weightedHomDensity G (fun v => (sizes v : ℝ) * x v) := by
  classical
  unfold weightedHomDensity weightedMean
  calc
    _ = ∑ p : Σ f : U → V, ∀ u, Fin (sizes (f u)),
        productWeight x p.1 * F.homIndicator G p.1 := by
      apply Fintype.sum_equiv (cloneFunctionEquiv U V sizes)
      intro f
      simp only [productWeight, cloneFunctionEquiv, Equiv.coe_fn_mk]
      congr 1
      simp only [homIndicator, isHom_blowup_iff, Function.comp_def]
    _ = ∑ f : U → V, (∏ u, (sizes (f u) : ℝ)) *
        (productWeight x f * F.homIndicator G f) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro f _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_prod]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [productWeight, Finset.prod_mul_distrib]
      ring

theorem homDensity_blowup (F : RGraph U r) (G : RGraph V r) (sizes : V → ℕ) :
    F.homDensity (G.blowup sizes) =
      F.weightedHomDensity G (fun v => (sizes v : ℝ) / (∑ w, sizes w : ℕ)) := by
  rw [← weightedHomDensity_uniform]
  have hc : Fintype.card (BlowupVertex sizes) = ∑ v, sizes v := by
    simp only [BlowupVertex, Fintype.card_sigma, Fintype.card_fin]
  rw [hc]
  simpa only [div_eq_mul_inv] using
    weightedHomDensity_blowup F G sizes (fun _ => ((∑ v, sizes v : ℕ) : ℝ)⁻¹)

theorem weightedHomDensity_pullback_equiv (F : RGraph U r) (G : RGraph W r)
    (e : V ≃ W) (x : W → ℝ) :
    F.weightedHomDensity (G.pullback e.toEmbedding) (x ∘ e) =
      F.weightedHomDensity G x := by
  exact weightedHomDensity_pullback_of_hom_supported F G e.toEmbedding
    (fun g _ u => ⟨e.symm (g u), e.apply_symm_apply _⟩) x

theorem homDensity_ofRGraph (F : RGraph U r) (G : RGraph V r) :
    F.homDensity (FiniteGraph.ofRGraph G).2 = F.homDensity G := by
  rw [← weightedHomDensity_uniform, ← weightedHomDensity_uniform]
  change F.weightedHomDensity (G.pullback (Fintype.equivFin V).symm.toEmbedding)
    (fun _ => (Fintype.card (Fin (Fintype.card V)) : ℝ)⁻¹) = _
  simp only [Fintype.card_fin]
  exact weightedHomDensity_pullback_equiv F G (Fintype.equivFin V).symm
    (fun _ => (Fintype.card V : ℝ)⁻¹)

end TuranUniversality.RGraph
