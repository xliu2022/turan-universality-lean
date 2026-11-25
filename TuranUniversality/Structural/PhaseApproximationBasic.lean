module

public import TuranUniversality.Structural.PhaseConvergence
public import TuranUniversality.Structural.CompiledOptimum

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact roles and inner profile of a concrete phase object

The active carrier is explicitly equivalent to the original inner graph.
This retains all isolated vertices. Optimal outer weights and the two data
probability distributions recover the prescribed role masses exactly.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.RecordApproximation

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable [Fintype V] [Fintype W] [Inhabited V]
variable (F : Finset (FiniteGraph 3)) (G : RGraph V 3)
variable (hG : familyHomFree F G) (phase : Bool)

@[simp] theorem ofGraph_inl_mem_active (v : V) :
    Sum.inl v ∈ (ofGraph (W := W) F G hG phase).active := by
  simp [ofGraph]

@[simp] theorem ofGraph_inr_not_mem_active (w : W) :
    Sum.inr w ∉ (ofGraph (W := W) F G hG phase).active := by
  simp [ofGraph]

noncomputable def activeEquiv : V ≃ (ofGraph (W := W) F G hG phase).active :=
  Equiv.ofBijective (fun v => ⟨Sum.inl v, ofGraph_inl_mem_active F G hG phase v⟩) (by
    constructor
    · intro v w h
      exact Sum.inl_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨v, hv⟩ := v
      rcases v with v | w
      · exact ⟨v, rfl⟩
      · exact False.elim ((ofGraph_inr_not_mem_active F G hG phase w) hv))

@[simp] theorem activeEquiv_val (v : V) :
    (activeEquiv (W := W) F G hG phase v).val = Sum.inl v := rfl

noncomputable def neutralEquiv : W ≃ PhaseRoles.Neutral (ofGraph (W := W) F G hG phase) :=
  Equiv.ofBijective (fun w => ⟨Sum.inr w, ofGraph_inr_not_mem_active F G hG phase w⟩) (by
    constructor
    · intro v w h
      exact Sum.inr_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨v, hv⟩ := v
      rcases v with v | w
      · exact False.elim (hv (ofGraph_inl_mem_active F G hG phase v))
      · exact ⟨w, rfl⟩)

@[simp] theorem neutralEquiv_val (w : W) :
    (neutralEquiv (W := W) F G hG phase w).val = Sum.inr w := rfl

theorem activeGraph_pullback_equiv :
    (((ofGraph (W := W) F G hG phase).inner phase).pullback
      (Function.Embedding.subtype _)).pullback (activeEquiv F G hG phase).toEmbedding = G := by
  have hi : (ofGraph (W := W) F G hG phase).inner phase = leftGraph G := by
    simp [ofGraph, phaseGraph]
  rw [hi]
  ext e
  simp only [RGraph.mem_pullback, Finset.card_map]
  simp only [Finset.map_eq_image, Finset.image_image]
  change (e.card = 3 ∧ e.card = 3 ∧ e.image Sum.inl ∈
    G.edges.image (fun d => d.image (Sum.inl : V → V ⊕ W))) ↔ e ∈ G.edges
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := Finset.mem_image.mp h.2.2
    have hde : d = e := Finset.image_injective Sum.inl_injective he
    simpa only [hde] using hd
  · intro he
    exact ⟨G.uniform e he, G.uniform e he, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩

theorem ofGraph_other_phase (s : Bool) (hs : s ≠ phase) :
    ((ofGraph (W := W) F G hG phase).inner s).edges = ∅ := by
  simp [ofGraph, phaseGraph, hs, RGraph.empty]

end TuranUniversality.Structural.RecordApproximation

namespace TuranUniversality.Structural.PhaseRoles

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable [Fintype V] [Fintype W] [Inhabited V] {b t : ℕ}

noncomputable def optimalRoleWeight (b t : ℕ) (α : ℝ) : Role b t → ℝ
  | .inl (.inl _) => 1 / (OuterWeights.arity b t : ℝ)
  | .inl (.inr _) => 3 / (5 * (OuterWeights.arity b t : ℝ))
  | .inr false => (4 / (OuterWeights.arity b t : ℝ)) * α
  | .inr true => (4 / (OuterWeights.arity b t : ℝ)) * (1 - α)

theorem ofGraph_roleWeight (F : Finset (FiniteGraph 3)) (G : RGraph V 3)
    (hG : familyHomFree F G) (phase : Bool) (α : ℝ)
    (x : V → ℝ) (y : W → ℝ) (hx : ∑ v, x v = 1) (hy : ∑ w, y w = 1) :
    roleWeight (RecordApproximation.ofGraph F G hG phase)
      (Compiled.optimalWeights b t (RecordApproximation.mixtureWeights α x y)) =
        optimalRoleWeight b t α := by
  funext j
  rcases j with (j | j) | a
  · rfl
  · rfl
  · cases a
    · change (∑ v : (RecordApproximation.ofGraph F G hG phase).active, _) = _
      rw [← (RecordApproximation.activeEquiv F G hG phase).sum_comp]
      simp only [Compiled.optimalWeights, RecordApproximation.activeEquiv_val,
        RecordApproximation.mixtureWeights, Sum.elim_inr, Sum.elim_inl,
        optimalRoleWeight, ← Finset.mul_sum, hx, mul_one]
    · change (∑ v : Neutral (RecordApproximation.ofGraph F G hG phase), _) = _
      rw [← (RecordApproximation.neutralEquiv F G hG phase).sum_comp]
      simp only [Compiled.optimalWeights, RecordApproximation.neutralEquiv_val,
        RecordApproximation.mixtureWeights, Sum.elim_inr, Sum.elim_inl,
        optimalRoleWeight, ← Finset.mul_sum, hy, mul_one]

theorem ofGraph_activeWeight (F : Finset (FiniteGraph 3)) (G : RGraph V 3)
    (hG : familyHomFree F G) (phase : Bool) (α : ℝ) (hα : α ≠ 0)
    (x : V → ℝ) (y : W → ℝ) (hx : ∑ v, x v = 1) (hy : ∑ w, y w = 1) :
    activeWeight (RecordApproximation.ofGraph F G hG phase)
      (Compiled.optimalWeights b t (RecordApproximation.mixtureWeights α x y)) ∘
        RecordApproximation.activeEquiv F G hG phase = x := by
  have hr : (OuterWeights.arity b t : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (OuterWeights.arity_pos b t))
  funext v
  rw [Function.comp_apply, activeWeight, ofGraph_roleWeight F G hG phase α x y hx hy]
  simp only [optimalRoleWeight, Compiled.optimalWeights, RecordApproximation.activeEquiv_val,
    RecordApproximation.mixtureWeights, Sum.elim_inr, Sum.elim_inl]
  field_simp [hα, hr]

theorem ofGraph_innerProfile (F : Finset (FiniteGraph 3)) (G : RGraph V 3)
    (hG : familyHomFree F G) (phase : Bool) (α : ℝ) (hα : α ≠ 0)
    (x : V → ℝ) (y : W → ℝ) (hx : ∑ v, x v = 1) (hy : ∑ w, y w = 1) :
    innerProfile (RecordApproximation.ofGraph F G hG phase) phase
      (Compiled.optimalWeights b t (RecordApproximation.mixtureWeights α x y)) =
        SetFamily.weightedProfile G x := by
  funext H
  unfold innerProfile SetFamily.weightedProfile
  rw [← RGraph.weightedHomDensity_pullback_equiv H.2 _
    (RecordApproximation.activeEquiv F G hG phase)]
  rw [RecordApproximation.activeGraph_pullback_equiv,
    ofGraph_activeWeight F G hG phase α hα x y hx hy]

end TuranUniversality.Structural.PhaseRoles
