module

public import TuranUniversality.Structural.PhaseMixtureWeights
public import TuranUniversality.Structural.WeightedExpectations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The finite neutral role model

There is one neutral data role, which can occur repeatedly in a source edge.
The model is therefore a finite role-sampling law, not a finite simple
hypergraph whose ordinary blowups would incorrectly reject repetitions.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.NeutralRoles

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

abbrev Role (b t : ℕ) := PhaseRoles.Root b t ⊕ Unit

def liftRole : Role b t → PhaseRoles.Role b t
  | .inl r => .inl r
  | .inr _ => .inr true

@[simp] theorem liftRole_ne_active (r : Role b t) : liftRole r ≠ .inr false := by
  cases r <;> simp [liftRole]

theorem activeSet_empty (θ : U → Role b t) : PhaseRoles.activeSet (liftRole ∘ θ) = ∅ := by
  ext u
  simp [PhaseRoles.mem_activeSet, Function.comp_def]

def object (B : Finset (FiniteGraph 3)) (hedges : ∀ A ∈ B, A.2.edges.Nonempty) :
    LegalObject B V := LegalObject.empty B hedges ∅

def sampleVertex : Role b t × V → Compiled.Vertex b t V
  | (.inl r, _) => PhaseRoles.rootVertex r
  | (.inr _, v) => .inr (.inr v)

def sampleMap (θ : U → Role b t) (f : U → V) : U → Compiled.Vertex b t V :=
  fun u => sampleVertex (θ u, f u)

noncomputable def coordinate (Ω : Label → Finset (Cube.Word b))
    (H : RGraph U (t + (3 * b + 4))) (z : Role b t → ℝ) : ℝ :=
  weightedMean z (fun θ => truth
    (PhaseRoles.Compatible Ω false H (liftRole ∘ θ) (RGraph.empty U 3)))

theorem continuous_coordinate (Ω : Label → Finset (Cube.Word b))
    (H : RGraph U (t + (3 * b + 4))) : Continuous (coordinate Ω H) := by
  unfold coordinate weightedMean productWeight
  fun_prop

theorem sampled_compatible_iff (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (θ : U → Role b t) (f : U → V) (hf : Function.Injective f)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    PhaseRoles.Compatible Ω false H (liftRole ∘ θ) (RGraph.empty U 3) ↔
      H.IsHom (Compiled.graph t Ω (object B hedges : LegalObject B V).records) (sampleMap θ f) := by
  let i : PhaseRoles.Data (liftRole ∘ θ) ↪ V :=
    ⟨fun u => f u.val, hf.comp Subtype.val_injective⟩
  have ha (u : PhaseRoles.Data (liftRole ∘ θ)) :
      i u ∈ (object B hedges : LegalObject B V).active ↔
        u ∈ PhaseRoles.activeSet (liftRole ∘ θ) := by
    simp [object, LegalObject.empty, activeSet_empty]
  have hs (a : Bool) (_ha : a ≠ false) :
      ((object B hedges : LegalObject B V).inner a).edges = ∅ := rfl
  have hK (e : Finset (PhaseRoles.Data (liftRole ∘ θ)))
      (_he : e ⊆ PhaseRoles.activeSet (liftRole ∘ θ)) :
      e.map (Function.Embedding.subtype _) ∈ (RGraph.empty U 3).edges ↔
        e.map i ∈ ((object B hedges : LegalObject B V).inner false).edges := by
    simp [object, LegalObject.empty, RGraph.empty]
  have h := PhaseRoles.compatible_iff (liftRole ∘ θ) false (RGraph.empty U 3)
    (object B hedges) i ha hs hK Ω H
  have hm : Compiled.mapData i ∘ PhaseRoles.place (liftRole ∘ θ) = sampleMap θ f := by
    funext u
    simp only [Function.comp_apply]
    unfold PhaseRoles.place
    split
    · rename_i r hr
      cases hθ : θ u with
      | inl s =>
        have hsr : s = r := by simpa [Function.comp_def, liftRole, hθ] using hr
        subst s
        cases r <;> simp [sampleMap, sampleVertex, hθ, PhaseRoles.rootVertex, Compiled.mapData]
      | inr a => simp [Function.comp_def, liftRole, hθ] at hr
    · rename_i c hc
      cases hθ : θ u with
      | inl r => simp [Function.comp_def, liftRole, hθ] at hc
      | inr a => simp [sampleMap, sampleVertex, hθ, Compiled.mapData, i]
  simpa only [hm] using h

theorem sampled_indicator_error (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (θ : U → Role b t) (f : U → V)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    |H.homIndicator (Compiled.graph t Ω (object B hedges : LegalObject B V).records)
        (sampleMap θ f) -
      truth (PhaseRoles.Compatible Ω false H (liftRole ∘ θ) (RGraph.empty U 3))| ≤
      truth (¬ Function.Injective f) := by
  classical
  by_cases hf : Function.Injective f
  · simp only [RGraph.homIndicator, ← sampled_compatible_iff hedges θ f hf Ω H]
    simp [truth, hf]
  · have h1 := H.homIndicator_nonneg
      (Compiled.graph t Ω (object B hedges : LegalObject B V).records) (sampleMap θ f)
    have h2 := H.homIndicator_le_one
      (Compiled.graph t Ω (object B hedges : LegalObject B V).records) (sampleMap θ f)
    have h3 := truth_nonneg
      (PhaseRoles.Compatible Ω false H (liftRole ∘ θ) (RGraph.empty U 3))
    have h4 := truth_le_one
      (PhaseRoles.Compatible Ω false H (liftRole ∘ θ) (RGraph.empty U 3))
    simp only [hf, not_false_eq_true, truth_true]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def mixtureWeight (z : Role b t → ℝ) (w : V → ℝ) :
    Compiled.Vertex b t V → ℝ :=
  pushforwardWeight sampleVertex (fun p => z p.1 * w p.2)

theorem coordinate_mixture_error (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4)))
    (z : Role b t → ℝ) (w : V → ℝ) (hz : ProbabilityWeights z) (hw : ProbabilityWeights w) :
    |H.weightedHomDensity (Compiled.graph t Ω (object B hedges : LegalObject B V).records)
        (mixtureWeight z w) - coordinate Ω H z| ≤
      (Fintype.card U : ℝ) ^ 2 * ∑ v, (w v) ^ 2 := by
  let μ : Role b t × V → ℝ := fun p => z p.1 * w p.2
  let A : (U → Role b t × V) → ℝ := fun f =>
    H.homIndicator (Compiled.graph t Ω (object B hedges : LegalObject B V).records)
      (sampleVertex ∘ f)
  let C : (U → Role b t × V) → ℝ := fun f =>
    truth (PhaseRoles.Compatible Ω false H (liftRole ∘ fun u => (f u).1) (RGraph.empty U 3))
  have hμ : ProbabilityWeights μ := probabilityWeights_product z w hz hw
  have hA : H.weightedHomDensity
      (Compiled.graph t Ω (object B hedges : LegalObject B V).records) (mixtureWeight z w) =
      weightedMean μ A := (weightedMean_pushforward sampleVertex μ _).symm
  have hC : coordinate Ω H z = weightedMean μ C := by
    unfold μ C
    rw [weightedMean_product z w]
    simp only [weightedMean_const w hw.2]
    rfl
  rw [hA, hC]
  apply (weightedMean_abs_sub_le μ hμ.1 A C).trans
  calc
    _ ≤ weightedMean μ (fun f : U → Role b t × V =>
        truth (¬ Function.Injective (fun u => (f u).2))) := by
      apply weightedMean_mono μ hμ.1
      intro f
      exact sampled_indicator_error hedges (fun u => (f u).1) (fun u => (f u).2) Ω H
    _ = weightedMean w (fun f : U → V => truth (¬ Function.Injective f)) := by
      unfold μ
      rw [weightedMean_product z w]
      dsimp only
      rw [weightedMean_const z hz.2]
    _ ≤ _ := weightedMean_collision_le w hw

def roleWeight (x : Compiled.Vertex b t V → ℝ) : Role b t → ℝ
  | .inl r => x (PhaseRoles.rootVertex r)
  | .inr _ => Compiled.dataMass x

theorem roleWeight_probability (x : Compiled.Vertex b t V → ℝ) (hx : ProbabilityWeights x) :
    ProbabilityWeights (roleWeight x) := by
  constructor
  · rintro (r | a)
    · exact hx.1 _
    · exact Compiled.dataMass_nonneg x hx.1
  · simpa [roleWeight, Fintype.sum_sum_type, PhaseRoles.rootVertex,
      Compiled.dataMass, Compiled.dataWeight, add_assoc] using hx.2

theorem mixtureWeight_eq (x : Compiled.Vertex b t V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hT : 0 < Compiled.dataMass x) :
    mixtureWeight (roleWeight x) (Compiled.normalizedData x) = x := by
  have hw := Compiled.normalizedData_probability x hx hT
  funext v
  rcases v with i | (i | v)
  · simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
      Fintype.sum_sum_type, sampleVertex, PhaseRoles.rootVertex]
    simp only [Sum.inl.injEq, Sum.inr_ne_inl, ite_false, Finset.sum_const_zero, add_zero]
    simp [roleWeight, PhaseRoles.rootVertex, ← Finset.mul_sum, hw.2]
  · simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
      Fintype.sum_sum_type, sampleVertex, PhaseRoles.rootVertex]
    simp only [Sum.inr.injEq, Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ite_false, Finset.sum_const_zero, zero_add, add_zero]
    simp [roleWeight, PhaseRoles.rootVertex, ← Finset.mul_sum, hw.2]
  · simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
      Fintype.sum_sum_type, sampleVertex, PhaseRoles.rootVertex]
    simp only [Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false,
      Finset.sum_const_zero, zero_add]
    simp [roleWeight, Compiled.normalizedData, Compiled.dataWeight,
      mul_div_cancel₀ _ (ne_of_gt hT)]

theorem coordinate_error (hedges : ∀ A ∈ B, A.2.edges.Nonempty)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4)))
    (x : Compiled.Vertex b t V → ℝ) (hx : ProbabilityWeights x)
    (hT : 0 < Compiled.dataMass x) :
    |H.weightedHomDensity (Compiled.graph t Ω (object B hedges : LegalObject B V).records) x -
      coordinate Ω H (roleWeight x)| ≤
      (Fintype.card U : ℝ) ^ 2 * ∑ v, (Compiled.normalizedData x v) ^ 2 := by
  simpa only [mixtureWeight_eq x hx.1 hT] using coordinate_mixture_error hedges Ω H
    (roleWeight x) (Compiled.normalizedData x) (roleWeight_probability x hx)
    (Compiled.normalizedData_probability x hx.1 hT)

end TuranUniversality.Structural.NeutralRoles
