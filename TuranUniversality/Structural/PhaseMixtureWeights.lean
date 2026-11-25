module

public import TuranUniversality.Structural.PhaseMixture
public import TuranUniversality.Structural.CompiledWeights

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Recovering an actual weighting from its role mixture -/

open scoped BigOperators

namespace TuranUniversality.Density

theorem pushforwardWeight_eq_sum_ite {V W : Type*} [Fintype V] [DecidableEq W]
    (f : V → W) (x : V → ℝ) (w : W) :
    pushforwardWeight f x w = ∑ v, if f v = w then x v else 0 := by
  classical
  unfold pushforwardWeight
  rw [← Finset.sum_subtype (Finset.univ.filter (fun v => f v = w))
    (by intro v; simp)]
  rw [Finset.sum_filter]

end TuranUniversality.Density

namespace TuranUniversality.Structural.PhaseRoles

open Density

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

theorem mixtureWeight_susp (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ) (ha : ∑ v, a v = 1) (hw : ∑ v, w v = 1)
    (i : Fin t) : mixtureWeight O z a w (.inl i) = z (.inl (.inl i)) := by
  simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_bool, sampleVertex, rootVertex]
  simp only [Sum.inl.injEq, Sum.inr_ne_inl, ite_false, Finset.sum_const_zero, add_zero]
  simp
  change (∑ u : O.active, ∑ v : Neutral O, z (.inl (.inl i)) * (a u * w v)) = _
  simp only [← Finset.mul_sum, hw, mul_one, ha]

theorem mixtureWeight_block (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ) (ha : ∑ v, a v = 1) (hw : ∑ v, w v = 1)
    (i : Support.Vertex b) : mixtureWeight O z a w (.inr (.inl i)) = z (.inl (.inr i)) := by
  simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_bool, sampleVertex, rootVertex]
  simp only [Sum.inr.injEq, Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
    ite_false, Finset.sum_const_zero, zero_add, add_zero]
  simp
  change (∑ u : O.active, ∑ v : Neutral O, z (.inl (.inr i)) * (a u * w v)) = _
  simp only [← Finset.mul_sum, hw, mul_one, ha]

theorem mixtureWeight_active (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ) (hw : ∑ v, w v = 1) (v : O.active) :
    mixtureWeight O z a w (.inr (.inr v.val)) = z (.inr false) * a v := by
  have hn (u : Neutral O) : u.val ≠ v.val := fun h => u.property (h.symm ▸ v.property)
  simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_bool, sampleVertex, rootVertex]
  simp only [Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, hn,
    ite_false, Finset.sum_const_zero, zero_add, Subtype.val_inj]
  simp
  simp only [← Finset.mul_sum, hw, mul_one]

theorem mixtureWeight_neutral (O : LegalObject B V) (z : Role b t → ℝ)
    (a : O.active → ℝ) (w : Neutral O → ℝ) (ha : ∑ v, a v = 1) (v : Neutral O) :
    mixtureWeight O z a w (.inr (.inr v.val)) = z (.inr true) * w v := by
  have hn (u : O.active) : u.val ≠ v.val := fun h => v.property (h ▸ u.property)
  simp only [mixtureWeight, pushforwardWeight_eq_sum_ite, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_bool, sampleVertex, rootVertex]
  simp only [Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, hn,
    ite_false, Finset.sum_const_zero, zero_add, add_zero, Subtype.val_inj]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_mul, ha, one_mul]

def roleWeight (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ) : Role b t → ℝ
  | .inl j => x (rootVertex j)
  | .inr false => ∑ v : O.active, x (.inr (.inr v.val))
  | .inr true => ∑ v : Neutral O, x (.inr (.inr v.val))

theorem roleWeight_probability (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ)
    (hx : ProbabilityWeights x) : ProbabilityWeights (roleWeight O x) := by
  constructor
  · intro j
    rcases j with j | j
    · exact hx.1 _
    · cases j <;> exact Finset.sum_nonneg (fun v _ => hx.1 _)
  · have hu : @Finset.univ O.active (Subtype.fintype (fun v => v ∈ O.active)) =
        (Finset.univ : Finset O.active) := by
      ext v
      simp only [Finset.mem_univ]
    have hs : (∑ v : O.active, x (.inr (.inr v.val))) +
        (∑ v : Neutral O, x (.inr (.inr v.val))) = ∑ v, x (.inr (.inr v)) := by
      have h := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ O.active)
        (fun v => x (.inr (.inr v)))
      rw [hu] at h
      exact h
    simp only [roleWeight, Fintype.sum_sum_type, Fintype.sum_bool, rootVertex]
    rw [add_comm (∑ v : Neutral O, _) (∑ v : O.active, _), hs]
    simpa only [Fintype.sum_sum_type, add_assoc] using hx.2

noncomputable def activeWeight (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ)
    (v : O.active) : ℝ := x (.inr (.inr v.val)) / roleWeight O x (.inr false)

noncomputable def neutralWeight (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ)
    (v : Neutral O) : ℝ := x (.inr (.inr v.val)) / roleWeight O x (.inr true)

theorem activeWeight_probability (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hA : 0 < roleWeight O x (.inr false)) :
    ProbabilityWeights (activeWeight O x) := by
  refine ⟨fun v => div_nonneg (hx _) hA.le, ?_⟩
  unfold activeWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hA)

theorem neutralWeight_probability (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hW : 0 < roleWeight O x (.inr true)) :
    ProbabilityWeights (neutralWeight O x) := by
  refine ⟨fun v => div_nonneg (hx _) hW.le, ?_⟩
  unfold neutralWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hW)

theorem mixtureWeight_eq (O : LegalObject B V) (x : Compiled.Vertex b t V → ℝ)
    (hx : ∀ v, 0 ≤ x v)
    (hA : 0 < roleWeight O x (.inr false)) (hW : 0 < roleWeight O x (.inr true)) :
    mixtureWeight O (roleWeight O x) (activeWeight O x) (neutralWeight O x) = x := by
  have ha := activeWeight_probability O x hx hA
  have hw := neutralWeight_probability O x hx hW
  funext v
  rcases v with i | (i | v)
  · exact mixtureWeight_susp O _ _ _ ha.2 hw.2 i
  · exact mixtureWeight_block O _ _ _ ha.2 hw.2 i
  · by_cases hv : v ∈ O.active
    · have h := mixtureWeight_active O (roleWeight O x) (activeWeight O x) (neutralWeight O x)
        hw.2 ⟨v, hv⟩
      simpa only [activeWeight, mul_div_cancel₀ _ (ne_of_gt hA)] using h
    · have h := mixtureWeight_neutral O (roleWeight O x) (activeWeight O x) (neutralWeight O x)
        ha.2 ⟨v, hv⟩
      simpa only [neutralWeight, mul_div_cancel₀ _ (ne_of_gt hW)] using h

end TuranUniversality.Structural.PhaseRoles
