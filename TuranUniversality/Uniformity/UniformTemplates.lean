module

public import TuranUniversality.Uniformity.BaselineTemplate
public import TuranUniversality.Uniformity.MassOptimization
public import TuranUniversality.Uniformity.Thresholds

@[expose] public section

/-! # Integer blowups realizing the suspension optimum at uniform weights -/

open scoped BigOperators

namespace TuranUniversality.Uniformity

noncomputable section

def suspendedCloneSizes (G : FiniteGraph 3) (s : ℕ) : Fin s ⊕ Fin G.1 → ℕ :=
  Sum.elim (fun _ => G.1) (fun _ => 3)

theorem suspendedCloneSizes_total (G : FiniteGraph 3) (s : ℕ) :
    (∑ v, suspendedCloneSizes G s v) = (s + 3) * G.1 := by
  simp [suspendedCloneSizes, Fintype.sum_sum_type]
  ring

def suspendedTemplate (G : FiniteGraph 3) (s : ℕ) : FiniteGraph (s + 3) :=
  FiniteGraph.ofRGraph ((G.2.suspension s).blowup (suspendedCloneSizes G s))

theorem suspendedTemplate_order (G : FiniteGraph 3) (s : ℕ) :
    (suspendedTemplate G s).1 = (s + 3) * G.1 := by
  change Fintype.card (RGraph.BlowupVertex (suspendedCloneSizes G s)) = _
  rw [RGraph.blowup_vertex_card, suspendedCloneSizes_total]

theorem suspendedTemplate_order_pos (G : FiniteGraph 3) (hG : 0 < G.1) (s : ℕ) :
    0 < (suspendedTemplate G s).1 := by
  rw [suspendedTemplate_order]
  positivity

theorem suspendedCloneSizes_weights (G : FiniteGraph 3) (hG : 0 < G.1) (s : ℕ) :
    (fun v => (suspendedCloneSizes G s v : ℝ) /
      ((∑ w, suspendedCloneSizes G s w : ℕ) : ℝ)) =
      RGraph.suspensionWeights s (fun _ : Fin G.1 => (G.1 : ℝ)⁻¹) := by
  have hn : (G.1 : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hG
  have hs : (s + 3 : ℝ) ≠ 0 := by positivity
  rw [suspendedCloneSizes_total]
  funext v
  cases v with
  | inl i =>
    simp only [suspendedCloneSizes, RGraph.suspensionWeights, Sum.elim_inl,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp
  | inr v =>
    simp only [suspendedCloneSizes, RGraph.suspensionWeights, Sum.elim_inr,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp

theorem suspendedTemplate_uniform_polynomial (G : FiniteGraph 3) (hG : 0 < G.1) (s : ℕ) :
    (suspendedTemplate G s).2.edgePolynomial
      (fun _ => ((suspendedTemplate G s).1 : ℝ)⁻¹) =
      27 / (s + 3 : ℝ) ^ (s + 3) * G.2.edgePolynomial (fun _ => (G.1 : ℝ)⁻¹) := by
  let B := (G.2.suspension s).blowup (suspendedCloneSizes G s)
  change (B.pullback (Fintype.equivFin (RGraph.BlowupVertex (suspendedCloneSizes G s))).symm.toEmbedding).edgePolynomial
    ((fun _ => (Fintype.card (RGraph.BlowupVertex (suspendedCloneSizes G s)) : ℝ)⁻¹) ∘
      (Fintype.equivFin (RGraph.BlowupVertex (suspendedCloneSizes G s))).symm) = _
  rw [B.pullback_equiv_polynomial]
  change ((G.2.suspension s).blowup (suspendedCloneSizes G s)).edgePolynomial _ = _
  rw [(G.2.suspension s).blowup_polynomial, suspendedCloneSizes_weights G hG s,
    G.2.suspensionWeights_value]

theorem suspendedTemplate_uniform_value (s : ℕ) :
    ((s + 3).factorial : ℝ) * (suspendedTemplate baselineThree s).2.edgePolynomial
      (fun _ => ((suspendedTemplate baselineThree s).1 : ℝ)⁻¹) =
      (thresholdR (s + 3) : ℝ) := by
  rw [suspendedTemplate_uniform_polynomial baselineThree baselineThree_order_pos s,
    thresholdR_cast]
  have h := baselineThree_uniform_value
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [← h]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem suspendedTemplate_familyHomFree {s : ℕ} (F : Finset (FiniteGraph (s + 3)))
    (G : FiniteGraph 3) (h : familyHomFree F (G.2.suspension s)) :
    familyHomFree F (suspendedTemplate G s).2 := by
  intro A hA
  have hB := A.2.blowup_homFree (G.2.suspension s) (h A hA) (suspendedCloneSizes G s)
  rintro ⟨f, hf⟩
  exact hB ⟨_, (FiniteGraph.ofRGraph_embedding
    ((G.2.suspension s).blowup (suspendedCloneSizes G s))).isHom.comp hf⟩

end
end TuranUniversality.Uniformity
