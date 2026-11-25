module

public import TuranUniversality.Effective.UniformTemplateMap
public import TuranUniversality.Effective.UniformSuspension
public import TuranUniversality.Effective.UniformCompiler
public import TuranUniversality.Uniformity.UniformTemplates

@[expose] public section

/-! # A primitive-recursive code for the fixed optimal template in every rank

The numeric code is exactly an explicitly relabeled mixed blowup of the
suspension. Both its uniform polynomial and its homomorphism avoidance are
therefore transported from actual finite graphs.
-/

namespace TuranUniversality.Effective.Uniform

open TuranUniversality.Uniformity TuranUniversality.Computation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

attribute [local irreducible] Uniformity.baselineThree forbiddenCompiler

def clonedSuspensionCode (s : ℕ) (g : Code) : Code :=
  numericPullback (s + 3) (mixedOrder s g.1) (suspendCode s g) (mixedTable s g.1)

theorem clonedSuspensionCode_primrec : Primrec₂ clonedSuspensionCode := by
  have hs : Primrec (fun p : ℕ × Code => p.1) := Primrec.fst
  have hg : Primrec (fun p : ℕ × Code => p.2) := Primrec.snd
  have hn : Primrec (fun p : ℕ × Code => p.2.1) := Primrec.fst.comp Primrec.snd
  exact numericPullback_primrec.comp
    ((Primrec.nat_add.comp hs (Primrec.const 3)).pair
      ((mixedOrder_primrec.comp hs hn).pair
        ((suspendCode_primrec.comp hs hg).pair (mixedTable_primrec.comp hs hn))))

/-- Exact graph equality along the explicit clone-numbering equivalence. -/
theorem decode_clonedSuspensionCode (s : ℕ) (g : Code) :
    decode (s + 3) (clonedSuspensionCode s g) =
      (((decode 3 g).suspension s).blowup (mixedSizes s g.1)).pullback
        (mixedEquiv s g.1).symm.toEmbedding := by
  classical
  change decode (s + 3) (mixedOrder s g.1,
    (allRows (s + 3) (mixedOrder s g.1)).filter
      (fun w => Edge (s + 3) (suspendCode s g) (imageRow (mixedTable s g.1) w))) = _
  apply RGraph.ext
  ext e
  refine (mem_decode_numericPullback _ _ _ _ (mixedMap s g.1)
    (fun v => (mixedTable_get s g.1 v).symm) e).trans ?_
  rw [decode_suspendCode]
  constructor
  · rintro ⟨hc, he⟩
    have hp := (((decode 3 g).suspension s).mem_pullback _ _).mp he
    apply (RGraph.mem_pullback _ _ _).mpr
    refine ⟨hc, (RGraph.mem_blowup _ _ _).mpr ⟨by simpa using hc, ?_⟩⟩
    simpa [Finset.map_eq_image, Finset.image_image, mixedMap, Function.comp_def] using hp.2
  · intro he
    obtain ⟨hc, he⟩ := (RGraph.mem_pullback _ _ _).mp he
    have hb := (RGraph.mem_blowup _ _ _).mp he
    have hp : (e.image (mixedMap s g.1)).map
        (finSumFinEquiv.symm : Fin (s + g.1) ≃ Fin s ⊕ Fin g.1).toEmbedding ∈
          ((decode 3 g).suspension s).edges := by
      simpa [Finset.map_eq_image, Finset.image_image, mixedMap, Function.comp_def] using hb.2
    refine ⟨hc, (RGraph.mem_pullback _ _ _).mpr ⟨?_, hp⟩⟩
    simpa only [Finset.card_map] using ((decode 3 g).suspension s).uniform _ hp

theorem clonedSuspensionCode_projection (s : ℕ) (g : Code) :
    (decode (s + 3) (clonedSuspensionCode s g)).IsHom ((decode 3 g).suspension s)
      (fun v => ((mixedEquiv s g.1).symm v).1) := by
  rw [decode_clonedSuspensionCode]
  exact (((decode 3 g).suspension s).blowup_projection (mixedSizes s g.1)).comp
    ((((decode 3 g).suspension s).blowup (mixedSizes s g.1)).pullback_isHom _)

theorem clonedSuspensionCode_order (s : ℕ) (g : Code) :
    (clonedSuspensionCode s g).1 = (s + 3) * g.1 := by
  change s * g.1 + g.1 * 3 = _
  ring

/-- Uniform weights are preserved by the exact finite relabeling. -/
theorem clonedSuspensionCode_uniform_polynomial (s : ℕ) (g : Code) :
    (decode (s + 3) (clonedSuspensionCode s g)).edgePolynomial
      (fun _ => ((clonedSuspensionCode s g).1 : ℝ)⁻¹) =
      (suspendedTemplate (decodeFinite 3 g) s).2.edgePolynomial
        (fun _ => ((suspendedTemplate (decodeFinite 3 g) s).1 : ℝ)⁻¹) := by
  classical
  let B := ((decode 3 g).suspension s).blowup (mixedSizes s g.1)
  have hc : Fintype.card (RGraph.BlowupVertex (mixedSizes s g.1)) = mixedOrder s g.1 := by
    simpa using Fintype.card_congr (mixedEquiv s g.1)
  rw [decode_clonedSuspensionCode]
  change (B.pullback (mixedEquiv s g.1).symm.toEmbedding).edgePolynomial
      ((fun _ => (mixedOrder s g.1 : ℝ)⁻¹) ∘ (mixedEquiv s g.1).symm) =
    (B.pullback (Fintype.equivFin (RGraph.BlowupVertex (mixedSizes s g.1))).symm.toEmbedding).edgePolynomial
      ((fun _ => (Fintype.card (RGraph.BlowupVertex (mixedSizes s g.1)) : ℝ)⁻¹) ∘
        (Fintype.equivFin (RGraph.BlowupVertex (mixedSizes s g.1))).symm)
  rw [B.pullback_equiv_polynomial, B.pullback_equiv_polynomial, hc]

/-- Keep conversion between the two finite three-graph presentations
parametric, so no closed compiler output is evaluated by definitional equality. -/
theorem clonedSuspensionCode_familyHomFree (s : ℕ) (p : Effective.GraphCode) (g : Code)
    (hfree : (Effective.decodeGraph p).HomFree (decode 3 g)) :
    familyHomFree (family (Effective.decodeGraphCode p) (s + 3))
      (decode (s + 3) (clonedSuspensionCode s g)) := by
  have h := familyHomFree_of_admissible (Effective.decodeGraphCode p) (s + 3)
    ((decode 3 g).suspension s)
    (Uniformity.Admissible.suspension (Effective.decodeGraph p) (decode 3 g) s hfree)
  exact familyHomFree_of_hom _ _ _ (clonedSuspensionCode_projection s g) h

theorem singleton_decode_homFree (p : Effective.GraphCode) (g : Code)
    (hfree : (Effective.decodeGraph p).HomFree (decode 3 g)) :
    familyHomFree {Effective.decodeGraphCode p} (decode 3 g) := by
  exact (familyHomFree_singleton _ _).mpr hfree

noncomputable def baselineCode : Code := liftThree (Effective.encodeFiniteGraph baselineThree)

@[simp] theorem decodeFinite_baselineCode : decodeFinite 3 baselineCode = baselineThree := by
  rw [baselineCode, decodeFinite_liftThree, Effective.decode_encode_finiteGraph]

@[simp] theorem baselineCode_order : baselineCode.1 = baselineThree.1 :=
  by
    have h := congrArg (fun G : FiniteGraph 3 => G.1) decodeFinite_baselineCode
    exact h

theorem baselineCode_homFree (β : BinaryWord) :
    (Effective.decodeGraph (forbiddenCompiler β)).HomFree (decode 3 baselineCode) := by
  change (fun G : FiniteGraph 3 => (Effective.decodeGraph (forbiddenCompiler β)).HomFree G.2)
    (decodeFinite 3 baselineCode)
  rw [decodeFinite_baselineCode]
  exact baselineThree_homFree β

theorem baselineCode_uniform_value :
    6 * (decode 3 baselineCode).edgePolynomial (fun _ => (baselineCode.1 : ℝ)⁻¹) =
      (tau3 : ℝ) := by
  change (fun G : FiniteGraph 3 => 6 * G.2.edgePolynomial (fun _ => (G.1 : ℝ)⁻¹))
    (decodeFinite 3 baselineCode) = _
  rw [decodeFinite_baselineCode]
  exact baselineThree_uniform_value

theorem clonedBaseline_uniform_value (s : ℕ) :
    ((s + 3).factorial : ℝ) *
      (decode (s + 3) (clonedSuspensionCode s baselineCode)).edgePolynomial
        (fun _ => ((clonedSuspensionCode s baselineCode).1 : ℝ)⁻¹) =
      (thresholdR (s + 3) : ℝ) := by
  rw [clonedSuspensionCode_uniform_polynomial, decodeFinite_baselineCode]
  exact suspendedTemplate_uniform_value s

theorem clonedBaseline_familyHomFree (s : ℕ) (β : BinaryWord) :
    familyHomFree (family (Effective.decodeGraphCode (forbiddenCompiler β)) (s + 3))
      (decode (s + 3) (clonedSuspensionCode s baselineCode)) :=
  clonedSuspensionCode_familyHomFree s (forbiddenCompiler β) baselineCode (baselineCode_homFree β)

/-- The endpoint uses the original fixed three-template; all other ranks use
the explicit mixed-clone suspension construction. -/
noncomputable def templateCode (r : ℕ) : Code :=
  if r = 3 then baselineCode else clonedSuspensionCode (r - 3) baselineCode

theorem templateCode_primrec : Primrec templateCode :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 3)) (Primrec.const baselineCode)
    (clonedSuspensionCode_primrec.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 3))
      (Primrec.const baselineCode))

theorem templateCode_computable : Computable templateCode := templateCode_primrec.to_comp

@[simp] theorem templateCode_three : templateCode 3 = baselineCode := by simp [templateCode]

noncomputable def uniformCodeValue (r : ℕ) (g : Code) : ℝ :=
  (r.factorial : ℝ) * (decode r g).edgePolynomial (fun _ => (g.1 : ℝ)⁻¹)

def codedFamilyHomFree {r : ℕ} (F : Finset (FiniteGraph r)) (g : Code) : Prop :=
  familyHomFree F (decode r g)

theorem templateCode_order_pos (r : ℕ) : 0 < (templateCode r).1 := by
  by_cases h : r = 3
  · rw [templateCode, ite_eq_left h, baselineCode_order]
    exact baselineThree_order_pos
  · rw [templateCode, ite_eq_right h, clonedSuspensionCode_order, baselineCode_order]
    exact Nat.mul_pos (by omega) baselineThree_order_pos

theorem templateCode_uniform_value (r : ℕ) (hr : 3 ≤ r) :
    (r.factorial : ℝ) * (decode r (templateCode r)).edgePolynomial
      (fun _ => ((templateCode r).1 : ℝ)⁻¹) = (thresholdR r : ℝ) := by
  change uniformCodeValue r (templateCode r) = _
  by_cases h : r = 3
  · subst r
    rw [templateCode_three, thresholdR_three]
    exact baselineCode_uniform_value
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    rw [templateCode, ite_eq_right h, Nat.add_sub_cancel]
    exact clonedBaseline_uniform_value s

/-- The fixed numeric template is homomorphism-free for every input's actual
finite forbidden family. -/
theorem templateCode_familyHomFree (r : ℕ) (hr : 3 ≤ r) (β : BinaryWord) :
    familyHomFree (((compiler r β).map (decodeFinite r)).toFinset)
      (decode r (templateCode r)) := by
  change codedFamilyHomFree _ (templateCode r)
  by_cases h : r = 3
  · subst r
    rw [compiler_decode_three, templateCode_three]
    change familyHomFree {Effective.decodeGraphCode (forbiddenCompiler β)} (decode 3 baselineCode)
    exact singleton_decode_homFree (forbiddenCompiler β) baselineCode (baselineCode_homFree β)
  · rw [compiler_decode_other r hr h β]
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    rw [templateCode, ite_eq_right h, Nat.add_sub_cancel]
    exact clonedBaseline_familyHomFree s β

theorem templateCode_blowup_free (r : ℕ) (hr : 3 ≤ r) (β : BinaryWord)
    (sizes : Fin (templateCode r).1 → ℕ) :
    familyFree (((compiler r β).map (decodeFinite r)).toFinset)
      ((decode r (templateCode r)).blowup sizes) :=
  familyFree_blowup _ _ (templateCode_familyHomFree r hr β) sizes

end TuranUniversality.Effective.Uniform
