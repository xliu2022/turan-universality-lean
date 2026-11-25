module

public import TuranUniversality.Structural.RecordComplete
public import TuranUniversality.Density.FiniteApproximation

@[expose] public section

/-! # Concrete complete record objects with prescribed active mass

An actual hom-free inner graph is placed on the left summand of a disjoint
union. Every vertex in the right summand is neutral. Either of the two
phases may carry the inner graph. The construction retains all vertices,
including isolated vertices, and its polynomial and weight sums are exact.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.RecordApproximation

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def leftGraph (G : RGraph V 3) : RGraph (V ⊕ W) 3 where
  edges := G.edges.image (fun e => e.image Sum.inl)
  uniform := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact G.uniform d hd

theorem leftGraph_polynomial (G : RGraph V 3) (x : V ⊕ W → ℝ) :
    (leftGraph G).edgePolynomial x = G.edgePolynomial (fun v => x (Sum.inl v)) := by
  unfold RGraph.edgePolynomial leftGraph
  rw [Finset.sum_image (fun a _ b _ h => Finset.image_injective Sum.inl_injective h)]
  apply Finset.sum_congr rfl
  intro e _
  exact Finset.prod_image (fun a _ b _ h => Sum.inl_injective h)

theorem leftGraph_projection [Inhabited V] (G : RGraph V 3) :
    (leftGraph G : RGraph (V ⊕ W) 3).IsHom G (Sum.elim id (fun _ => default)) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  simpa [Finset.image_image, Function.comp_def] using hd

def phaseGraph (G : RGraph V 3) (phase a : Bool) : RGraph (V ⊕ W) 3 :=
  if a = phase then leftGraph G else RGraph.empty (V ⊕ W) 3

theorem phaseGraph_projection [Inhabited V] (G : RGraph V 3) (phase a : Bool) :
    (phaseGraph G phase a : RGraph (V ⊕ W) 3).IsHom G
      (Sum.elim id (fun _ => default)) := by
  by_cases h : a = phase
  · simpa only [phaseGraph, h, ite_true] using (leftGraph_projection (W := W) G)
  · simp [phaseGraph, h, RGraph.IsHom, RGraph.empty]

def ofGraph [Fintype V] [Inhabited V] (F : Finset (FiniteGraph 3))
    (G : RGraph V 3) (hG : familyHomFree F G) (phase : Bool) :
    LegalObject (homomorphicClosure F) (V ⊕ W) where
  active := Finset.univ.image Sum.inl
  inner := phaseGraph G phase
  supported := by
    intro a e he v hv
    by_cases h : a = phase
    · simp only [phaseGraph, h, ite_true, leftGraph] at he
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    · simp [phaseGraph, h, RGraph.empty] at he
  onePhase := by
    cases phase <;> simp [phaseGraph, RGraph.empty]
  free := by
    intro a A hA f _ hf
    have hQ := (familyHomFree_homomorphicClosure_iff F G).mpr hG
    exact hQ A hA ⟨Sum.elim id (fun _ : W => (default : V)) ∘ f,
      (phaseGraph_projection G phase a).comp hf.isHom⟩

theorem ofGraph_projection [Fintype V] [Inhabited V] (F : Finset (FiniteGraph 3))
    (G : RGraph V 3) (hG : familyHomFree F G) (phase : Bool) :
    (ofGraph (W := W) F G hG phase).projection = leftGraph G := by
  apply RGraph.ext
  cases phase <;> simp [LegalObject.projection, ofGraph, phaseGraph, RGraph.empty]

def mixtureWeights (α : ℝ) (x : V → ℝ) (y : W → ℝ) : V ⊕ W → ℝ :=
  Sum.elim (fun v => α * x v) (fun w => (1 - α) * y w)

theorem mixture_probability [Fintype V] [Fintype W] (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (x : V → ℝ) (y : W → ℝ)
    (hx : ProbabilityWeights x) (hy : ProbabilityWeights y) :
    ProbabilityWeights (mixtureWeights α x y) := by
  constructor
  · rintro (v | w)
    · exact mul_nonneg hα (hx.1 v)
    · exact mul_nonneg (sub_nonneg.mpr hα1) (hy.1 w)
  · simp only [Fintype.sum_sum_type, mixtureWeights, Sum.elim_inl, Sum.elim_inr,
      ← Finset.mul_sum, hx.2, hy.2, mul_one]
    ring

theorem ofGraph_activeMass [Fintype V] [Fintype W] [Inhabited V]
    (F : Finset (FiniteGraph 3)) (G : RGraph V 3) (hG : familyHomFree F G)
    (phase : Bool) (α : ℝ) (x : V → ℝ) (y : W → ℝ) (hx : ∑ v, x v = 1) :
    (ofGraph F G hG phase).activeMass (mixtureWeights α x y) = α := by
  unfold LegalObject.activeMass ofGraph
  rw [Finset.sum_image (fun a _ b _ h => Sum.inl_injective h)]
  simp only [mixtureWeights, Sum.elim_inl, ← Finset.mul_sum, hx, mul_one]

theorem ofGraph_polynomial [Fintype V] [Inhabited V]
    (F : Finset (FiniteGraph 3)) (G : RGraph V 3) (hG : familyHomFree F G)
    (phase : Bool) (α : ℝ) (x : V → ℝ) (y : W → ℝ) :
    (ofGraph F G hG phase).projection.edgePolynomial (mixtureWeights α x y) =
      α ^ 3 * G.edgePolynomial x := by
  rw [ofGraph_projection, leftGraph_polynomial]
  exact G.edgePolynomial_scale x α

theorem mixture_squares [Fintype V] [Fintype W]
    (α : ℝ) (x : V → ℝ) (y : W → ℝ) :
    ∑ v, (mixtureWeights α x y v) ^ 2 =
      α ^ 2 * ∑ v, (x v) ^ 2 + (1 - α) ^ 2 * ∑ w, (y w) ^ 2 := by
  simp only [Fintype.sum_sum_type, mixtureWeights, Sum.elim_inl, Sum.elim_inr,
    mul_pow, ← Finset.mul_sum]

/-- The relaxed score is exact even at active mass zero, where the ratio
defining `innerDensity` is deliberately totalized. -/
theorem ofGraph_relaxedScore [Fintype V] [Fintype W] [Inhabited V]
    (F : Finset (FiniteGraph 3)) (G : RGraph V 3) (hG : familyHomFree F G)
    (phase : Bool) (p q α : ℝ) (hq : q ≠ 0) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (x : V → ℝ) (y : W → ℝ) (hx : ProbabilityWeights x) (hy : ProbabilityWeights y) :
    (ofGraph F G hG phase).relaxedScore p q (mixtureWeights α x y) =
      160 * q / 24 + (q / 6) *
        ((6 * G.edgePolynomial x - p / q) * α ^ 3 * (1 - α) - α ^ 4) := by
  let O : LegalObject (homomorphicClosure F) (V ⊕ W) := ofGraph F G hG phase
  let w := mixtureWeights α x y
  have hw := mixture_probability α hα hα1 x y hx hy
  have hm : O.activeMass w = α := ofGraph_activeMass F G hG phase α x y hx.2
  have hpoly : O.projection.edgePolynomial w = α ^ 3 * G.edgePolynomial x :=
    ofGraph_polynomial F G hG phase α x y
  have hi := O.innerDensity_mul_mass w hw.1
  rw [hm, hpoly] at hi
  rw [O.relaxedScore_formula p q hq w hw, hm]
  have hi' := congrArg (fun a : ℝ => (q / 6) * (1 - α) * a) hi
  nlinarith only [hi']

theorem uniform_squares (m : ℕ) :
    ∑ _v : Fin m, ((m : ℝ)⁻¹) ^ 2 = (m : ℝ)⁻¹ := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hm : (m : ℝ) = 0
  · simp [hm]
  · field_simp

theorem uniform_mixture_squares (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∑ v, (mixtureWeights α (fun _ : Fin m => (m : ℝ)⁻¹)
      (fun _ : Fin m => (m : ℝ)⁻¹) v) ^ 2 ≤ (m : ℝ)⁻¹ := by
  rw [mixture_squares, uniform_squares]
  have hprod : 0 ≤ α * (1 - α) := mul_nonneg hα (sub_nonneg.mpr hα1)
  have hs : α ^ 2 + (1 - α) ^ 2 ≤ 1 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (m : ℝ)⁻¹)
  nlinarith only [h]

end TuranUniversality.Structural.RecordApproximation
