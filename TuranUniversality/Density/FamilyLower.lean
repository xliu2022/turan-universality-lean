module

public import TuranUniversality.Density.FamilyExtremal
public import TuranUniversality.Density.WeightedSampling
public import TuranUniversality.Density.SampleMoments

@[expose] public section

/-! # Real-weight lower bounds for the ordinary density of a finite family

Independent sampling with the specified real vertex weights gives an exact
finite first moment. Every sample of a family-hom-free graph is ordinarily
family-free, so no rational approximation or asymptotic blowup is needed.
-/

open scoped BigOperators

namespace TuranUniversality

open Selector Density

universe u
variable {r : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

namespace RGraph

theorem weightedMean_sample_edge (G : RGraph V r) (x : V → ℝ)
    (hx : ∑ v, x v = 1) (m : ℕ) (e : Finset (Fin m)) (he : e.card = r) :
    weightedMean x (fun f : Fin m → V => truth (e ∈ (G.sample m f).edges)) =
      (r.factorial : ℝ) * G.edgePolynomial x := by
  classical
  let a : Fin r ≃ e := Fintype.equivOfCardEq (by simp [he])
  let i : Fin r → Fin m := fun j => (a j).val
  have hi : Function.Injective i := fun u v h => a.injective (Subtype.ext h)
  have him : Finset.univ.image i = e := by
    ext v
    constructor
    · intro hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact (a j).property
    · intro hv
      obtain ⟨j, hj⟩ := a.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  have hpoint (f : Fin m → V) : truth (e ∈ (G.sample m f).edges) =
      (oneEdge r).homIndicator G (f ∘ i) := by
    unfold truth homIndicator
    congr 1
    apply propext
    rw [G.mem_sample, G.oneEdge_isHom, ← Finset.image_image, him]
    simp [he]
  calc
    _ = weightedMean x (fun f : Fin m → V => (oneEdge r).homIndicator G (f ∘ i)) :=
      weightedMean_congr x hpoint
    _ = weightedMean x ((oneEdge r).homIndicator G) :=
      weightedMean_restrict_injective x hx i hi _
    _ = _ := G.weightedMean_oneEdge x

theorem weightedMean_sample_card (G : RGraph V r) (x : V → ℝ)
    (hx : ∑ v, x v = 1) (m : ℕ) :
    weightedMean x (fun f : Fin m → V => ((G.sample m f).edges.card : ℝ)) =
      (m.choose r : ℝ) * ((r.factorial : ℝ) * G.edgePolynomial x) := by
  classical
  have hcount (f : Fin m → V) : ((G.sample m f).edges.card : ℝ) =
      ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        truth (e ∈ (G.sample m f).edges) := by
    calc
      ((G.sample m f).edges.card : ℝ) =
          ∑ _e ∈ (G.sample m f).edges, (1 : ℝ) := by simp
      _ = ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
          if e.image f ∈ G.edges then (1 : ℝ) else 0 := by
        rw [sample, Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        have hcard := (Finset.mem_powersetCard.mp he).2
        simp [truth, G.mem_sample, hcard]
  calc
    _ = weightedMean x (fun f : Fin m → V =>
        ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
          truth (e ∈ (G.sample m f).edges)) := weightedMean_congr x hcount
    _ = ∑ e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        weightedMean x (fun f : Fin m → V => truth (e ∈ (G.sample m f).edges)) :=
      weightedMean_sum x _ _
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
        ((r.factorial : ℝ) * G.edgePolynomial x) := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.weightedMean_sample_edge x hx m e (Finset.mem_powersetCard.mp he).2
    _ = _ := by simp [Finset.card_powersetCard]

end RGraph

omit [Fintype V] in
theorem familyHomFree_sample (F : Finset (FiniteGraph r)) (G : RGraph V r)
    (hfree : familyHomFree F G) (m : ℕ) (f : Fin m → V) :
    familyHomFree F (G.sample m f) :=
  familyHomFree_of_hom F _ G (G.sample_projection m f) hfree

theorem familyHomFree_weighted_le_extremalDensity (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyHomFree F G) (x : V → ℝ)
    (hx : ProbabilityWeights x) {n : ℕ} (hn : r ≤ n) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ familyExtremalDensity F n := by
  have hpoint (f : Fin n → V) : ((G.sample n f).edges.card : ℝ) ≤
      (familyExtremalNumber F n : ℝ) := by
    exact_mod_cast edge_card_le_familyExtremalNumber F (G.sample n f)
      (familyHomFree_free F _ (familyHomFree_sample F G hfree n f))
  have hmean := weightedMean_mono x hx.1 hpoint
  rw [G.weightedMean_sample_card x hx.2, weightedMean_const x hx.2] at hmean
  have hc : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hn
  apply (le_div_iff₀ hc).mpr
  simpa [mul_comm] using hmean

/-- Every real probability weighting of a finite family-hom-free template
gives a lower bound on the actual ordinary Turán density. -/
theorem familyTuranDensity_lower_of_homFree (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyHomFree F G) (x : V → ℝ)
    (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ familyTuranDensity F := by
  apply le_ciInf
  intro n
  exact familyHomFree_weighted_le_extremalDensity F G hfree x hx (by omega)

/-- Singleton specialization, valid in every uniformity and for real weights. -/
theorem turanDensity_lower_weighted_of_homFree {k : ℕ} (F : RGraph (Fin k) r)
    (G : RGraph V r) (hfree : F.HomFree G) (x : V → ℝ) (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ turanDensity F := by
  have hfamily : familyHomFree {⟨k, F⟩} G := by simpa
  simpa using familyTuranDensity_lower_of_homFree {⟨k, F⟩} G hfamily x hx

omit [DecidableEq V] in
theorem probabilityWeights_uniform [Nonempty V] :
    ProbabilityWeights (fun _ : V => (Fintype.card V : ℝ)⁻¹) := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro v
    positivity
  · simp [hcard]

theorem familyTuranDensity_lower_uniform [Nonempty V] (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyHomFree F G) :
    (RGraph.oneEdge r).homDensity G ≤ familyTuranDensity F := by
  rw [G.oneEdge_homDensity_polynomial]
  exact familyTuranDensity_lower_of_homFree F G hfree _ probabilityWeights_uniform

theorem familyTuranDensity_lower_integer_weights (F : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyHomFree F G) (sizes : V → ℕ)
    (hsizes : 0 < ∑ v, sizes v) :
    (r.factorial : ℝ) * G.edgePolynomial
      (fun v => (sizes v : ℝ) / (∑ w, sizes w : ℕ)) ≤ familyTuranDensity F := by
  have htotal : ((∑ v, sizes v : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hsizes
  apply familyTuranDensity_lower_of_homFree F G hfree
  constructor
  · intro v
    positivity
  · rw [← Finset.sum_div]
    simp only [← Nat.cast_sum]
    exact div_self htotal

end TuranUniversality
