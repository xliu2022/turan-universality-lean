module

public import TuranUniversality.Structural.CommonLink
public import TuranUniversality.Density.Box

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Weighted samples of records

The sampling space is the actual finite type `Fin n → V`, with product weights.
Repeated vertices are rejected by the success event itself.  Thus the erasure
probability includes both repetitions and missing four-set records.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

open Density

variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def sampleProbability {n : ℕ} (x : V → ℝ) (E : (Fin n → V) → Prop) : ℝ :=
  weightedMean x (fun f => truth (E f))

theorem sampleProbability_nonneg {n : ℕ} (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (E : (Fin n → V) → Prop) : 0 ≤ sampleProbability x E := by
  classical
  unfold sampleProbability weightedMean
  exact Finset.sum_nonneg (fun f _ => mul_nonneg
    (Finset.prod_nonneg (fun i _ => hx (f i))) (truth_nonneg _))

theorem sampleProbability_le_one {n : ℕ} (x : V → ℝ) (hx : ProbabilityWeights x)
    (E : (Fin n → V) → Prop) : sampleProbability x E ≤ 1 := by
  classical
  have h := weightedMean_mono x hx.1
    (F := fun f : Fin n → V => truth (E f))
    (G := fun _ => 1) (fun f => by unfold truth; split <;> norm_num)
  simpa only [sampleProbability, weightedMean_const x hx.2] using h

theorem sampleProbability_compl {n : ℕ} (x : V → ℝ) (hx : ProbabilityWeights x)
    (E : (Fin n → V) → Prop) :
    sampleProbability x (fun f => ¬ E f) = 1 - sampleProbability x E := by
  classical
  unfold sampleProbability
  calc
    weightedMean x (fun f => truth (¬ E f)) =
        weightedMean x (fun f => 1 - truth (E f)) := by
      apply weightedMean_congr
      intro f
      by_cases h : E f <;> simp [truth, h]
    _ = _ := by
      simp only [weightedMean, mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [sum_productWeight x hx.2]

theorem weightedMean_succ {n : ℕ} (x : V → ℝ) (F : (Fin (n + 1) → V) → ℝ) :
    weightedMean x F = weightedMean x (fun f : Fin n → V => ∑ v, x v * F (Fin.cons v f)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => V)
  calc
    weightedMean x F = ∑ p : V × (Fin n → V),
        productWeight x (Fin.cons p.1 p.2) * F (Fin.cons p.1 p.2) :=
      (e.sum_comp (fun f => productWeight x f * F f)).symm
    _ = ∑ f : Fin n → V, ∑ v : V,
        (x v * productWeight x f) * F (Fin.cons v f) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [productWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    _ = weightedMean x (fun f : Fin n → V => ∑ v, x v * F (Fin.cons v f)) := by
      unfold weightedMean
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro v _
      ring

theorem weightedMean_one {x : V → ℝ} (F : V → ℝ) :
    weightedMean x (fun f : Fin 1 → V => F (f 0)) = ∑ v, x v * F v := by
  classical
  unfold weightedMean
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
  intro f
  simp [productWeight, Fin.prod_univ_one, Equiv.funUnique, Equiv.piUnique]

theorem coordinate_probability {n : ℕ} (x : V → ℝ) (hx : ProbabilityWeights x)
    (i : Fin n) (S : Finset V) :
    sampleProbability x (fun f : Fin n → V => f i ∈ S) = ∑ v ∈ S, x v := by
  classical
  let j : Fin 1 → Fin n := fun _ => i
  have hj : Function.Injective j := fun a b _ => Subsingleton.elim a b
  have h := weightedMean_restrict_injective x hx.2 j hj
    (fun f : Fin 1 → V => truth (f 0 ∈ S))
  calc
    sampleProbability x (fun f : Fin n → V => f i ∈ S) =
        weightedMean x (fun f : Fin 1 → V => truth (f 0 ∈ S)) := by
      simpa only [sampleProbability, Function.comp_apply, j] using h
    _ = ∑ v, x v * truth (v ∈ S) := weightedMean_one (x := x) (fun v => truth (v ∈ S))
    _ = _ := by simp [truth]

theorem image_cons {n : ℕ} (v : V) (f : Fin n → V) :
    Finset.univ.image (Fin.cons v f) = insert v (Finset.univ.image f) := by
  ext w
  simp [Fin.exists_fin_succ, eq_comm]

namespace RecordSystem

def Successful (R : RecordSystem V) (f : Fin 4 → V) : Prop :=
  Finset.univ.image f ∈ R.recorded.edges

instance (R : RecordSystem V) (f : Fin 4 → V) : Decidable (R.Successful f) :=
  inferInstanceAs (Decidable (_ ∈ _))

theorem Successful.injective {R : RecordSystem V} {f : Fin 4 → V} (h : R.Successful f) :
    Function.Injective f := by
  have hc := R.recorded.uniform _ h
  have hi : Set.InjOn f (Finset.univ : Finset (Fin 4)) :=
    Finset.card_image_iff.mp (by simpa using hc)
  exact fun a b hab => hi (Finset.mem_univ a) (Finset.mem_univ b) hab

def erasure (R : RecordSystem V) (x : V → ℝ) : ℝ :=
  1 - 24 * R.recorded.edgePolynomial x

theorem success_probability (R : RecordSystem V) (x : V → ℝ) :
    sampleProbability x R.Successful = 24 * R.recorded.edgePolynomial x := by
  classical
  calc
    sampleProbability x R.Successful =
        weightedMean x ((RGraph.oneEdge 4).homIndicator R.recorded) := by
      apply weightedMean_congr
      intro f
      unfold truth RGraph.homIndicator
      congr 1
      exact propext (R.recorded.oneEdge_isHom f).symm
    _ = _ := by simpa [Nat.factorial] using R.recorded.weightedMean_oneEdge x

theorem erasure_probability (R : RecordSystem V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    sampleProbability x (fun f => ¬ R.Successful f) = R.erasure x := by
  rw [sampleProbability_compl x hx, success_probability]
  rfl

theorem erasure_nonneg (R : RecordSystem V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    0 ≤ R.erasure x := by
  rw [← R.erasure_probability x hx]
  exact sampleProbability_nonneg x hx.1 _

theorem erasure_le_one (R : RecordSystem V) (x : V → ℝ) (hx : ProbabilityWeights x) :
    R.erasure x ≤ 1 := by
  rw [← R.erasure_probability x hx]
  exact sampleProbability_le_one x hx _

def sampleNeighborhood (R : RecordSystem V) (f : Fin 3 → V) : Finset V :=
  if Function.Injective f then R.neighborhood (Finset.univ.image f) else ∅

theorem mem_sampleNeighborhood (R : RecordSystem V) (f : Fin 3 → V) (v : V) :
    v ∈ R.sampleNeighborhood f ↔ R.Successful (Fin.cons v f) := by
  classical
  by_cases hf : Function.Injective f
  · simp only [sampleNeighborhood, ite_eq_left hf, mem_neighborhood]
    constructor
    · rintro ⟨_, hrec⟩
      simpa only [Successful, image_cons] using hrec
    · intro h
      have hv := (Fin.cons_injective_iff.mp h.injective).1
      refine ⟨?_, ?_⟩
      · simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hv
      · simpa only [Successful, image_cons] using h
  · simp only [sampleNeighborhood, ite_eq_right hf, Finset.notMem_empty, false_iff]
    intro h
    exact hf (Fin.cons_injective_iff.mp h.injective).2

/-- The expected neighborhood mass is exactly the success probability of one
additional independent vertex. -/
theorem mean_neighborhood_mass (R : RecordSystem V) (x : V → ℝ) :
    weightedMean x (fun f : Fin 3 → V => ∑ v ∈ R.sampleNeighborhood f, x v) =
      1 - R.erasure x := by
  classical
  have h := R.success_probability x
  rw [sampleProbability, weightedMean_succ] at h
  have hp (f : Fin 3 → V) :
      (∑ v, x v * truth (R.Successful (Fin.cons v f))) =
        ∑ v ∈ R.sampleNeighborhood f, x v := by
    simp only [← R.mem_sampleNeighborhood]
    simp [truth]
  change weightedMean x (fun f : Fin 3 → V =>
    ∑ v, x v * truth (R.Successful (Fin.cons v f))) = _ at h
  simp_rw [hp] at h
  rw [h, erasure]
  ring

end RecordSystem
end TuranUniversality.Structural
