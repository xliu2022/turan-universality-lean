module

public import TuranUniversality.Uniformity.Admissible
public import TuranUniversality.Uniformity.MassOptimization
public import TuranUniversality.Density.FamilyLower
public import TuranUniversality.Density.HomInvariance

@[expose] public section

/-! # The actual weighted bound for admissible common-core graphs -/

open scoped BigOperators

namespace TuranUniversality

namespace RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem core_disjoint_link_image (S : Finset V) (e : Finset {v // v ∉ S}) :
    Disjoint S (e.image Subtype.val) := by
  apply Finset.disjoint_left.mpr
  intro v hv he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  exact a.property hv

theorem restoreCore_injective (S : Finset V) :
    Function.Injective (fun e : Finset {v // v ∉ S} => S ∪ e.image Subtype.val) := by
  intro e d h
  apply Finset.image_injective Subtype.val_injective
  have hdiff := congrArg (fun a : Finset V => a \ S) h
  simpa only [Finset.union_sdiff_cancel_left (core_disjoint_link_image S e),
    Finset.union_sdiff_cancel_left (core_disjoint_link_image S d)] using hdiff

/-- Removing and restoring a genuine common core gives an exact edge bijection. -/
theorem coreLink_edges_image (G : RGraph V r) (S : Finset V) (hS : G.IsCore S) :
    (G.coreLink S).edges.image (fun e => S ∪ e.image Subtype.val) = G.edges := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact ((G.mem_coreLink S d).mp hd).2
  · intro he
    let d : Finset {v // v ∉ S} :=
      (e \ S).preimage Subtype.val Subtype.val_injective.injOn
    have him : d.image Subtype.val = e \ S := by
      rw [Finset.image_preimage]
      exact Finset.filter_true_of_mem fun v hv => ⟨⟨v, (Finset.mem_sdiff.mp hv).2⟩, rfl⟩
    have hrestore : S ∪ d.image Subtype.val = e := by
      rw [him]
      exact Finset.union_sdiff_of_subset (hS.subset e he)
    have hdcard : d.card = 3 := by
      calc
        d.card = (d.image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = (e \ S).card := congrArg Finset.card him
        _ = 3 := hS.sdiff_card he
    exact Finset.mem_image.mpr ⟨d,
      (G.mem_coreLink S d).mpr ⟨hdcard, hrestore ▸ he⟩, hrestore⟩

/-- Factor the edge polynomial into the core product and its three-uniform link. -/
theorem coreLink_polynomial (G : RGraph V r) (S : Finset V) (hS : G.IsCore S)
    (x : V → ℝ) :
    G.edgePolynomial x = (∏ v ∈ S, x v) *
      (G.coreLink S).edgePolynomial (fun v => x v.val) := by
  classical
  unfold edgePolynomial
  rw [← G.coreLink_edges_image S hS, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.prod_union (core_disjoint_link_image S e)]
    rw [Finset.prod_image]
    exact fun a _ b _ h => Subtype.val_injective h
  · exact fun a _ b _ h => restoreCore_injective S h

theorem coreLink_polynomial_bound (G : RGraph V r) (S : Finset V) (hS : G.IsCore S)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ y, ProbabilityWeights y → (G.coreLink S).edgePolynomial y ≤ b)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    G.edgePolynomial x ≤ 27 / (r : ℝ) ^ r * b := by
  classical
  let z : S → ℝ := fun v => x v.val
  let y : {v // v ∉ S} → ℝ := fun v => x v.val
  let t := ∑ v, y v
  have hz : ∀ v, 0 ≤ z v := fun v => hx.1 v.val
  have hy : ∀ v, 0 ≤ y v := fun v => hx.1 v.val
  have ht : 0 ≤ t := Finset.sum_nonneg fun v _ => hy v
  have hsum : t + ∑ v, z v = 1 := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ S) x
    rw [← Finset.sum_subtype S (fun v => Iff.rfl) x] at h
    dsimp only [t, y, z]
    rw [Finset.sum_coe_sort]
    rw [add_comm, h, hx.2]
  have hmass := suspension_mass_bound t z ht hz hsum
  have hcard : Fintype.card S + 3 = r := by simpa using hS.card
  have hcardR : (Fintype.card S : ℝ) + 3 = r := by exact_mod_cast hcard
  rw [hcard, hcardR] at hmass
  rw [G.coreLink_polynomial S hS]
  have hprod : (∏ v ∈ S, x v) = ∏ v, z v :=
    (Finset.prod_coe_sort S x).symm
  rw [hprod]
  calc
    (∏ v, z v) * (G.coreLink S).edgePolynomial (fun v => x v.val) ≤
        (∏ v, z v) * (t ^ 3 * b) :=
      mul_le_mul_of_nonneg_left ((G.coreLink S).three_polynomial_bound_of_mass b hb y hy)
        (Finset.prod_nonneg fun v _ => hz v)
    _ = (t ^ 3 * ∏ v, z v) * b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass hb0

end RGraph

namespace Uniformity

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem admissible_polynomial_bound (P : FiniteGraph 3) (G : RGraph V r)
    (hG : Admissible P.2 G) (x : V → ℝ) (hx : ProbabilityWeights x) :
    G.edgePolynomial x ≤ 27 / (r : ℝ) ^ r * (turanDensity P.2 / 6) := by
  have hp : 0 ≤ turanDensity P.2 := turanDensity_nonneg P.2
  rcases hG with hempty | ⟨S, hS, hfree⟩
  · simp only [RGraph.edgePolynomial, hempty, Finset.sum_empty]
    positivity
  · apply G.coreLink_polynomial_bound S hS _ (by positivity) _ x hx
    intro y hy
    have h := turanDensity_lower_weighted_of_homFree P.2 (G.coreLink S) hfree y hy
    norm_num at h
    linarith

/-- The normalized form used by the ordinary finite-family upper bridge. -/
theorem admissible_weighted_bound (P : FiniteGraph 3) (G : RGraph V r)
    (hG : Admissible P.2 G) (x : V → ℝ) (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤
      (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) * turanDensity P.2 := by
  calc
    _ ≤ (r.factorial : ℝ) * (27 / (r : ℝ) ^ r * (turanDensity P.2 / 6)) :=
      mul_le_mul_of_nonneg_left (admissible_polynomial_bound P G hG x hx) (Nat.cast_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end Uniformity
end TuranUniversality
