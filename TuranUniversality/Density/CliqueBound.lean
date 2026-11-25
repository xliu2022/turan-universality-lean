module

public import TuranUniversality.Density.WeightedSampling
public import TuranUniversality.Density.Sampling
public import TuranUniversality.Hypergraph.Clique
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! # The clique-free weighted bound by finite independent sampling -/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weightedMean_image_edge (G : RGraph V 3) (x : V → ℝ)
    (hx : ∑ v, x v = 1) (t : ℕ) (e : Finset (Fin t)) (he : e.card = 3) :
    weightedMean x (fun f : Fin t → V => truth (e.image f ∈ G.edges)) =
      6 * G.edgePolynomial x := by
  classical
  let a : Fin 3 ≃ e := Fintype.equivOfCardEq (by simp [he])
  let i : Fin 3 → Fin t := fun j => (a j).val
  have hi : Function.Injective i := fun j k h => a.injective (Subtype.ext h)
  have himage : Finset.univ.image i = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact (a j).property
    · intro hv
      obtain ⟨j, hj⟩ := a.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  have hpoint (f : Fin t → V) : truth (e.image f ∈ G.edges) =
      (oneEdge 3).homIndicator G (f ∘ i) := by
    unfold truth homIndicator
    congr 1
    apply propext
    rw [G.oneEdge_isHom, ← Finset.image_image, himage]
  calc
    weightedMean x (fun f : Fin t → V => truth (e.image f ∈ G.edges)) =
        weightedMean x (fun f : Fin t → V => (oneEdge 3).homIndicator G (f ∘ i)) :=
      weightedMean_congr x hpoint
    _ = weightedMean x ((oneEdge 3).homIndicator G) :=
      weightedMean_restrict_injective x hx i hi _
    _ = _ := by simpa [Nat.factorial] using G.weightedMean_oneEdge x

/-- The standard clique bound holds for all real probability weights, using
a union bound on actual independent finite vertex samples. -/
theorem clique_free_weighted_bound (G : RGraph V 3) {t : ℕ} (ht : 3 ≤ t)
    (hfree : (clique (Fin t) 3).HomFree G) (x : V → ℝ) (hx : ProbabilityWeights x) :
    6 * G.edgePolynomial x ≤ 1 - 1 / (t.choose 3 : ℝ) := by
  classical
  let E := (Finset.univ : Finset (Fin t)).powersetCard 3
  have hpoint (f : Fin t → V) :
      (∑ e ∈ E, truth (e.image f ∈ G.edges)) ≤ (t.choose 3 : ℝ) - 1 := by
    have hbad : ∃ e ∈ E, e.image f ∉ G.edges := by
      by_contra h
      push Not at h
      exact hfree ⟨f, h⟩
    obtain ⟨e, he, hbad⟩ := hbad
    have hproper : E.filter (fun e => e.image f ∈ G.edges) ⊂ E := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have hin : e ∈ E.filter (fun e => e.image f ∈ G.edges) := heq.symm ▸ he
      exact hbad (Finset.mem_filter.mp hin).2
    have hc := Finset.card_lt_card hproper
    have hcard : E.card = t.choose 3 := by simp [E]
    rw [hcard] at hc
    have hc' : ((E.filter (fun e => e.image f ∈ G.edges)).card : ℝ) + 1 ≤
        (t.choose 3 : ℝ) := by exact_mod_cast hc
    have hsum : (∑ e ∈ E, truth (e.image f ∈ G.edges)) =
        ((E.filter (fun e => e.image f ∈ G.edges)).card : ℝ) := by
      calc
        (∑ e ∈ E, truth (e.image f ∈ G.edges)) =
            ∑ _e ∈ E.filter (fun e => e.image f ∈ G.edges), (1 : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _
          by_cases hd : d.image f ∈ G.edges <;> simp [truth, hd]
        _ = _ := by simp
    linarith
  have hmean := weightedMean_mono x hx.1 hpoint
  rw [weightedMean_const x hx.2, weightedMean_sum] at hmean
  have hsum : (∑ e ∈ E, weightedMean x (fun f : Fin t → V => truth (e.image f ∈ G.edges))) =
      (t.choose 3 : ℝ) * (6 * G.edgePolynomial x) := by
    calc
      (∑ e ∈ E, weightedMean x (fun f : Fin t → V => truth (e.image f ∈ G.edges))) =
          ∑ _e ∈ E, 6 * G.edgePolynomial x := by
        apply Finset.sum_congr rfl
        intro e he
        exact G.weightedMean_image_edge x hx.2 t e (Finset.mem_powersetCard.mp he).2
      _ = _ := by simp [E]
  rw [hsum] at hmean
  have hcpos : (0 : ℝ) < t.choose 3 := by exact_mod_cast Nat.choose_pos ht
  have hmean' : 6 * G.edgePolynomial x ≤ ((t.choose 3 : ℝ) - 1) / (t.choose 3 : ℝ) :=
    (le_div_iff₀ hcpos).mpr (by simpa [mul_comm] using hmean)
  have heq : ((t.choose 3 : ℝ) - 1) / (t.choose 3 : ℝ) =
      1 - 1 / (t.choose 3 : ℝ) := by field_simp
  simpa only [heq] using hmean'

theorem edgePolynomial_div {r : ℕ} (G : RGraph V r) (x : V → ℝ) (c : ℝ) :
    G.edgePolynomial (fun v => x v / c) = G.edgePolynomial x / c ^ r := by
  unfold edgePolynomial
  simp only [Finset.prod_div_distrib, Finset.prod_const]
  calc
    (∑ e ∈ G.edges, (∏ v ∈ e, x v) / c ^ e.card) =
        ∑ e ∈ G.edges, (∏ v ∈ e, x v) / c ^ r :=
      Finset.sum_congr rfl (fun e he => by rw [G.uniform e he])
    _ = _ := (Finset.sum_div _ _ _).symm

theorem clique_free_weighted_mass_bound (G : RGraph V 3) {t : ℕ} (ht : 3 ≤ t)
    (hfree : (clique (Fin t) 3).HomFree G) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * G.edgePolynomial x ≤ (1 - 1 / (t.choose 3 : ℝ)) * (∑ v, x v) ^ 3 := by
  have hmass : 0 ≤ ∑ v, x v := Finset.sum_nonneg fun v _ => hx v
  by_cases hz : ∑ v, x v = 0
  · have hxzero : x = fun _ => 0 := by
      funext v
      have hv := Finset.single_le_sum (fun v _ => hx v) (Finset.mem_univ v)
      exact le_antisymm (hz ▸ hv) (hx v)
    rw [hz, hxzero, G.edgePolynomial_uniform]
    norm_num
  · have hmasspos : 0 < ∑ v, x v := lt_of_le_of_ne hmass (Ne.symm hz)
    let y := fun v => x v / (∑ w, x w)
    have hy : ProbabilityWeights y := by
      refine ⟨fun v => div_nonneg (hx v) hmass, ?_⟩
      dsimp [y]
      rw [← Finset.sum_div, div_self hz]
    have h := G.clique_free_weighted_bound ht hfree y hy
    change 6 * G.edgePolynomial (fun v => x v / (∑ w, x w)) ≤ _ at h
    rw [G.edgePolynomial_div] at h
    apply (div_le_iff₀ (pow_pos hmasspos 3)).mp
    simpa only [mul_div_assoc] using h

theorem clique_deficit_lower {t : ℕ} (ht : 3 ≤ t) :
    6 / (t : ℝ) ^ 3 ≤ 1 / (t.choose 3 : ℝ) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hc0 : (0 : ℝ) < t.choose 3 := by exact_mod_cast Nat.choose_pos ht
  have h := Nat.choose_le_pow_div (α := ℝ) 3 t
  norm_num [Nat.factorial] at h
  apply (div_le_div_iff₀ (pow_pos ht0 3) hc0).mpr
  nlinarith

end TuranUniversality.RGraph
