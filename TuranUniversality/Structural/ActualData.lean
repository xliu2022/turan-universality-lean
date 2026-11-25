module

public import TuranUniversality.Structural.LegalOrdinaryApproximation
public import TuranUniversality.Structural.PhaseInnerProfiles

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Removing zero-weight copies of ordinary root vertices from the data

A canonical quotient retains the original carrier as its data type. The
root-assigned vertices have zero data weight. Restricting the repaired
object to the actual data set preserves both its finite realization and
its weighted inner density.
-/

open scoped BigOperators

namespace TuranUniversality.Structural

namespace Rooted

open Density

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def ordinaryData (ρ : V → Option (Roots b t)) : Finset V :=
  Finset.univ.filter (fun v => ρ v = none)

@[simp] theorem mem_ordinaryData (ρ : V → Option (Roots b t)) (v : V) :
    v ∈ ordinaryData ρ ↔ ρ v = none := by simp [ordinaryData]

theorem dataWeight_pushforward (ρ : V → Option (Roots b t)) (x : V → ℝ) (v : V) :
    Compiled.dataWeight (pushforwardWeight (place ρ) x) v =
      if ρ v = none then x v else 0 := by
  simp only [Compiled.dataWeight, pushforwardWeight_eq_sum_ite, place_eq_data, ite_and]
  simp

theorem data_of_image_edge (ρ : V → Option (Roots b t)) (e X : Finset V)
    (Z : Finset (Support.Vertex b))
    (he : e.image (place ρ) = Compiled.edge t Z X) : X ⊆ ordinaryData ρ := by
  intro v hv
  have hm : Sum.inr (Sum.inr v) ∈ e.image (place ρ) := by
    rw [he]
    simpa using hv
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hm
  obtain ⟨rfl, hn⟩ := (place_eq_data ρ u v).mp hu
  exact (mem_ordinaryData ρ u).mpr hn

end Rooted

namespace LegalObject

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {B : Finset (FiniteGraph 3)} {b t : ℕ}

theorem restrict_label (O : LegalObject B V) (S X : Finset V)
    (hX : X.card ≤ 4) (hXS : X ⊆ S) : (O.restrict S).label X = O.label X := by
  exact ((O.restrict S).labels_iff X hX _).mp
    ((O.restrict_labels S X hXS _).mpr (O.labels_label X hX))

theorem restrict_data_realization (O : LegalObject B V)
    (Ω : Label → Finset (Cube.Word b)) (ρ : V → Option (Rooted.Roots b t)) :
    (Compiled.graph t Ω (O.restrict (Rooted.ordinaryData ρ)).records).inverseImage (Rooted.place ρ) =
      (Compiled.graph t Ω O.records).inverseImage (Rooted.place ρ) := by
  ext e
  simp only [RGraph.mem_inverseImage]
  constructor
  · rintro ⟨hc, hm⟩
    obtain ⟨X, hX, Z, hZ, he⟩ := (Compiled.mem_graph Ω (O.restrict _).records _).mp hm
    have hXcard := ((O.restrict _).mem_records X).mp hX
    refine ⟨hc, (Compiled.mem_graph Ω O.records _).mpr
      ⟨X, (O.mem_records X).mpr hXcard, Z, ?_, he⟩⟩
    have hXS := Rooted.data_of_image_edge ρ e X Z he.symm
    change Z ∈ (Support.poolGraph (Ω (O.label X))).edges
    simpa only [records, O.restrict_label _ X hXcard.le hXS] using hZ
  · rintro ⟨hc, hm⟩
    obtain ⟨X, hX, Z, hZ, he⟩ := (Compiled.mem_graph Ω O.records _).mp hm
    have hXcard := (O.mem_records X).mp hX
    refine ⟨hc, (Compiled.mem_graph Ω (O.restrict _).records _).mpr
      ⟨X, ((O.restrict _).mem_records X).mpr hXcard, Z, ?_, he⟩⟩
    have hXS := Rooted.data_of_image_edge ρ e X Z he.symm
    change Z ∈ (Support.poolGraph (Ω ((O.restrict _).label X))).edges
    rw [O.restrict_label _ X hXcard.le hXS]
    exact hZ

theorem restrict_activeMass (O : LegalObject B V) (S : Finset V) (x : V → ℝ)
    (hx : ∀ v ∉ S, x v = 0) : (O.restrict S).activeMass x = O.activeMass x := by
  change (∑ v ∈ O.active ∩ S, x v) = ∑ v ∈ O.active, x v
  apply Finset.sum_subset Finset.inter_subset_left
  intro v hv hn
  exact hx v (fun hs => hn (Finset.mem_inter.mpr ⟨hv, hs⟩))

theorem restrict_projection_polynomial (O : LegalObject B V) (S : Finset V) (x : V → ℝ)
    (hx : ∀ v ∉ S, x v = 0) :
    (O.restrict S).projection.edgePolynomial x = O.projection.edgePolynomial x := by
  have he : (O.restrict S).projection.edges = O.projection.edges.filter (· ⊆ S) := by
    ext e
    simp only [mem_projection, restrict, Finset.mem_filter]
    tauto
  unfold RGraph.edgePolynomial
  rw [he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hS : e ⊆ S
  · simp only [hS, ite_true]
  · simp only [hS, ite_false]
    symm
    obtain ⟨v, hv, hnv⟩ := Finset.not_subset.mp hS
    exact Finset.prod_eq_zero hv (hx v hnv)

theorem restrict_innerDensity (O : LegalObject B V) (S : Finset V) (x : V → ℝ)
    (hx : ∀ v ∉ S, x v = 0) : (O.restrict S).innerDensity x = O.innerDensity x := by
  simp only [innerDensity, O.restrict_projection_polynomial S x hx, O.restrict_activeMass S x hx]

theorem active_constant_innerDensity (O : LegalObject B V) (x : V → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hx : ∀ v ∈ O.active, x v = c) :
    (RGraph.oneEdge 3).homDensity O.activeProjection = O.innerDensity x := by
  have hm : O.activeMass x = O.active.card * c := by
    unfold activeMass
    simp_rw [Finset.sum_congr rfl (fun v hv => hx v hv)]
    simp
  have hp : O.projection.edgePolynomial x = O.activeProjection.edgePolynomial (fun _ => c) := by
    rw [← O.activeProjection_polynomial]
    congr 1
    funext v
    exact hx v.val v.property
  rw [RGraph.oneEdge_homDensity_polynomial, innerDensity, hp, hm,
    RGraph.edgePolynomial_uniform, RGraph.edgePolynomial_uniform]
  norm_num only [Nat.factorial, Fintype.card_coe]
  rw [mul_pow]
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]
  ring_nf
  field_simp [hc]

end LegalObject
end TuranUniversality.Structural
