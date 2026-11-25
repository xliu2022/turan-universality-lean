module

public import TuranUniversality.Density.HomDensity
public import TuranUniversality.Hypergraph.Polynomial
public import Mathlib.Data.Fintype.Perm

@[expose] public section

/-! # Edge density and the edge polynomial have the usual normalization -/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Selector Density

universe u
variable {V : Type u} [DecidableEq V] {r : ℕ}

/-- A single r-edge on its r labeled vertices. -/
def oneEdge (r : ℕ) : RGraph (Fin r) r where
  edges := {Finset.univ}
  uniform e he := by
    rw [Finset.mem_singleton] at he
    rw [he]
    exact Finset.card_fin r

@[simp] theorem oneEdge_isHom (G : RGraph V r) (f : Fin r → V) :
    (oneEdge r).IsHom G f ↔ Finset.univ.image f ∈ G.edges := by
  simp [oneEdge, IsHom]

/-- An ordering of an actual edge of G. -/
abbrev EdgeOrdering (G : RGraph V r) := Σ e : G.edges, Fin r ≃ e.val

def orderingFunction (G : RGraph V r) (p : EdgeOrdering G) : Fin r → V :=
  fun j => (p.2 j).val

theorem orderingFunction_image (G : RGraph V r) (p : EdgeOrdering G) :
    Finset.univ.image (G.orderingFunction p) = p.1.val := by
  ext v
  constructor
  · rintro hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (p.2 j).property
  · intro hv
    obtain ⟨j, hj⟩ := p.2.surjective ⟨v, hv⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩

def orderedEdgeMap (G : RGraph V r) (p : EdgeOrdering G) :
    {f : Fin r → V // (oneEdge r).IsHom G f} :=
  ⟨G.orderingFunction p, (G.oneEdge_isHom _).mpr (G.orderingFunction_image p ▸ p.1.property)⟩

theorem orderedEdgeMap_bijective (G : RGraph V r) :
    Function.Bijective G.orderedEdgeMap := by
  classical
  constructor
  · intro p q hpq
    have hf : G.orderingFunction p = G.orderingFunction q := congrArg Subtype.val hpq
    have he : p.1 = q.1 := Subtype.ext (by
      rw [← G.orderingFunction_image p, ← G.orderingFunction_image q, hf])
    cases p with
    | mk e a =>
      cases q with
      | mk e' b =>
        dsimp only at he
        subst e'
        congr 1
        apply Equiv.ext
        intro j
        exact Subtype.ext (congrFun hf j)
  · intro f
    let e : G.edges := ⟨Finset.univ.image f.val, (G.oneEdge_isHom _).mp f.property⟩
    have hi : Function.Injective f.val := by
      have hcard : (Finset.univ.image f.val).card = (Finset.univ : Finset (Fin r)).card := by
        rw [G.uniform _ e.property, Finset.card_fin]
      have hinj := Finset.card_image_iff.mp hcard
      intro a b hab
      exact hinj (Finset.mem_univ _) (Finset.mem_univ _) hab
    let g : Fin r → e.val := fun j => ⟨f.val j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact hi (congrArg Subtype.val hab)
      · intro v
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp v.property
        exact ⟨j, Subtype.ext hj⟩
    refine ⟨⟨e, Equiv.ofBijective g hg⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem card_ordered_homs [Fintype V] (G : RGraph V r) :
    Fintype.card {f : Fin r → V // (oneEdge r).IsHom G f} =
      G.edges.card * r.factorial := by
  classical
  rw [← Fintype.card_congr (Equiv.ofBijective G.orderedEdgeMap G.orderedEdgeMap_bijective),
    Fintype.card_sigma]
  have hc (e : G.edges) : Fintype.card (Fin r ≃ e.val) = r.factorial := by
    have he : Fintype.card (Fin r) = Fintype.card e.val := by
      simp [G.uniform _ e.property]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq he), Fintype.card_fin]
  simp_rw [hc]
  simp

/-- Homomorphism density of a single edge equals r!|E|/n^r. -/
theorem oneEdge_homDensity [Fintype V] (G : RGraph V r) :
    (oneEdge r).homDensity G =
      (r.factorial : ℝ) * G.edges.card / (Fintype.card V : ℝ) ^ r := by
  classical
  unfold homDensity homIndicator
  rw [mean_eq_sum_div_card]
  simp only [Finset.sum_boole, ← Fintype.card_subtype, G.card_ordered_homs,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  ring

theorem oneEdge_homDensity_polynomial [Fintype V] (G : RGraph V r) :
    (oneEdge r).homDensity G =
      (r.factorial : ℝ) * G.edgePolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) := by
  rw [G.oneEdge_homDensity, G.edgePolynomial_uniform]
  simp [div_eq_mul_inv, mul_assoc]

end TuranUniversality.RGraph
