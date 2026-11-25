module

public import TuranUniversality.Hypergraph.VertexDeletion
public import TuranUniversality.Density.EditDistance
public import TuranUniversality.Density.WeightedHomPushforward
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

/-! # Finite profiles with repeated roles on an edge

An allowed edge is a multiset of roles. Repeated roles remain repeated:
this is more general than a blowup of a finite simple hypergraph.
-/

open Filter Topology

namespace TuranUniversality

structure FiniteRolePattern (R : Type*) (r : ℕ) where
  edges : Finset (Multiset R)
  uniform : ∀ m ∈ edges, m.card = r

namespace FiniteRolePattern

variable {R V W : Type*} [DecidableEq R] [DecidableEq V] [DecidableEq W]
variable [Fintype V] {r : ℕ}

def graph (P : FiniteRolePattern R r) (ρ : V → R) : RGraph V r where
  edges := (Finset.univ.powersetCard r).filter (fun e => e.val.map ρ ∈ P.edges)
  uniform e he := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_graph (P : FiniteRolePattern R r) (ρ : V → R) (e : Finset V) :
    e ∈ (P.graph ρ).edges ↔ e.card = r ∧ e.val.map ρ ∈ P.edges := by
  simp [graph]

theorem graph_agrees_on (P : FiniteRolePattern R r) (ρ σ : V → R)
    (S : Finset V) (h : ∀ v ∈ S, ρ v = σ v) :
    (P.graph ρ).keepVertices S = (P.graph σ).keepVertices S := by
  ext e
  simp only [RGraph.mem_keepVertices, mem_graph]
  by_cases he : e ⊆ S
  · have hm : e.val.map ρ = e.val.map σ :=
      Multiset.map_congr rfl (fun v hv => h v (he hv))
    simp only [he, hm]
  · simp only [he, and_false]

theorem edit_le_moved (P : FiniteRolePattern R r) (hr : 1 ≤ r)
    (hn : 0 < Fintype.card V) (ρ σ : V → R) :
    (P.graph ρ).normalizedEditDistance (P.graph σ) ≤
      2 * ((Finset.univ.filter (fun v => ρ v ≠ σ v)).card : ℝ) / Fintype.card V := by
  let S : Finset V := Finset.univ.filter (fun v => ρ v = σ v)
  have he := P.graph_agrees_on ρ σ S (fun v hv => (Finset.mem_filter.mp hv).2)
  have hs : Finset.univ \ S = Finset.univ.filter (fun v => ρ v ≠ σ v) := by
    ext v
    simp [S]
  have h1 := (P.graph ρ).keepVertices_edit_ratio_le hr hn S
  have h2 := (P.graph σ).keepVertices_edit_ratio_le hr hn S
  have ht := (P.graph ρ).normalizedEditDistance_triangle ((P.graph ρ).keepVertices S) (P.graph σ)
  have hc : ((P.graph σ).keepVertices S).normalizedEditDistance (P.graph σ) =
      (P.graph σ).normalizedEditDistance ((P.graph σ).keepVertices S) := by
    simp only [RGraph.normalizedEditDistance, RGraph.edgeSymmDifference_comm]
  rw [he, hc] at ht
  change (P.graph ρ).normalizedEditDistance ((P.graph ρ).keepVertices S) ≤ _ at h1
  change (P.graph σ).normalizedEditDistance ((P.graph σ).keepVertices S) ≤ _ at h2
  rw [hs] at h1 h2
  rw [he] at h1
  calc
    _ ≤ ((Finset.univ.filter (fun v => ρ v ≠ σ v)).card : ℝ) / Fintype.card V +
        ((Finset.univ.filter (fun v => ρ v ≠ σ v)).card : ℝ) / Fintype.card V :=
      ht.trans (add_le_add h1 h2)
    _ = _ := by ring

theorem map_eq_of_equiv (s : Finset V) (d : Finset W)
    (ρ : V → R) (σ : W → R) (e : s ≃ d) (he : ∀ v, ρ v.val = σ (e v).val) :
    s.val.map ρ = d.val.map σ := by
  apply Multiset.map_eq_map_of_bij_of_nodup ρ σ s.nodup d.nodup
    (fun v hv => (e ⟨v, hv⟩).val) (fun v hv => (e ⟨v, hv⟩).property)
  · intro v hv w hw h
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  · intro w hw
    obtain ⟨v, hv⟩ := e.surjective ⟨w, hw⟩
    exact ⟨v.val, v.property, congrArg Subtype.val hv⟩
  · intro v hv
    exact he ⟨v, hv⟩

omit [Fintype V] in
theorem fiber_card (a : Finset V) (f : V → R) (c : R) :
    Fintype.card {v : a // f v.val = c} = (a.filter (fun v => f v = c)).card := by
  classical
  let e : {v : a // f v.val = c} ≃ (a.filter (fun v => f v = c)) :=
    { toFun v := ⟨v.val.val, Finset.mem_filter.mpr ⟨v.val.property, v.property⟩⟩
      invFun v := ⟨⟨v.val, (Finset.mem_filter.mp v.property).1⟩,
        (Finset.mem_filter.mp v.property).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem exists_equiv_of_map_eq (s : Finset V) (d : Finset W)
    (ρ : V → R) (σ : W → R) (he : s.val.map ρ = d.val.map σ) :
    ∃ e : s ≃ d, ∀ v, ρ v.val = σ (e v).val := by
  classical
  have hc (c : R) : Fintype.card {v : s // ρ v.val = c} =
      Fintype.card {v : d // σ v.val = c} := by
    rw [fiber_card, fiber_card]
    have h := congrArg (Multiset.count c) he
    simpa only [Multiset.count_map, eq_comm (a := c), ← Finset.filter_val, Finset.card] using h
  let e := Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c))
  exact ⟨e, fun v => (Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hc c)) v).symm⟩

end FiniteRolePattern
end TuranUniversality
