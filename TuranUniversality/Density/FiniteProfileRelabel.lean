module

public import TuranUniversality.Density.FiniteProfiles
public import TuranUniversality.Hypergraph.PartitionRounding

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Relabelling a finite multiset profile

The independent public statement uses numbered roles. Relabelling changes
neither any realized graph nor its full hom-density profile.
-/

namespace TuranUniversality.FiniteRolePattern

open Density

variable {R S V : Type*} [DecidableEq R] [DecidableEq S] [DecidableEq V]
variable {r : ℕ}

def relabel (P : FiniteRolePattern R r) (e : R ≃ S) : FiniteRolePattern S r where
  edges := P.edges.image (fun m => m.map e)
  uniform m hm := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    simpa using P.uniform n hn

@[simp] theorem mem_relabel_map (P : FiniteRolePattern R r) (e : R ≃ S)
    (m : Multiset R) : m.map e ∈ (P.relabel e).edges ↔ m ∈ P.edges := by
  change m.map e ∈ P.edges.image (fun n => n.map e) ↔ _
  constructor
  · rintro h
    obtain ⟨n, hn, hnm⟩ := Finset.mem_image.mp h
    have heq : n = m := Multiset.map_injective e.injective hnm
    simpa only [heq] using hn
  · intro h
    exact Finset.mem_image.mpr ⟨m, h, rfl⟩

theorem graph_relabel [Fintype V] (P : FiniteRolePattern R r) (e : R ≃ S)
    (ρ : V → R) : (P.relabel e).graph (e ∘ ρ) = P.graph ρ := by
  ext d
  simp only [mem_graph, ← Multiset.map_map, mem_relabel_map]

theorem compatible_relabel [Fintype V] (P : FiniteRolePattern R r) (e : R ≃ S)
    (H : RGraph V r) (θ : V → R) :
    (P.relabel e).Compatible H (e ∘ θ) ↔ P.Compatible H θ := by
  unfold Compatible
  simp only [← Multiset.map_map, mem_relabel_map]

theorem coordinate_relabel [Fintype R] [Fintype S] [Fintype V]
    (P : FiniteRolePattern R r) (e : R ≃ S) (H : RGraph V r) (z : R → ℝ) :
    (P.relabel e).coordinate H (pushforwardWeight e z) = P.coordinate H z := by
  unfold coordinate
  rw [← weightedMean_pushforward e z]
  apply weightedMean_congr
  intro θ
  rw [P.compatible_relabel e H θ]

theorem profile_relabel [Fintype R] [Fintype S]
    (P : FiniteRolePattern R r) (e : R ≃ S) (z : R → ℝ) :
    (P.relabel e).profile (pushforwardWeight e z) = P.profile z := by
  funext H
  exact coordinate_relabel P e H.2 z

theorem pushforward_equiv [Fintype R] (e : R ≃ S) (z : R → ℝ) (s : S) :
    pushforwardWeight e z s = z (e.symm s) := by
  classical
  let a : {a : R // e a = s} := ⟨e.symm s, e.apply_symm_apply s⟩
  have hsingle : (Finset.univ : Finset {a : R // e a = s}) = {a} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    exact e.injective (x.property.trans (e.apply_symm_apply s).symm)
  simp only [pushforwardWeight, hsingle, Finset.sum_singleton, a]

theorem fiberSize_relabel [Fintype V] (e : R ≃ S) (ρ : V → R) (s : S) :
    PartitionRounding.fiberSize (e ∘ ρ) s = PartitionRounding.fiberSize ρ (e.symm s) := by
  unfold PartitionRounding.fiberSize
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  exact e.apply_eq_iff_eq_symm_apply

end TuranUniversality.FiniteRolePattern
