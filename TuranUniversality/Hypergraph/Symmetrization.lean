module

public import TuranUniversality.Hypergraph.TwinPotential

@[expose] public section

/-! # Finite symmetrization by the actual clone potential

Every finite graph has a symmetrized graph on the same carrier, with at
least as many edges, which maps homomorphically back to the original. The
maximum argument is over the actual finite type of simple uniform graphs.
-/

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem exists_symmetrized_hom (G : RGraph V r) :
    ∃ H : RGraph V r, H.Symmetrized ∧ G.edges.card ≤ H.edges.card ∧
      ∃ f : V → V, H.IsHom G f := by
  classical
  let S := Finset.univ.filter (fun H : RGraph V r =>
    G.edges.card ≤ H.edges.card ∧ ∃ f : V → V, H.IsHom G f)
  have hG : G ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, le_rfl, id, G.isHom_id⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image S cloneScore ⟨G, hG⟩
  obtain ⟨hedges, f, hf⟩ := (Finset.mem_filter.mp hH).2
  refine ⟨H, ?_, hedges, f, hf⟩
  by_contra hn
  obtain ⟨u, v, _, _, he, hs⟩ := H.exists_clone_improvement hn
  have hc : H.clone u v ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hedges.trans he, f ∘ cloneMap u v,
      hf.comp (H.clone_isHom u v)⟩
  exact (not_lt_of_ge (hmax _ hc)) hs

end TuranUniversality.RGraph
