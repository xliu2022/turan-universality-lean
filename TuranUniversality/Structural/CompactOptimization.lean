module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! # Near equality at a unique maximum on a compact set

This is the compactness step used by both the scalar switch and the outer
root weights. It applies to arbitrary filters and finite-dimensional domains.
-/

open Filter Topology

namespace TuranUniversality.Structural

theorem tendsto_of_unique_value_on_compact
    {X I : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    (f : X → ℝ) (hf : Continuous f) (a : X) (c : ℝ)
    (hu : ∀ y ∈ s, f y = c → y = a)
    {l : Filter I} (u : I → X) (hm : ∀ᶠ i in l, u i ∈ s)
    (hv : Tendsto (fun i => f (u i)) l (𝓝 c)) : Tendsto u l (𝓝 a) := by
  apply hs.tendsto_nhds_of_unique_mapClusterPt hm
  intro y hy hcluster
  apply hu y hy
  have hc := hcluster.continuousAt_comp hf.continuousAt
  exact eq_of_nhds_neBot (hc.clusterPt.mono hv)

end TuranUniversality.Structural
