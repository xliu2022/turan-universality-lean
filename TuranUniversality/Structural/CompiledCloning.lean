module

public import TuranUniversality.Structural.CompiledTransport
public import TuranUniversality.Structural.RecordCloning

@[expose] public section

/-! # Exact compiled-edge reflection under arbitrary data cloning -/

namespace TuranUniversality.Structural.Compiled

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {b t : ℕ}

@[simp] theorem mem_image_mapData_susp (f : V → W) (e : Finset (Vertex b t V)) (i : Fin t) :
    Sum.inl i ∈ e.image (mapData f) ↔ Sum.inl i ∈ e := by
  simp [Finset.mem_image, mapData, Sum.exists]

@[simp] theorem mem_image_mapData_block (f : V → W) (e : Finset (Vertex b t V))
    (i : Support.Vertex b) :
    Sum.inr (Sum.inl i) ∈ e.image (mapData f) ↔ Sum.inr (Sum.inl i) ∈ e := by
  simp [Finset.mem_image, mapData, Sum.exists]

theorem eq_edge_of_image_mapData (f : V → W) (e : Finset (Vertex b t V))
    (Z : Finset (Support.Vertex b)) (X : Finset W)
    (he : e.image (mapData f) = edge t Z X) :
    e = edge t Z e.toRight.toRight := by
  ext v
  rcases v with i | (v | v)
  · have h : Sum.inl i ∈ e.image (mapData f) := by rw [he]; simp
    simp only [mem_edge_susp, iff_true]
    exact (mem_image_mapData_susp f e i).mp h
  · have h := Finset.ext_iff.mp he (Sum.inr (Sum.inl v))
    simpa only [mem_image_mapData_block, mem_edge_block] using h
  · simp

variable [Fintype V]

theorem mem_graph_clone (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem W)
    (f : V → W) (e : Finset (Vertex b t V)) :
    e ∈ (graph t Ω (R.clone f)).edges ↔
      e.card = t + (3 * b + 4) ∧ e.image (mapData f) ∈ (graph t Ω R).edges := by
  constructor
  · intro he
    refine ⟨(graph t Ω (R.clone f)).uniform e he, ?_⟩
    obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω (R.clone f) e).mp he
    rw [image_edge_mapData]
    exact (mem_graph Ω R _).mpr ⟨X.image f, ((R.mem_clone f X).mp hX).2, Z, hZ, rfl⟩
  · rintro ⟨hc, he⟩
    obtain ⟨X, hX, Z, hZ, hz⟩ := (mem_graph Ω R _).mp he
    have hdata : e.toRight.toRight.image f = X := by
      have h := congrArg (fun d : Finset (Vertex b t W) => d.toRight.toRight) hz
      simpa only [dataPart_edge, dataPart_image_mapData] using h.symm
    have heq := eq_edge_of_image_mapData f e Z X hz.symm
    have hcard : e.toRight.toRight.card = 4 := by
      have hcZ := (Support.poolGraph (Ω (R.label X))).uniform Z hZ
      rw [heq, edge_card, hcZ] at hc
      omega
    apply (mem_graph Ω (R.clone f) e).mpr
    refine ⟨e.toRight.toRight, (R.mem_clone f _).mpr ⟨hcard, hdata ▸ hX⟩, Z, ?_, heq.symm⟩
    change Z ∈ (Support.poolGraph (Ω (R.label (e.toRight.toRight.image f)))).edges
    rwa [hdata]

theorem clone_isHom (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem W) (f : V → W) :
    (graph t Ω (R.clone f)).IsHom (graph t Ω R) (mapData f) :=
  fun e he => ((mem_graph_clone Ω R f e).mp he).2

end TuranUniversality.Structural.Compiled
