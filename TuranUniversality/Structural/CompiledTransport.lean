module

public import TuranUniversality.Structural.Compiled
public import TuranUniversality.Structural.RecordTransport

@[expose] public section

/-! # Transporting actual compiled hypergraphs in the data coordinate -/

namespace TuranUniversality.Structural.Compiled

universe u v

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {b t : ℕ}

def mapData (f : V → W) : Vertex b t V → Vertex b t W := Sum.map id (Sum.map id f)

theorem mapData_injective (f : V ↪ W) : Function.Injective (@mapData V W b t f) :=
  Function.injective_id.sumMap (Function.injective_id.sumMap f.injective)

theorem mapData_eq_data (f : V → W) (u : Vertex b t V) (v : W) :
    mapData f u = .inr (.inr v) ↔ ∃ z : V, u = .inr (.inr z) ∧ f z = v := by
  cases u with
  | inl i => simp [mapData]
  | inr u => cases u <;> simp [mapData]

theorem image_edge_mapData (f : V → W) (Z : Finset (Support.Vertex b)) (X : Finset V) :
    (edge t Z X).image (mapData f) = edge t Z (X.image f) := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    cases u with
    | inl i => simp [mapData]
    | inr u =>
      cases u with
      | inl u => simpa [mapData] using hu
      | inr u =>
        simp only [mapData, Sum.map_inr, mem_edge_data] at hu ⊢
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · intro hv
    cases v with
    | inl i => exact Finset.mem_image.mpr ⟨.inl i, by simp, rfl⟩
    | inr v =>
      cases v with
      | inl v => exact Finset.mem_image.mpr ⟨.inr (.inl v), by simpa using hv, rfl⟩
      | inr v =>
        simp only [mem_edge_data] at hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨.inr (.inr u), by simpa using hu, rfl⟩

@[simp] theorem dataPart_edge (Z : Finset (Support.Vertex b)) (X : Finset V) :
    (edge t Z X).toRight.toRight = X := by
  ext v
  simp

theorem dataPart_image_mapData (f : V → W) (e : Finset (Vertex b t V)) :
    (e.image (mapData f)).toRight.toRight = e.toRight.toRight.image f := by
  ext v
  simp only [Finset.mem_toRight, Finset.mem_image, mapData_eq_data]
  constructor
  · rintro ⟨u, hu, z, rfl, hz⟩
    exact ⟨z, hu, hz⟩
  · rintro ⟨z, hz, hf⟩
    exact ⟨.inr (.inr z), hz, z, rfl, hf⟩

variable [Fintype V]

theorem mem_graph_pullback (Ω : Label → Finset (Cube.Word b)) (R : RecordSystem W)
    (f : V ↪ W) (e : Finset (Vertex b t V)) :
    e ∈ (graph t Ω (R.pullback f)).edges ↔
      e.image (mapData f) ∈ (graph t Ω R).edges := by
  constructor
  · intro he
    obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω (R.pullback f) e).mp he
    rw [image_edge_mapData]
    apply (mem_graph Ω R _).mpr
    refine ⟨X.image f, ?_, Z, ?_, rfl⟩
    · simpa only [Finset.map_eq_image] using (R.mem_pullback f X).mp hX
    · simpa only [RecordSystem.pullback, Finset.map_eq_image] using hZ
  · intro he
    obtain ⟨X, hX, Z, hZ, hz⟩ := (mem_graph Ω R _).mp he
    have hdata : e.toRight.toRight.image f = X := by
      have h := congrArg (fun d : Finset (Vertex b t W) => d.toRight.toRight) hz
      simpa only [dataPart_edge, dataPart_image_mapData] using h.symm
    have heq : edge t Z e.toRight.toRight = e := by
      apply Finset.image_injective (mapData_injective f)
      rw [image_edge_mapData, hdata]
      exact hz
    apply (mem_graph Ω (R.pullback f) e).mpr
    refine ⟨e.toRight.toRight, ?_, Z, ?_, heq⟩
    · apply (R.mem_pullback f _).mpr
      simpa only [Finset.map_eq_image, hdata] using hX
    · simpa only [RecordSystem.pullback, Finset.map_eq_image, hdata] using hZ

theorem legal_map_isHom {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Cube.Word b))
    [Fintype W] (O : LegalObject B V) (f : V ↪ W) :
    (graph t Ω O.records).IsHom (graph t Ω (O.map f).records) (mapData f) := by
  intro e he
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω O.records e).mp he
  rw [image_edge_mapData]
  have hc : X.card = 4 := (O.mem_records X).mp hX
  have hl : (O.map f).label (X.image f) = O.label X := by
    simpa only [Finset.map_eq_image] using O.map_label f X (le_of_eq hc)
  apply (mem_graph Ω (O.map f).records _).mpr
  refine ⟨X.image f, (LegalObject.mem_records _ _).mpr ?_, Z, ?_, rfl⟩
  · rw [Finset.card_image_of_injective _ f.injective, hc]
  · change Z ∈ (Support.poolGraph (Ω ((O.map f).label (X.image f)))).edges
    rw [hl]
    exact hZ

theorem records_map_isHom (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (f : V ↪ W) :
    (graph t Ω R).IsHom (graph t Ω (R.map f)) (mapData f) := by
  intro e he
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω R e).mp he
  rw [image_edge_mapData]
  have hl : (R.map f).label (X.image f) = R.label X := by
    simpa only [Finset.map_eq_image] using R.map_label f X
  apply (mem_graph Ω (R.map f) _).mpr
  refine ⟨X.image f, ?_, Z, ?_, rfl⟩
  · exact Finset.mem_image.mpr ⟨X, hX, Finset.map_eq_image f X⟩
  · rw [hl]
    exact hZ

end TuranUniversality.Structural.Compiled
