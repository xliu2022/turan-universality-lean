module

public import TuranUniversality.Structural.NeutralRoles
public import TuranUniversality.Hypergraph.FiniteProfiles
public import TuranUniversality.Structural.RootedLocal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The fixed neutral model as a finite multiset profile

Every allowed multiset has all suspension roles, one support from the
neutral word pool, and four copies of the single neutral role. The finite
ordinary realization is exactly the actual all-neutral compiled model.
-/

namespace TuranUniversality.Structural.NeutralRoles

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable [Fintype V] {b t : ℕ}

def collapse : Compiled.Vertex b t V → Role b t
  | .inl i => .inl (.inl i)
  | .inr (.inl j) => .inl (.inr j)
  | .inr (.inr _) => .inr ()

@[simp] theorem collapse_sampleVertex (a : Role b t) (v : V) :
    collapse (sampleVertex (a, v)) = a := by
  rcases a with (i | j) | a
  · rfl
  · rfl
  · cases a; rfl

@[simp] theorem collapse_mapData (f : V → W) (v : Compiled.Vertex b t V) :
    collapse (Compiled.mapData f v) = collapse v := by
  rcases v with i | (j | v) <;> rfl

def compiledNeutral (Ω : Label → Finset (Cube.Word b)) (V : Type*)
    [DecidableEq V] [Fintype V] : RGraph (Compiled.Vertex b t V) (t + (3 * b + 4)) :=
  Compiled.graph t Ω (object ∅ (by simp) : LegalObject ∅ V).records

theorem mem_compiledNeutral (Ω : Label → Finset (Cube.Word b))
    (e : Finset (Compiled.Vertex b t V)) :
    e ∈ (compiledNeutral (t := t) Ω V).edges ↔
      ∃ X : Finset V, X.card = 4 ∧ ∃ Z ∈ (Support.poolGraph (Ω (.inl 0))).edges,
        Compiled.edge t Z X = e := by
  simp [compiledNeutral, Compiled.mem_graph, LegalObject.records,
    object, LegalObject.empty, LegalObject.label, RGraph.empty]

def graph (Ω : Label → Finset (Cube.Word b)) (θ : V → Role b t) :
    RGraph V (t + (3 * b + 4)) :=
  (compiledNeutral Ω V).inverseImage (fun v => sampleVertex (θ v, v))

def roleOfRooting (ρ : V → Option (Rooted.Roots b t)) : V → Role b t :=
  fun v => match ρ v with
    | some r => .inl r
    | none => .inr ()

theorem sample_roleOfRooting (ρ : V → Option (Rooted.Roots b t)) (v : V) :
    sampleVertex (roleOfRooting ρ v, v) = Rooted.place ρ v := by
  cases h : ρ v with
  | none => simp [roleOfRooting, h, sampleVertex, Rooted.place_none ρ h]
  | some r => cases r <;> simp [roleOfRooting, h, sampleVertex,
      PhaseRoles.rootVertex, Rooted.place_root ρ h]

theorem graph_roleOfRooting (Ω : Label → Finset (Cube.Word b))
    (ρ : V → Option (Rooted.Roots b t)) :
    graph Ω (roleOfRooting ρ) = (compiledNeutral Ω V).inverseImage (Rooted.place ρ) := by
  simp only [graph, sample_roleOfRooting]

def edgePattern (Z : Finset (Support.Vertex b)) : Multiset (Role b t) :=
  (Compiled.edge t Z (Finset.univ : Finset (Fin 4))).val.map collapse

def pattern (Ω : Label → Finset (Cube.Word b)) : FiniteRolePattern (Role b t) (t + (3 * b + 4)) where
  edges := (Support.poolGraph (Ω (.inl 0))).edges.image edgePattern
  uniform := by
    intro m hm
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hm
    simp only [edgePattern, Multiset.card_map]
    change (Compiled.edge t Z (Finset.univ : Finset (Fin 4))).card = _
    simp only [Compiled.edge_card, Finset.card_univ, Fintype.card_fin,
      (Support.poolGraph _).uniform Z hZ]

theorem compiled_edge_pattern (Z : Finset (Support.Vertex b)) (X : Finset V) (hX : X.card = 4) :
    (Compiled.edge t Z X).val.map collapse = edgePattern (t := t) Z := by
  classical
  let a : Fin 4 ≃ X := Fintype.equivOfCardEq (by simp [hX])
  let f : Fin 4 ↪ V := a.toEmbedding.trans (Function.Embedding.subtype _)
  have hf : Finset.univ.image f = X := by
    ext v
    constructor
    · rintro hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact (a j).property
    · intro hv
      obtain ⟨j, hj⟩ := a.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  have him : (Compiled.edge t Z (Finset.univ : Finset (Fin 4))).image
      (Compiled.mapData f) = Compiled.edge t Z X := by
    rw [Compiled.image_edge_mapData, hf]
  rw [← him, Finset.image_val_of_injOn (Compiled.mapData_injective f).injOn,
    Multiset.map_map]
  simp only [Function.comp_def, collapse_mapData, edgePattern]

theorem edge_of_role_equiv (Ω : Label → Finset (Cube.Word b))
    (θ : V → Role b t) (e : Finset V) (Z : Finset (Support.Vertex b))
    (hZ : Z ∈ (Support.poolGraph (Ω (.inl 0))).edges)
    (a : e ≃ Compiled.edge t Z (Finset.univ : Finset (Fin 4)))
    (ha : ∀ v, θ v.val = collapse (a v).val) :
    e.image (fun v => sampleVertex (θ v, v)) ∈ (compiledNeutral Ω V).edges := by
  let d (j : Fin 4) : Compiled.edge t Z (Finset.univ : Finset (Fin 4)) :=
    ⟨.inr (.inr j), by simp⟩
  let i : Fin 4 ↪ V :=
    ⟨fun j => (a.symm (d j)).val, by
      intro j k hjk
      have h := congrArg Subtype.val (a.symm.injective (Subtype.ext hjk))
      simpa only [d, Sum.inr.injEq] using h⟩
  have hm (v : e) : sampleVertex (θ v.val, v.val) = Compiled.mapData i (a v).val := by
    cases h : (a v).val with
    | inl j => simp [ha v, h, collapse, sampleVertex, PhaseRoles.rootVertex, Compiled.mapData]
    | inr w =>
      cases w with
      | inl j => simp [ha v, h, collapse, sampleVertex, PhaseRoles.rootVertex, Compiled.mapData]
      | inr j =>
        have he : a v = d j := Subtype.ext h
        have hi : i j = v.val := by
          change (a.symm (d j)).val = v.val
          rw [← he, a.symm_apply_apply]
        simp [ha v, h, collapse, sampleVertex, Compiled.mapData, hi]
  have heq : e.image (fun v => sampleVertex (θ v, v)) =
      (Compiled.edge t Z (Finset.univ : Finset (Fin 4))).image (Compiled.mapData i) := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr ⟨(a ⟨v, hv⟩).val, (a ⟨v, hv⟩).property, (hm ⟨v, hv⟩).symm⟩
    · intro hw
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hw
      subst w
      let v := a.symm ⟨u, hu⟩
      refine Finset.mem_image.mpr ⟨v.val, v.property, ?_⟩
      simpa only [v, a.apply_symm_apply] using hm v
  rw [heq, Compiled.image_edge_mapData, mem_compiledNeutral]
  exact ⟨Finset.univ.image i, by simp [Finset.card_image_of_injective _ i.injective], Z, hZ, rfl⟩

theorem graph_eq_pattern (Ω : Label → Finset (Cube.Word b)) (θ : V → Role b t) :
    graph Ω θ = (pattern Ω).graph θ := by
  classical
  ext e
  rw [graph, RGraph.mem_inverseImage, FiniteRolePattern.mem_graph]
  constructor
  · rintro ⟨hc, he⟩
    have hi : Set.InjOn (fun v => sampleVertex (θ v, v)) e :=
      Finset.injOn_of_card_image_eq (((compiledNeutral Ω V).uniform _ he).trans hc.symm)
    obtain ⟨X, hX, Z, hZ, hz⟩ := (mem_compiledNeutral Ω _).mp he
    refine ⟨hc, Finset.mem_image.mpr ⟨Z, hZ, ?_⟩⟩
    have hm := congrArg (fun d : Finset (Compiled.Vertex b t V) => d.val.map collapse) hz
    rw [compiled_edge_pattern Z X hX, Finset.image_val_of_injOn hi, Multiset.map_map] at hm
    simpa only [Function.comp_def, collapse_sampleVertex] using hm
  · rintro ⟨hc, he⟩
    obtain ⟨Z, hZ, hz⟩ := Finset.mem_image.mp he
    obtain ⟨a, ha⟩ := FiniteRolePattern.exists_equiv_of_map_eq e
      (Compiled.edge t Z (Finset.univ : Finset (Fin 4))) θ collapse hz.symm
    exact ⟨hc, edge_of_role_equiv Ω θ e Z hZ a ha⟩

end TuranUniversality.Structural.NeutralRoles
