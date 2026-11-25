module

public import TuranUniversality.Structural.CompiledTransport
public import TuranUniversality.Density.Sampling

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual finite role models for the phase-coordinate expansion

For a fixed outer test, assign each source vertex a root role, an active
role, or a neutral role. An ordinary finite inner test graph then determines
a genuine complete record system on the data positions. Compatibility is
an actual homomorphism into its compiled hypergraph, not a formal label.
-/

namespace TuranUniversality.Structural.PhaseRoles

variable {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] {b t : ℕ}

abbrev Root (b t : ℕ) := Fin t ⊕ Support.Vertex b
abbrev Role (b t : ℕ) := Root b t ⊕ Bool

def dataSet (θ : U → Role b t) : Finset U :=
  Finset.univ.filter (fun u => ∃ a : Bool, θ u = .inr a)

abbrev Data (θ : U → Role b t) := dataSet θ

@[simp] theorem mem_dataSet (θ : U → Role b t) (u : U) :
    u ∈ dataSet θ ↔ ∃ a : Bool, θ u = .inr a := by simp [dataSet]

def activeSet (θ : U → Role b t) : Finset (Data θ) :=
  Finset.univ.filter (fun u => θ u.val = .inr false)

@[simp] theorem mem_activeSet (θ : U → Role b t) (u : Data θ) :
    u ∈ activeSet θ ↔ θ u.val = .inr false := by simp [activeSet]

def rootVertex (j : Root b t) : Compiled.Vertex b t V :=
  match j with
  | .inl i => .inl i
  | .inr v => .inr (.inl v)

def place (θ : U → Role b t) (u : U) : Compiled.Vertex b t (Data θ) :=
  match h : θ u with
  | .inl j => rootVertex j
  | .inr a => .inr (.inr ⟨u, (mem_dataSet θ u).mpr ⟨a, h⟩⟩)

def innerGraph (θ : U → Role b t) (K : RGraph U 3) : RGraph (Data θ) 3 where
  edges := (K.pullback (Function.Embedding.subtype _)).edges.filter (· ⊆ activeSet θ)
  uniform e he := (K.pullback _).uniform e (Finset.mem_filter.mp he).1

theorem mem_innerGraph (θ : U → Role b t) (K : RGraph U 3) (e : Finset (Data θ)) :
    e ∈ (innerGraph θ K).edges ↔
      e.map (Function.Embedding.subtype _) ∈ K.edges ∧ e ⊆ activeSet θ := by
  rw [innerGraph, Finset.mem_filter, RGraph.mem_pullback]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · rintro ⟨he, hs⟩
    exact ⟨⟨by simpa using K.uniform _ he, he⟩, hs⟩

def object (θ : U → Role b t) (phase : Bool) (K : RGraph U 3) :
    LegalObject ∅ (Data θ) where
  active := activeSet θ
  inner a := if a = phase then innerGraph θ K else RGraph.empty _ 3
  supported := by
    intro a e he
    by_cases ha : a = phase
    · simpa only [if_pos ha] using ((mem_innerGraph θ K e).mp (by simpa [ha] using he)).2
    · simpa [ha, RGraph.empty] using he
  onePhase := by
    cases phase
    · exact Or.inr (by simp [RGraph.empty])
    · exact Or.inl (by simp [RGraph.empty])
  free := by simp

def Compatible (Ω : Label → Finset (Cube.Word b)) (phase : Bool)
    (H : RGraph U (t + (3 * b + 4))) (θ : U → Role b t) (K : RGraph U 3) : Prop :=
  H.IsHom (Compiled.graph t Ω (object θ phase K).records) (place θ)

variable {B : Finset (FiniteGraph 3)}

/-- Finite relation preservation suffices to identify every actual record.
The hypothesis refers only to the inner three-edge relation. -/
theorem object_label (θ : U → Role b t) (phase : Bool) (K : RGraph U 3)
    (O : LegalObject B V) (i : Data θ ↪ V)
    (ha : ∀ u, i u ∈ O.active ↔ u ∈ activeSet θ)
    (hphase : ∀ a, a ≠ phase → (O.inner a).edges = ∅)
    (hK : ∀ e : Finset (Data θ), e ⊆ activeSet θ →
      (e.map (Function.Embedding.subtype _) ∈ K.edges ↔ e.map i ∈ (O.inner phase).edges))
    (X : Finset (Data θ)) (hX : X.card ≤ 4) :
    (object θ phase K).label X = O.label (X.map i) := by
  have hactive : (object θ phase K).active = (O.pullback i).active := by
    ext u
    simp only [object, LegalObject.mem_pullback_active]
    exact (ha u).symm
  have hinner (a : Bool) : (object θ phase K).inner a = (O.pullback i).inner a := by
    apply RGraph.ext
    ext e
    rw [O.mem_pullback_inner]
    by_cases hp : a = phase
    · subst a
      simp only [object, if_pos]
      rw [mem_innerGraph]
      constructor
      · rintro ⟨he, hs⟩
        exact (hK e hs).mp he
      · intro he
        have hs : e ⊆ activeSet θ := by
          intro u hu
          exact (ha u).mp (O.supported phase _ he (Finset.mem_map.mpr ⟨u, hu, rfl⟩))
        exact ⟨(hK e hs).mpr he, hs⟩
    · simp [object, hp, hphase a hp, RGraph.empty]
  calc
    (object θ phase K).label X = (O.pullback i).label X := by
      simp only [LegalObject.label, hactive, hinner]
    _ = _ := O.pullback_label i X hX

theorem graph_object (θ : U → Role b t) (phase : Bool) (K : RGraph U 3)
    (O : LegalObject B V) [Fintype V] (i : Data θ ↪ V)
    (ha : ∀ u, i u ∈ O.active ↔ u ∈ activeSet θ)
    (hphase : ∀ a, a ≠ phase → (O.inner a).edges = ∅)
    (hK : ∀ e : Finset (Data θ), e ⊆ activeSet θ →
      (e.map (Function.Embedding.subtype _) ∈ K.edges ↔ e.map i ∈ (O.inner phase).edges))
    (Ω : Label → Finset (Cube.Word b)) :
    Compiled.graph t Ω (object θ phase K).records =
      Compiled.graph t Ω (O.records.pullback i) := by
  apply RGraph.ext
  ext e
  rw [Compiled.mem_graph, Compiled.mem_graph]
  have hm (X : Finset (Data θ)) : X ∈ (O.records.pullback i).recorded.edges ↔ X.card = 4 := by
    rw [RecordSystem.mem_pullback, LegalObject.mem_records, Finset.card_map]
  simp only [LegalObject.mem_records, hm]
  constructor <;> rintro ⟨X, hX, Z, hZ, he⟩ <;> refine ⟨X, hX, Z, ?_, he⟩
  · change Z ∈ (Support.poolGraph (Ω (O.label (X.map i)))).edges
    rw [← object_label θ phase K O i ha hphase hK X hX.le]
    exact hZ
  · change Z ∈ (Support.poolGraph (Ω ((object θ phase K).label X))).edges
    rw [object_label θ phase K O i ha hphase hK X hX.le]
    exact hZ

theorem compatible_iff (θ : U → Role b t) (phase : Bool) (K : RGraph U 3)
    (O : LegalObject B V) [Fintype V] (i : Data θ ↪ V)
    (ha : ∀ u, i u ∈ O.active ↔ u ∈ activeSet θ)
    (hphase : ∀ a, a ≠ phase → (O.inner a).edges = ∅)
    (hK : ∀ e : Finset (Data θ), e ⊆ activeSet θ →
      (e.map (Function.Embedding.subtype _) ∈ K.edges ↔ e.map i ∈ (O.inner phase).edges))
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    Compatible Ω phase H θ K ↔
      H.IsHom (Compiled.graph t Ω O.records) (Compiled.mapData i ∘ place θ) := by
  unfold Compatible
  rw [graph_object θ phase K O i ha hphase hK Ω]
  constructor
  · intro h e he
    simpa only [Finset.image_image] using
      (Compiled.mem_graph_pullback Ω O.records i (e.image (place θ))).mp (h e he)
  · intro h e he
    apply (Compiled.mem_graph_pullback Ω O.records i (e.image (place θ))).mpr
    simpa only [Finset.image_image] using h e he

end TuranUniversality.Structural.PhaseRoles
