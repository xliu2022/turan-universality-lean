module

public import TuranUniversality.Structural.Canonical

@[expose] public section

/-! # Local constraints for arbitrary root classes

The role map is not required to be injective on root classes. This is the
actual local characterization used when adding one vertex to a canonical
ordinary graph. Its equivalence with a locally legal record presentation
is proved below.
-/

namespace TuranUniversality.Structural.Roles

open Cube Support Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def dataSet (ρ : V → Option (Roots b t)) (e : Finset V) : Finset V :=
  e.filter fun v => ρ v = none

@[simp] theorem mem_dataSet (ρ : V → Option (Roots b t)) (e : Finset V) (v : V) :
    v ∈ dataSet ρ e ↔ v ∈ e ∧ ρ v = none := by simp [dataSet]

theorem data_mem_image (ρ : V → Option (Roots b t)) (e : Finset V) (v : V) :
    Sum.inr (Sum.inr v) ∈ e.image (place ρ) ↔ v ∈ dataSet ρ e := by
  simp only [Finset.mem_image, place_eq_data, mem_dataSet]
  constructor
  · rintro ⟨u, hu, rfl, hn⟩
    exact ⟨hu, hn⟩
  · rintro ⟨hv, hn⟩
    exact ⟨v, hv, rfl, hn⟩

theorem image_data_eq (ρ : V → Option (Roots b t)) (e X : Finset V)
    (Z : Finset (Support.Vertex b))
    (h : e.image (place ρ) = Compiled.edge t Z X) : dataSet ρ e = X := by
  ext v
  rw [← data_mem_image, h, Compiled.mem_edge_data]

def Declares (Ω : Label → Finset (Word b)) (ρ : V → Option (Roots b t))
    (e : Finset V) (l : Label) : Prop :=
  ∃ Z ∈ (poolGraph (Ω l)).edges, e.image (place ρ) = Compiled.edge t Z (dataSet ρ e)

def GoodEdge (Ω : Label → Finset (Word b)) (ρ : V → Option (Roots b t)) (e : Finset V) : Prop :=
  (dataSet ρ e).card = 4 ∧ ∃ l, Declares Ω ρ e l

def Fits {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Word b))
    (ρ : V → Option (Roots b t)) (O : LegalObject B V) (e : Finset V) : Prop :=
  e.image (place ρ) ∈ (Compiled.graph t Ω O.records).edges

def LocallyLegal (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t)) : Prop :=
  ∀ S : Finset V, S.card ≤ RecordSystem.cutoff B →
    ∃ O : LegalObject B V, O.active ⊆ S ∧
      ∀ e ∈ G.edges, dataSet ρ e ⊆ S → Fits Ω ρ O e

def Admissible (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t)) : Prop :=
  (∀ e ∈ G.edges, GoodEdge Ω ρ e) ∧ LocallyLegal B Ω G ρ

theorem declares_unique (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (ρ : V → Option (Roots b t)) (e : Finset V) {l k : Label}
    (hl : Declares Ω ρ e l) (hk : Declares Ω ρ e k) : l = k := by
  obtain ⟨Z, hZ, hz⟩ := hl
  obtain ⟨W, hW, hw⟩ := hk
  have hp : (Z, dataSet ρ e) = (W, dataSet ρ e) := Compiled.edge_injective (hz.symm.trans hw)
  have heq : Z = W := congrArg Prod.fst hp
  subst W
  exact poolGraph_label_unique Ω hdis hZ hW

theorem fits_iff_declares {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Word b))
    (ρ : V → Option (Roots b t)) (O : LegalObject B V) (e : Finset V)
    (hc : (dataSet ρ e).card = 4) :
    Fits Ω ρ O e ↔ Declares Ω ρ e (O.label (dataSet ρ e)) := by
  constructor
  · intro h
    obtain ⟨X, hX, Z, hZ, hz⟩ := (Compiled.mem_graph Ω O.records _).mp h
    have hx : dataSet ρ e = X := image_data_eq ρ e X Z hz.symm
    subst X
    exact ⟨Z, hZ, hz.symm⟩
  · rintro ⟨Z, hZ, hz⟩
    exact (Compiled.mem_graph Ω O.records _).mpr
      ⟨dataSet ρ e, (O.mem_records _).mpr hc, Z, hZ, hz.symm⟩

theorem records_consistent (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t))
    (hadm : Admissible B Ω G ρ)
    {e f : Finset V} (he : e ∈ G.edges) (hf : f ∈ G.edges)
    (hdata : dataSet ρ e = dataSet ρ f) {l k : Label}
    (hl : Declares Ω ρ e l) (hk : Declares Ω ρ f k) : l = k := by
  have hc := (hadm.1 e he).1
  have hcf := (hadm.1 f hf).1
  have hsmall : (dataSet ρ e).card ≤ RecordSystem.cutoff B := by
    rw [hc]
    have hQ := RecordSystem.cutoff_ge_thirteen B
    omega
  obtain ⟨O, _, hfit⟩ := hadm.2 (dataSet ρ e) hsmall
  have hle := (fits_iff_declares Ω ρ O e hc).mp (hfit e he (le_refl _))
  have hkf := (fits_iff_declares Ω ρ O f hcf).mp (hfit f hf (by rw [hdata]))
  rw [declares_unique Ω hdis ρ e hl hle, declares_unique Ω hdis ρ f hk hkf, hdata]

theorem extract_records (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t))
    (hadm : Admissible B Ω G ρ) :
    ∃ R : RecordSystem V, R.recorded.edges = G.edges.image (dataSet ρ) ∧
      R.LocallyLegal B ∧ G.IsHom (Compiled.graph t Ω R) (place ρ) := by
  classical
  have hlabels (X : Finset V) : ∃ l : Label,
      ∀ e ∈ G.edges, dataSet ρ e = X → Declares Ω ρ e l := by
    by_cases hX : ∃ e ∈ G.edges, dataSet ρ e = X
    · obtain ⟨e, he, rfl⟩ := hX
      obtain ⟨l, hl⟩ := (hadm.1 e he).2
      refine ⟨l, ?_⟩
      intro f hf hdata
      obtain ⟨k, hk⟩ := (hadm.1 f hf).2
      have heq := records_consistent B Ω hdis G ρ hadm he hf hdata.symm hl hk
      exact heq ▸ hk
    · exact ⟨.inl 0, fun e he hdata => False.elim (hX ⟨e, he, hdata⟩)⟩
  choose labels hlabels using hlabels
  let R : RecordSystem V :=
    { recorded :=
        { edges := G.edges.image (dataSet ρ)
          uniform := by
            intro X hX
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hX
            exact (hadm.1 e he).1 }
      label := labels }
  refine ⟨R, rfl, ?_, ?_⟩
  · intro S hScard
    obtain ⟨O, hOS, hfit⟩ := hadm.2 S hScard
    refine ⟨O, hOS, ?_⟩
    intro X hX hXS
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hX
    have hc := (hadm.1 e he).1
    have hl := (fits_iff_declares Ω ρ O e hc).mp (hfit e he hXS)
    have heq : labels (dataSet ρ e) = O.label (dataSet ρ e) :=
      declares_unique Ω hdis ρ e (hlabels _ e he rfl) hl
    change O.Labels (dataSet ρ e) (labels (dataSet ρ e))
    rw [heq]
    exact O.labels_label _ (le_of_eq hc)
  · intro e he
    obtain ⟨Z, hZ, hz⟩ := hlabels (dataSet ρ e) e he rfl
    exact (Compiled.mem_graph Ω R _).mpr
      ⟨dataSet ρ e, Finset.mem_image.mpr ⟨e, he, rfl⟩, Z, hZ, hz.symm⟩

theorem admissible_of_records (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t))
    (R : RecordSystem V) (hlegal : R.LocallyLegal B)
    (hf : G.IsHom (Compiled.graph t Ω R) (place ρ)) : Admissible B Ω G ρ := by
  have hdecode (e : Finset V) (he : e ∈ G.edges) :
      dataSet ρ e ∈ R.recorded.edges ∧ Declares Ω ρ e (R.label (dataSet ρ e)) := by
    obtain ⟨X, hX, Z, hZ, hz⟩ := (Compiled.mem_graph Ω R _).mp (hf e he)
    have hx : dataSet ρ e = X := image_data_eq ρ e X Z hz.symm
    subst X
    exact ⟨hX, Z, hZ, hz.symm⟩
  refine ⟨fun e he => ⟨R.recorded.uniform _ (hdecode e he).1, _, (hdecode e he).2⟩, ?_⟩
  intro S hcard
  obtain ⟨O, hO, hreal⟩ := hlegal S hcard
  refine ⟨O, hO, ?_⟩
  intro e he heS
  have h := hdecode e he
  have hc := R.recorded.uniform _ h.1
  have heq := (O.labels_iff _ (le_of_eq hc) _).mp (hreal _ h.1 heS)
  apply (fits_iff_declares Ω ρ O e hc).mpr
  rw [heq]
  exact h.2

theorem canonical_iff (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) :
    Canonical B Ω G ↔ ∃ ρ, Admissible B Ω G ρ := by
  constructor
  · rintro ⟨ρ, R, hR, hh⟩
    exact ⟨ρ, admissible_of_records B Ω G ρ R hR hh⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨R, _, hR, hh⟩ := extract_records B Ω hdis G ρ hρ
    exact ⟨ρ, R, hR, hh⟩

theorem dataSet_congr (ρ σ : V → Option (Roots b t)) (e : Finset V)
    (h : ∀ v ∈ e, ρ v = σ v) : dataSet ρ e = dataSet σ e := by
  apply Finset.filter_congr
  intro v hv
  rw [h v hv]

theorem image_congr (ρ σ : V → Option (Roots b t)) (e : Finset V)
    (h : ∀ v ∈ e, ρ v = σ v) : e.image (place ρ) = e.image (place σ) := by
  apply Finset.image_congr
  intro v hv
  simp only [place, Selector.rootedVertex, h v hv]

theorem goodEdge_congr (Ω : Label → Finset (Word b)) (ρ σ : V → Option (Roots b t))
    (e : Finset V) (h : ∀ v ∈ e, ρ v = σ v) : GoodEdge Ω ρ e ↔ GoodEdge Ω σ e := by
  simp only [GoodEdge, Declares, dataSet_congr ρ σ e h, image_congr ρ σ e h]

theorem fits_congr {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Word b))
    (ρ σ : V → Option (Roots b t)) (O : LegalObject B V) (e : Finset V)
    (h : ∀ v ∈ e, ρ v = σ v) : Fits Ω ρ O e ↔ Fits Ω σ O e := by
  simp only [Fits, image_congr ρ σ e h]

end TuranUniversality.Structural.Roles
