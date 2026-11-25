module

public import TuranUniversality.Structural.RootedLocal
public import TuranUniversality.Structural.CodePools

@[expose] public section

/-! # Extracting consistent actual records from partial rootings

The local admissibility predicate is equivalent to the paper's semantics:
the available data four-sets carry a single label, these records are locally
legal, and all ordinary edges embed in their actual support completion.
-/

namespace TuranUniversality.Structural.Rooted

open Cube Support

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem place_eq_data (ρ : V → Option (Roots b t)) (u v : V) :
    place ρ u = (Sum.inr (Sum.inr v) : Compiled.Vertex b t V) ↔ u = v ∧ ρ u = none := by
  cases h : ρ u with
  | none => simp [place, Selector.rootedVertex, h]
  | some r => cases r <;> simp [place, Selector.rootedVertex, h]

theorem data_mem_image (μ : Rooting (Roots b t) V) (e : Finset V) (v : V) :
    Sum.inr (Sum.inr v) ∈ e.image (place μ.inverse.val) ↔ v ∈ dataSet μ e := by
  simp only [Finset.mem_image, place_eq_data, mem_dataSet]
  constructor
  · rintro ⟨u, hu, rfl, hn⟩
    exact ⟨hu, hn⟩
  · rintro ⟨hv, hn⟩
    exact ⟨v, hv, rfl, hn⟩

theorem image_data_eq (μ : Rooting (Roots b t) V) (e X : Finset V)
    (Z : Finset (Support.Vertex b))
    (h : e.image (place μ.inverse.val) = Compiled.edge t Z X) : dataSet μ e = X := by
  ext v
  rw [← data_mem_image, h, Compiled.mem_edge_data]

theorem poolGraph_label_unique (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    {l k : Label} {Z : Finset (Support.Vertex b)}
    (hl : Z ∈ (poolGraph (Ω l)).edges) (hk : Z ∈ (poolGraph (Ω k)).edges) : l = k := by
  obtain ⟨u, hu, hZu⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨v, hv, hZv⟩ := Finset.mem_biUnion.mp hk
  have heq : u = v := word_eq_of_common_edge hZu hZv
  subst v
  by_contra hne
  exact Finset.disjoint_left.mp (hdis l k hne) hu hv

def Declares (Ω : Label → Finset (Word b)) (μ : Rooting (Roots b t) V)
    (e : Finset V) (l : Label) : Prop :=
  ∃ Z ∈ (poolGraph (Ω l)).edges,
    e.image (place μ.inverse.val) = Compiled.edge t Z (dataSet μ e)

theorem goodEdge_declares (Ω : Label → Finset (Word b)) (μ : Rooting (Roots b t) V)
    (e : Finset V) : GoodEdge Ω μ e ↔ (dataSet μ e).card = 4 ∧ ∃ l, Declares Ω μ e l := Iff.rfl

theorem declares_unique (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (μ : Rooting (Roots b t) V) (e : Finset V) {l k : Label}
    (hl : Declares Ω μ e l) (hk : Declares Ω μ e k) : l = k := by
  obtain ⟨Z, hZ, hz⟩ := hl
  obtain ⟨W, hW, hw⟩ := hk
  have hp : (Z, dataSet μ e) = (W, dataSet μ e) := Compiled.edge_injective (hz.symm.trans hw)
  have heq : Z = W := congrArg Prod.fst hp
  subst W
  exact poolGraph_label_unique Ω hdis hZ hW

theorem fits_iff_declares {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Word b))
    (μ : Rooting (Roots b t) V) (O : LegalObject B V) (e : Finset V)
    (hc : (dataSet μ e).card = 4) :
    Fits Ω μ O e ↔ Declares Ω μ e (O.label (dataSet μ e)) := by
  constructor
  · intro h
    obtain ⟨X, hX, Z, hZ, hz⟩ := (Compiled.mem_graph Ω O.records _).mp h
    have hx : dataSet μ e = X := image_data_eq μ e X Z hz.symm
    subst X
    exact ⟨Z, hZ, hz.symm⟩
  · rintro ⟨Z, hZ, hz⟩
    exact (Compiled.mem_graph Ω O.records _).mpr
      ⟨dataSet μ e, (O.mem_records _).mpr hc, Z, hZ, hz.symm⟩

theorem records_consistent (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (μ : Rooting (Roots b t) V)
    (hadm : AdmissibleOn B Ω G Finset.univ μ)
    {e f : Finset V} (he : e ∈ G.edges) (hf : f ∈ G.edges)
    (hdata : dataSet μ e = dataSet μ f) {l k : Label}
    (hl : Declares Ω μ e l) (hk : Declares Ω μ f k) : l = k := by
  have hc := (hadm.1 e he (Finset.subset_univ _)).1
  have hcf := (hadm.1 f hf (Finset.subset_univ _)).1
  have hnone (v : V) (hv : v ∈ dataSet μ e) : μ.inverse.val v = none :=
    ((mem_dataSet μ e v).mp hv).2
  have hsmall : (dataSet μ e).card ≤ RecordSystem.cutoff B := by
    rw [hc]
    have hQ := RecordSystem.cutoff_ge_thirteen B
    omega
  obtain ⟨O, hO, hfit⟩ := hadm.2 (dataSet μ e) (Finset.subset_univ _) hnone hsmall
  have hle := (fits_iff_declares Ω μ O e hc).mp
    (hfit e he (Finset.subset_univ _) (le_refl _))
  have hkf := (fits_iff_declares Ω μ O f hcf).mp
    (hfit f hf (Finset.subset_univ _) (by rw [hdata]))
  have h1 := declares_unique Ω hdis μ e hl hle
  have h2 := declares_unique Ω hdis μ f hk hkf
  rw [h1, h2, hdata]

/-- The actual extraction, with the exact available four-sets and a genuine
ordinary embedding into the support-completed model. -/
theorem extract_records (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (μ : Rooting (Roots b t) V)
    (hadm : AdmissibleOn B Ω G Finset.univ μ) :
    ∃ R : RecordSystem V, R.recorded.edges = G.edges.image (dataSet μ) ∧
      R.LocallyLegal B ∧ G.IsEmbedding (Compiled.graph t Ω R) (place μ.inverse.val) := by
  classical
  have hlabels (X : Finset V) : ∃ l : Label,
      ∀ e ∈ G.edges, dataSet μ e = X → Declares Ω μ e l := by
    by_cases hX : ∃ e ∈ G.edges, dataSet μ e = X
    · obtain ⟨e, he, rfl⟩ := hX
      obtain ⟨l, hl⟩ := (hadm.1 e he (Finset.subset_univ _)).2
      refine ⟨l, ?_⟩
      intro f hf hdata
      obtain ⟨k, hk⟩ := (hadm.1 f hf (Finset.subset_univ _)).2
      have heq := records_consistent B Ω hdis G μ hadm he hf hdata.symm hl hk
      exact heq ▸ hk
    · exact ⟨.inl 0, fun e he hdata => False.elim (hX ⟨e, he, hdata⟩)⟩
  choose labels hlabels using hlabels
  let R : RecordSystem V :=
    { recorded :=
        { edges := G.edges.image (dataSet μ)
          uniform := by
            intro X hX
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hX
            exact (hadm.1 e he (Finset.subset_univ _)).1 }
      label := labels }
  refine ⟨R, rfl, ?_, place_injective μ.inverse.val μ.inverse.property, ?_⟩
  · intro S hScard
    let S' := S.filter fun v => μ.inverse.val v = none
    have hS' : S' ⊆ S := Finset.filter_subset _ _
    have hnone : ∀ v ∈ S', μ.inverse.val v = none :=
      fun v hv => (Finset.mem_filter.mp hv).2
    have hS'card : S'.card ≤ RecordSystem.cutoff B :=
      (Finset.card_le_card hS').trans hScard
    obtain ⟨O, hOS, hfit⟩ := hadm.2 S' (Finset.subset_univ _) hnone hS'card
    refine ⟨O, hOS.trans hS', ?_⟩
    intro X hX hXS
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hX
    have heS' : dataSet μ e ⊆ S' := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨hXS hv, ((mem_dataSet μ e v).mp hv).2⟩
    have hc := (hadm.1 e he (Finset.subset_univ _)).1
    have hl := (fits_iff_declares Ω μ O e hc).mp (hfit e he (Finset.subset_univ _) heS')
    have heq : labels (dataSet μ e) = O.label (dataSet μ e) :=
      declares_unique Ω hdis μ e (hlabels _ e he rfl) hl
    change O.Labels (dataSet μ e) (labels (dataSet μ e))
    rw [heq]
    exact O.labels_label _ (le_of_eq hc)
  · intro e he
    obtain ⟨Z, hZ, hz⟩ := hlabels (dataSet μ e) e he rfl
    apply (Compiled.mem_graph Ω R _).mpr
    exact ⟨dataSet μ e, Finset.mem_image.mpr ⟨e, he, rfl⟩, Z, hZ, hz.symm⟩

/-- A locally legal completion witnesses exactly the same local rooted
admissibility predicate, in the reverse direction. -/
theorem admissibleOn_of_records (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (T : Finset V) (μ : Rooting (Roots b t) V)
    (R : RecordSystem V) (hlegal : R.LocallyLegal B)
    (hf : ∀ e ∈ G.edges, e ⊆ T → e.image (place μ.inverse.val) ∈ (Compiled.graph t Ω R).edges) :
    AdmissibleOn B Ω G T μ := by
  have hdecode (e : Finset V) (he : e ∈ G.edges) (heT : e ⊆ T) :
      dataSet μ e ∈ R.recorded.edges ∧ Declares Ω μ e (R.label (dataSet μ e)) := by
    obtain ⟨X, hX, Z, hZ, hz⟩ := (Compiled.mem_graph Ω R _).mp (hf e he heT)
    have hx := image_data_eq μ e X Z hz.symm
    subst X
    exact ⟨hX, Z, hZ, hz.symm⟩
  refine ⟨?_, ?_⟩
  · intro e he heT
    have h := hdecode e he heT
    exact ⟨R.recorded.uniform _ h.1, R.label (dataSet μ e), h.2⟩
  · intro S hS hnone hcard
    obtain ⟨O, hO, hreal⟩ := hlegal S hcard
    refine ⟨O, hO, ?_⟩
    intro e he heU heS
    have h := hdecode e he heU
    have hc := R.recorded.uniform _ h.1
    have hl := hreal (dataSet μ e) h.1 heS
    have heq : O.label (dataSet μ e) = R.label (dataSet μ e) :=
      (O.labels_iff _ (le_of_eq hc) _).mp hl
    apply (fits_iff_declares Ω μ O e hc).mpr
    rw [heq]
    exact h.2

theorem admissible_of_records (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (μ : Rooting (Roots b t) V)
    (R : RecordSystem V) (hlegal : R.LocallyLegal B)
    (hf : G.IsHom (Compiled.graph t Ω R) (place μ.inverse.val)) :
    AdmissibleOn B Ω G Finset.univ μ :=
  admissibleOn_of_records B Ω G Finset.univ μ R hlegal (fun e he _ => hf e he)

end TuranUniversality.Structural.Rooted
