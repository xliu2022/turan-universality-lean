module

public import TuranUniversality.Structural.Compiled
public import TuranUniversality.Structural.RecordComplete
public import TuranUniversality.Selector.RootingSupport

@[expose] public section

/-! # Local admissibility under an actual partial root assignment

The edge test uses the actual seven support graphs. Local legal objects
must simultaneously realize every available edge over each small data set;
this includes conflicting-record failures. No selected labels or assumed
local-witness bounds are part of the definition.
-/

namespace TuranUniversality.Structural.Rooted

open Cube Support

abbrev Roots (b t : ℕ) := Fin t ⊕ Support.Vertex b

@[simp] theorem roots_card (b t : ℕ) : Fintype.card (Roots b t) = t + 5 * b := by
  simp [Roots, Support.Vertex, Nat.mul_comm]

def place {V : Type*} {b t : ℕ} (ρ : V → Option (Roots b t)) (v : V) :
    Compiled.Vertex b t V := (Equiv.sumAssoc (Fin t) (Support.Vertex b) V) (Selector.rootedVertex ρ v)

theorem place_injective {V : Type*} {b t : ℕ} (ρ : V → Option (Roots b t))
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) : Function.Injective (place ρ) :=
  (Equiv.sumAssoc (Fin t) (Support.Vertex b) V).injective.comp (Selector.rootedVertex_injective ρ hρ)

@[simp] theorem place_none {V : Type*} {b t : ℕ} (ρ : V → Option (Roots b t))
    {v : V} (h : ρ v = none) : place ρ v = .inr (.inr v) := by
  simp [place, Selector.rootedVertex, h]

@[simp] theorem place_root {V : Type*} {b t : ℕ} (ρ : V → Option (Roots b t))
    {v : V} {r : Roots b t} (h : ρ v = some r) :
    place ρ v = (Equiv.sumAssoc (Fin t) (Support.Vertex b) V) (.inl r) := by
  simp [place, Selector.rootedVertex, h]

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

noncomputable def dataSet (μ : Rooting (Roots b t) V) (e : Finset V) : Finset V :=
  e.filter fun v => μ.inverse.val v = none

@[simp] theorem mem_dataSet (μ : Rooting (Roots b t) V) (e : Finset V) (v : V) :
    v ∈ dataSet μ e ↔ v ∈ e ∧ μ.inverse.val v = none := by simp [dataSet]

theorem edge_subset_roots_data (μ : Rooting (Roots b t) V) (e : Finset V) :
    e ⊆ μ.range ∪ dataSet μ e := by
  intro v hv
  by_cases hr : v ∈ μ.range
  · exact Finset.mem_union_left _ hr
  · exact Finset.mem_union_right _ ((mem_dataSet μ e v).mpr
      ⟨hv, (Selector.inverse_none_iff μ v).mpr hr⟩)

def GoodEdge (Ω : Label → Finset (Word b)) (μ : Rooting (Roots b t) V) (e : Finset V) : Prop :=
  (dataSet μ e).card = 4 ∧ ∃ l : Label, ∃ Z ∈ (poolGraph (Ω l)).edges,
    e.image (place μ.inverse.val) = Compiled.edge t Z (dataSet μ e)

def Fits {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Word b))
    (μ : Rooting (Roots b t) V) (O : LegalObject B V) (e : Finset V) : Prop :=
  e.image (place μ.inverse.val) ∈ (Compiled.graph t Ω O.records).edges

def LocallyLegalOn (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (T : Finset V) (μ : Rooting (Roots b t) V) : Prop :=
  ∀ S : Finset V, S ⊆ T → (∀ v ∈ S, μ.inverse.val v = none) → S.card ≤ RecordSystem.cutoff B →
    ∃ O : LegalObject B V, O.active ⊆ S ∧
      ∀ e ∈ G.edges, e ⊆ T → dataSet μ e ⊆ S → Fits Ω μ O e

def AdmissibleOn (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) (T : Finset V) (μ : Rooting (Roots b t) V) : Prop :=
  (∀ e ∈ G.edges, e ⊆ T → GoodEdge Ω μ e) ∧ LocallyLegalOn B Ω G T μ

def Admits (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (G : RGraph V (t + (3 * b + 4))) : Prop :=
  ∃ μ : Rooting (Roots b t) V, AdmissibleOn B Ω G Finset.univ μ

theorem dataSet_congr (μ ν : Rooting (Roots b t) V) (e : Finset V)
    (h : ∀ v ∈ e, μ.inverse.val v = ν.inverse.val v) : dataSet μ e = dataSet ν e := by
  apply Finset.filter_congr
  intro v hv
  rw [h v hv]

theorem image_congr (μ ν : Rooting (Roots b t) V) (e : Finset V)
    (h : ∀ v ∈ e, μ.inverse.val v = ν.inverse.val v) :
    e.image (place μ.inverse.val) = e.image (place ν.inverse.val) := by
  apply Finset.image_congr
  intro v hv
  simp only [place, Selector.rootedVertex, h v hv]

theorem goodEdge_congr (Ω : Label → Finset (Word b)) (μ ν : Rooting (Roots b t) V)
    (e : Finset V) (h : ∀ v ∈ e, μ.inverse.val v = ν.inverse.val v) :
    GoodEdge Ω μ e ↔ GoodEdge Ω ν e := by
  simp only [GoodEdge, dataSet_congr μ ν e h, image_congr μ ν e h]

theorem fits_congr {B : Finset (FiniteGraph 3)} (Ω : Label → Finset (Word b))
    (μ ν : Rooting (Roots b t) V) (O : LegalObject B V) (e : Finset V)
    (h : ∀ v ∈ e, μ.inverse.val v = ν.inverse.val v) :
    Fits Ω μ O e ↔ Fits Ω ν O e := by
  simp only [Fits, image_congr μ ν e h]

theorem admissibleOn_mono {B : Finset (FiniteGraph 3)} {Ω : Label → Finset (Word b)}
    {G : RGraph V (t + (3 * b + 4))} {T U : Finset V} {μ : Rooting (Roots b t) V}
    (h : AdmissibleOn B Ω G T μ) (hUT : U ⊆ T) : AdmissibleOn B Ω G U μ := by
  refine ⟨fun e he heU => h.1 e he (heU.trans hUT), ?_⟩
  intro S hSU hdata hcard
  obtain ⟨O, hO, hfit⟩ := h.2 S (hSU.trans hUT) hdata hcard
  exact ⟨O, hO, fun e he heU hdata => hfit e he (heU.trans hUT) hdata⟩

end TuranUniversality.Structural.Rooted
