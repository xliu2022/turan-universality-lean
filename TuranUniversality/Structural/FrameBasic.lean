module

public import TuranUniversality.Structural.Compiled
public import TuranUniversality.Hypergraph.Clique

@[expose] public section

/-! # The actual finite neutral frame

Five formal data vertices carry all four-subsets. The frame contains the
specified neutral support pool. The all-zero word already proves pair
coverage and that exactly the suspension vertices belong to every edge.
-/

namespace TuranUniversality.Structural.Frame

open Compiled Cube Support

def neutralRecords : RecordSystem (Fin 5) where
  recorded := RGraph.clique (Fin 5) 4
  label _ := .inl 0

def graph (b t : ℕ) (Ω : Finset (Word b)) :
    RGraph (Compiled.Vertex b t (Fin 5)) (t + (3 * b + 4)) :=
  Compiled.graph t (fun _ => Ω) neutralRecords

theorem mem_graph {b t : ℕ} (Ω : Finset (Word b))
    (e : Finset (Compiled.Vertex b t (Fin 5))) :
    e ∈ (graph b t Ω).edges ↔
      ∃ X : Finset (Fin 5), X.card = 4 ∧
        ∃ Z ∈ (poolGraph Ω).edges, Compiled.edge t Z X = e := by
  rw [graph, Compiled.mem_graph]
  simp [neutralRecords]

theorem edge_mem {b t : ℕ} {Ω : Finset (Word b)} {w : Word b} (hw : w ∈ Ω)
    (e : Choice w) {X : Finset (Fin 5)} (hX : X.card = 4) :
    Compiled.edge t (choiceEdge w e) X ∈ (graph b t Ω).edges := by
  apply (mem_graph Ω _).mpr
  refine ⟨X, hX, choiceEdge w e, ?_, rfl⟩
  exact Finset.mem_biUnion.mpr ⟨w, hw, (mem_wordGraph _ _).mpr ⟨e, rfl⟩⟩

theorem pentagon_pair (a c : Fin 5) :
    ∃ e ∈ Pentagon.P0.edges, a ∈ e ∧ c ∈ e := by
  have h : ∀ a c : Fin 5, ∃ e ∈ Pentagon.P0.edges, a ∈ e ∧ c ∈ e := by decide
  exact h a c

theorem data_pair (a c : Fin 5) :
    ∃ X : Finset (Fin 5), X.card = 4 ∧ a ∈ X ∧ c ∈ X := by
  have h : ∀ a c : Fin 5, ∃ X : Finset (Fin 5), X.card = 4 ∧ a ∈ X ∧ c ∈ X := by
    decide
  exact h a c

theorem pentagon_avoids (a : Fin 5) : ∃ e ∈ Pentagon.P0.edges, a ∉ e := by
  have h : ∀ a : Fin 5, ∃ e ∈ Pentagon.P0.edges, a ∉ e := by decide
  exact h a

def blockCoordinate {b t : ℕ} (i : Fin b) : Compiled.Vertex b t (Fin 5) → Fin 5
  | .inr (.inl v) => if v.1 = i then v.2 else 0
  | _ => 0

def dataCoordinate {b t : ℕ} : Compiled.Vertex b t (Fin 5) → Fin 5
  | .inr (.inr v) => v
  | _ => 0

/-- An explicit edge contains any two prescribed formal vertices. -/
theorem contains_pair {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω)
    (u v : Compiled.Vertex b t (Fin 5)) :
    ∃ e ∈ (graph b t Ω).edges, u ∈ e ∧ v ∈ e := by
  classical
  choose es hes hu hv using
    (fun i : Fin b => pentagon_pair (blockCoordinate i u) (blockCoordinate i v))
  let a : Choice (∅ : Word b) := fun i => ⟨es i, by simpa [blockGraph, Pentagon.graph] using hes i⟩
  obtain ⟨X, hX, huX, hvX⟩ := data_pair (dataCoordinate u) (dataCoordinate v)
  refine ⟨Compiled.edge t (choiceEdge ∅ a) X, edge_mem hzero a hX, ?_, ?_⟩
  · cases u with
    | inl i => simp
    | inr u =>
      cases u with
      | inl u =>
        simpa [choiceEdge, joinRows, a, blockCoordinate] using hu u.1
      | inr u => simpa [dataCoordinate] using huX
  · cases v with
    | inl i => simp
    | inr v =>
      cases v with
      | inl v =>
        simpa [choiceEdge, joinRows, a, blockCoordinate] using hv v.1
      | inr v => simpa [dataCoordinate] using hvX

theorem coversPairs {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω) :
    (graph b t Ω).CoversPairs := fun u v _ => contains_pair hzero u v

theorem edges_nonempty {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω) :
    (graph b t Ω).edges.Nonempty := by
  obtain ⟨e, he, _⟩ := contains_pair (t := t) hzero (.inr (.inr 0)) (.inr (.inr 0))
  exact ⟨e, he⟩

def baseChoice (b : ℕ) : Choice (∅ : Word b) :=
  fun _ => ⟨{0, 1, 2}, by simp [blockGraph, Pentagon.graph, Pentagon.P0]⟩

theorem avoids_data {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω) (v : Fin 5) :
    ∃ e ∈ (graph b t Ω).edges, Sum.inr (Sum.inr v) ∉ e := by
  let X : Finset (Fin 5) := Finset.univ.erase v
  have hX : X.card = 4 := by simp [X]
  exact ⟨Compiled.edge t (choiceEdge ∅ (baseChoice b)) X,
    edge_mem hzero (baseChoice b) hX, by simp [X]⟩

theorem avoids_block {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω)
    (v : Support.Vertex b) :
    ∃ e ∈ (graph b t Ω).edges, Sum.inr (Sum.inl v) ∉ e := by
  classical
  obtain ⟨Z, hZ, hv⟩ := pentagon_avoids v.2
  let a : Choice (∅ : Word b) := fun i =>
    ⟨if i = v.1 then Z else {0, 1, 2}, by
      by_cases hi : i = v.1
      · simpa [hi, blockGraph, Pentagon.graph] using hZ
      · simp [hi, blockGraph, Pentagon.graph, Pentagon.P0]⟩
  refine ⟨Compiled.edge t (choiceEdge ∅ a) {0, 1, 2, 3},
    edge_mem hzero a (by decide), ?_⟩
  simpa [choiceEdge, joinRows, a] using hv

/-- The common intersection is exactly the suspension set, as an ordinary graph fact. -/
theorem common_intersection {b t : ℕ} {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω)
    (v : Compiled.Vertex b t (Fin 5)) :
    (∀ e ∈ (graph b t Ω).edges, v ∈ e) ↔ ∃ i : Fin t, v = Sum.inl i := by
  constructor
  · intro h
    cases v with
    | inl i => exact ⟨i, rfl⟩
    | inr v =>
      cases v with
      | inl v =>
        obtain ⟨e, he, hve⟩ := avoids_block (t := t) hzero v
        exact False.elim (hve (h e he))
      | inr v =>
        obtain ⟨e, he, hve⟩ := avoids_data (t := t) hzero v
        exact False.elim (hve (h e he))
  · rintro ⟨i, rfl⟩ e he
    obtain ⟨X, hX, Z, hZ, rfl⟩ := (mem_graph Ω e).mp he
    simp

theorem hom_injective {V : Type*} [DecidableEq V] {b t : ℕ}
    {Ω : Finset (Word b)} (hzero : ∅ ∈ Ω)
    {G : RGraph V (t + (3 * b + 4))} {f : Compiled.Vertex b t (Fin 5) → V}
    (hf : (graph b t Ω).IsHom G f) : Function.Injective f :=
  (coversPairs hzero).hom_injective hf

end TuranUniversality.Structural.Frame
