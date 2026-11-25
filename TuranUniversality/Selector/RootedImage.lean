/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RowRooting
public import TuranUniversality.Weighted.Model
public import TuranUniversality.Hypergraph.Rooting

/-! # Realizing a partial root assignment as an actual rooted graph -/

@[expose] public section

namespace TuranUniversality.Selector

open RGraph Weighted

variable {X Roots : Type*} [DecidableEq X] [DecidableEq Roots]

def rootedVertex (ρ : X → Option Roots) (x : X) : Roots ⊕ X :=
  match ρ x with
  | none => Sum.inr x
  | some r => Sum.inl r

omit [DecidableEq X] [DecidableEq Roots] in
@[simp] theorem rootedVertex_eq_inl (ρ : X → Option Roots) (x : X) (r : Roots) :
    rootedVertex ρ x = Sum.inl r ↔ ρ x = some r := by
  cases h : ρ x <;> simp [rootedVertex, h]

omit [DecidableEq X] [DecidableEq Roots] in
@[simp] theorem rootedVertex_eq_inr (ρ : X → Option Roots) (x y : X) :
    rootedVertex ρ x = Sum.inr y ↔ x = y ∧ ρ x = none := by
  cases h : ρ x <;> simp [rootedVertex, h]

omit [DecidableEq X] [DecidableEq Roots] in
theorem rootedVertex_injective (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) :
    Function.Injective (rootedVertex ρ) := by
  intro x y heq
  cases hx : ρ x with
  | none =>
      cases hy : ρ y with
      | none => simpa [rootedVertex, hx, hy] using heq
      | some r => simp [rootedVertex, hx, hy] at heq
  | some r =>
      cases hy : ρ y with
      | none => simp [rootedVertex, hx, hy] at heq
      | some s =>
          have hrs : r = s := by simpa [rootedVertex, hx, hy] using heq
          exact hρ x y r hx (hrs ▸ hy)

/-- Add unused root labels and unused data copies only as isolated
vertices, and transport every source edge along the injective rooting. -/
def rootedGraph (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) :
    RGraph (Roots ⊕ X) 3 where
  edges := A.edges.image fun e => e.image (rootedVertex ρ)
  uniform := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.card_image_of_injective _ (rootedVertex_injective ρ hρ)]
    exact A.uniform d hd

def rootedImage (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) : RootedModel Roots X :=
  RootedModel.ofRGraph (rootedGraph A ρ hρ)

@[simp] theorem rootedImage_toRGraph (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) :
    (rootedImage A ρ hρ).toRGraph = rootedGraph A ρ hρ := RootedModel.toRGraph_ofRGraph _

theorem rootedGraph_embedding (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) :
    A.IsEmbedding (rootedGraph A ρ hρ) (rootedVertex ρ) := by
  refine ⟨rootedVertex_injective ρ hρ, ?_⟩
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem rootedGraph_reflect_triple (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) (x y z : X) :
    {rootedVertex ρ x, rootedVertex ρ y, rootedVertex ρ z} ∈ (rootedGraph A ρ hρ).edges ↔
      {x, y, z} ∈ A.edges := by
  constructor
  · intro he
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp he
    have heq' : e.image (rootedVertex ρ) = ({x, y, z} : Finset X).image (rootedVertex ρ) := by
      simpa using heq
    have hes : e = {x, y, z} := Finset.image_injective (rootedVertex_injective ρ hρ) heq'
    exact hes ▸ he
  · intro he
    simpa using (rootedGraph_embedding A ρ hρ).2 _ he

theorem rootedGraph_vertex_preimage (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y)
    {e : Finset (Roots ⊕ X)} (he : e ∈ (rootedGraph A ρ hρ).edges)
    {v : Roots ⊕ X} (hv : v ∈ e) : ∃ x, rootedVertex ρ x = v := by
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
  exact ⟨x, hx⟩

theorem rootedGraph_data_none (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y)
    {e : Finset (Roots ⊕ X)} (he : e ∈ (rootedGraph A ρ hρ).edges)
    {x : X} (hx : Sum.inr x ∈ e) : ρ x = none := by
  obtain ⟨y, hy⟩ := rootedGraph_vertex_preimage A ρ hρ he hx
  obtain ⟨rfl, hn⟩ := (rootedVertex_eq_inr ρ y x).mp hy
  exact hn

theorem rootedGraph_root_exists (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y)
    {e : Finset (Roots ⊕ X)} (he : e ∈ (rootedGraph A ρ hρ).edges)
    {r : Roots} (hr : Sum.inl r ∈ e) : ∃ x, ρ x = some r := by
  obtain ⟨x, hx⟩ := rootedGraph_vertex_preimage A ρ hρ he hr
  exact ⟨x, (rootedVertex_eq_inl ρ x r).mp hx⟩

theorem split_edge_mem_iff {Data : Type*} [DecidableEq Data]
    (M : RootedModel Roots Data) (r : Finset Roots) (d : Finset Data) :
    (r, d) ∈ M.edges ↔ r.disjSum d ∈ M.toRGraph.edges := by
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨(r, d), h, rfl⟩
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    have hep : p = (r, d) := Prod.ext (Finset.disjSum_inj.mp heq).1 (Finset.disjSum_inj.mp heq).2
    exact hep ▸ hp

end TuranUniversality.Selector
