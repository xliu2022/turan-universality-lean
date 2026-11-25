/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.Admissibility
public import TuranUniversality.Selector.RootedWitnesses
public import TuranUniversality.Computation.Pullback

/-! # Rooted legality under actual edge-preserving embeddings -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

variable {Roots X Y Code Kinds Alphabet : Type*} {L : ℕ}
    [DecidableEq Roots] [DecidableEq X] [DecidableEq Y]

/-- An embedding fixes every root label and injects the data vertices. -/
structure RootedEmbedding (A : RootedModel Roots X) (B : RootedModel Roots Y) where
  dataMap : X ↪ Y
  edge_map : ∀ p ∈ A.edges, (p.1, p.2.image dataMap) ∈ B.edges

namespace RootedEmbedding

variable {A : RootedModel Roots X} {B : RootedModel Roots Y}

theorem rootLink (F : RootedEmbedding A B) (x : X) : A.rootLink x ⊆ B.rootLink (F.dataMap x) := by
  intro p hp
  have he := F.edge_map (p, {x}) ((A.mem_rootLink x p).mp hp)
  exact (B.mem_rootLink (F.dataMap x) p).mpr (by simpa using he)

theorem dataLink (F : RootedEmbedding A B) (r : Roots) (p : Finset X) (hp : p ∈ A.dataLink r) :
    p.image F.dataMap ∈ B.dataLink r :=
  (B.mem_dataLink r _).mpr (F.edge_map ({r}, p) ((A.mem_dataLink r p).mp hp))

theorem dataTriples (F : RootedEmbedding A B) (p : Finset X) (hp : p ∈ A.dataTriples) :
    p.image F.dataMap ∈ B.dataTriples :=
  (B.mem_dataTriples _).mpr (F.edge_map (∅, p) ((A.mem_dataTriples p).mp hp))

variable [Fintype Roots] [Fintype Code] [DecidableEq Code]

theorem candidates (F : RootedEmbedding A B) (C : CodeSystem Roots Code) (x : X) :
    C.candidates B (F.dataMap x) ⊆ C.candidates A x := by
  intro c hc
  apply (C.mem_candidates A x c).mpr
  exact ((C.mem_candidates B (F.dataMap x) c).mp hc).mono_left (F.rootLink x)

theorem hasCandidates (F : RootedEmbedding A B) (C : CodeSystem Roots Code)
    (hB : C.HasCandidates B) : C.HasCandidates A := by
  intro x
  obtain ⟨c, hc⟩ := hB (F.dataMap x)
  exact ⟨c, F.candidates C x hc⟩

theorem declared (F : RootedEmbedding A B) (C : CodeSystem Roots Code)
    (hB : C.HasCandidates B) (x : X) (c : Code) (hc : C.Declared A x c) :
    C.Declared B (F.dataMap x) c := by
  have hsub : C.candidates B (F.dataMap x) ⊆ {c} := by
    rw [← hc]
    exact F.candidates C x
  obtain ⟨d, hd⟩ := hB (F.dataMap x)
  have hdc : d = c := Finset.mem_singleton.mp (hsub hd)
  apply Finset.Subset.antisymm hsub
  exact Finset.singleton_subset_iff.mpr (hdc ▸ hd)

variable [Fintype X] [Fintype Y] [Fintype Kinds] [DecidableEq Kinds]

theorem typeClass (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (x : X) (k : Kinds) (hx : x ∈ S.typeClass A k) :
    F.dataMap x ∈ S.typeClass B k := by
  obtain ⟨c, hc, hkind⟩ := (S.codes.mem_typeVertices A S.physical k x).mp hx
  exact (S.codes.mem_typeVertices B S.physical k (F.dataMap x)).mpr
    ⟨c, F.declared S.codes hB x c hc, hkind⟩

theorem relationCopy (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (e : Fin 3) (j : Fin L) (x y : X)
    (hp : (x, y) ∈ S.relationCopy A e j) :
    (F.dataMap x, F.dataMap y) ∈ S.relationCopy B e j := by
  obtain ⟨hx, hy, he⟩ := (S.mem_relationCopy A e j (x, y)).mp hp
  apply (S.mem_relationCopy B e j _).mpr
  refine ⟨F.typeClass S hB x _ hx, F.typeClass S hB y _ hy, ?_⟩
  simpa using F.edge_map ({S.copyRoot (e, j)}, {x, y}) he

theorem unionRelation (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (e : Fin 3) (x y : X)
    (hp : (x, y) ∈ S.unionRelation A e) : (F.dataMap x, F.dataMap y) ∈ S.unionRelation B e := by
  obtain ⟨j, hj⟩ := (S.mem_unionRelation A e (x, y)).mp hp
  exact (S.mem_unionRelation B e _).mpr ⟨j, F.relationCopy S hB e j x y hj⟩

theorem oneRootRules (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (hH2 : S.OneRootRules B) : S.OneRootRules A := by
  intro r p hp x hx y hy hxy c d hc hd hphysical
  exact hH2 r (p.image F.dataMap) (F.dataLink r p hp)
    (F.dataMap x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (F.dataMap y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    (fun h => hxy (F.dataMap.injective h)) c d
    (F.declared S.codes hB x c hc) (F.declared S.codes hB y d hd) hphysical

theorem matching (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (e : Fin 3) (hm : S.IsMatching B e) : S.IsMatching A e := by
  constructor
  · intro p hp q hq heq
    have hpt := F.unionRelation S hB e p.1 p.2 hp
    have hqt := F.unionRelation S hB e q.1 q.2 hq
    have ht := hm.1 hpt hqt (congrArg F.dataMap heq)
    exact Prod.ext heq (F.dataMap.injective (congrArg Prod.snd ht))
  · intro p hp q hq heq
    have hpt := F.unionRelation S hB e p.1 p.2 hp
    have hqt := F.unionRelation S hB e q.1 q.2 hq
    have ht := hm.2 hpt hqt (congrArg F.dataMap heq)
    exact Prod.ext (F.dataMap.injective (congrArg Prod.fst ht)) heq

theorem oneMarker (F : RootedEmbedding A B) (hB : B.dataTriples.card ≤ 1) : A.dataTriples.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  apply Finset.image_injective F.dataMap.injective
  exact Finset.card_le_one.mp hB _ (F.dataTriples p hp) _ (F.dataTriples q hq)

theorem markerTypes (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (hMarker : S.MarkerTypes B) : S.MarkerTypes A := by
  intro p hp x hx c hc
  exact hMarker (p.image F.dataMap) (F.dataTriples p hp) (F.dataMap x)
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩) c (F.declared S.codes hB x c hc)

theorem marks (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.codes.HasCandidates B) (x : X) (hx : x ∈ S.marks A) : F.dataMap x ∈ S.marks B := by
  obtain ⟨htype, p, hp, hxp⟩ := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.typeClass S hB x S.cellKind htype,
    p.image F.dataMap, F.dataTriples p hp, Finset.mem_image.mpr ⟨x, hxp, rfl⟩⟩

theorem incidenceLegal (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (hB : S.IncidenceLegal B) : S.IncidenceLegal A where
  candidates := F.hasCandidates S.codes hB.candidates
  oneRoot := F.oneRootRules S hB.candidates hB.oneRoot
  matching := fun e => F.matching S hB.candidates e (hB.matching e)
  oneMarker := F.oneMarker hB.oneMarker
  markerTypes := F.markerTypes S hB.candidates hB.markerTypes

variable [Inhabited Alphabet] [DecidableEq Alphabet]

noncomputable def computationalPullback (F : RootedEmbedding A B)
    (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (hB : S.IncidenceLegal B) :
    Realization.Pullback (rootedRealization S A color (F.incidenceLegal S hB).matching)
      (rootedRealization S B color hB.matching) where
  domain := Finset.univ
  map := fun x => F.dataMap x.val
  injective := by intro x y heq; exact Subtype.ext (F.dataMap.injective heq)
  J_domain := fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  R_domain := fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  S_domain := fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  marks_domain := Finset.subset_univ _
  J_preserve := fun x y hp => F.unionRelation S hB.candidates 0 x.val y.val hp
  R_preserve := fun x y hp => F.unionRelation S hB.candidates 1 x.val y.val hp
  S_preserve := fun x y hp => F.unionRelation S hB.candidates 2 x.val y.val hp
  label_preserve := by
    intro x hx
    obtain ⟨c, hc, _⟩ := (S.codes.mem_typeVertices A S.physical S.colorKind x.val).mp hx
    change decodedLabel S B color (F.dataMap x.val) = decodedLabel S A color x.val
    rw [decodedLabel_of_declared S B color _ c (F.declared S.codes hB.candidates x.val c hc),
      decodedLabel_of_declared S A color _ c hc]
  marks_preserve := fun x hx => F.marks S hB.candidates x.val hx

theorem rootedLegal (F : RootedEmbedding A B) (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (hB : RootedLegal S B color spec) :
    RootedLegal S A color spec := by
  obtain ⟨hinc, hcomp⟩ := hB
  exact ⟨F.incidenceLegal S hinc, (F.computationalPullback S color hinc).legal spec hcomp⟩

end RootedEmbedding

theorem rootedVertex_comp (ρ : Y → Option Roots) (f : X → Y) (x : X) :
    Sum.map id f (rootedVertex (ρ ∘ f) x) = rootedVertex ρ (f x) := by
  cases h : ρ (f x) <;> simp [rootedVertex, Function.comp_def, h]

theorem image_disjSum_map (f : X → Y) (r : Finset Roots) (d : Finset X) :
    (r.disjSum d).image (Sum.map id f) = r.disjSum (d.image f) := by
  ext z
  cases z with
  | inl r => simp
  | inr y => simp

def rootedImage_embedding (A : RGraph X 3) (B : RGraph Y 3) (f : X → Y)
    (hf : A.IsEmbedding B f) (ρ : VertexRooting Roots Y) :
    RootedEmbedding
      (rootedImage A (ρ.val ∘ f) (fun x y r hx hy => hf.1 (ρ.property (f x) (f y) r hx hy)))
      (rootedImage B ρ.val ρ.property) where
  dataMap := ⟨f, hf.1⟩
  edge_map := by
    intro p hp
    let hρ : ∀ x y r, (ρ.val ∘ f) x = some r → (ρ.val ∘ f) y = some r → x = y :=
      fun x y r hx hy => hf.1 (ρ.property (f x) (f y) r hx hy)
    have hsource := (split_edge_mem_iff (rootedImage A (ρ.val ∘ f) hρ) p.1 p.2).mp hp
    rw [rootedImage_toRGraph] at hsource
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hsource
    have ht := (rootedGraph_embedding B ρ.val ρ.property).2 (e.image f) (hf.2 e he)
    have heq' : (e.image f).image (rootedVertex ρ.val) = (p.1.disjSum p.2).image (Sum.map id f) := by
      rw [← heq, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro x _
      exact (rootedVertex_comp ρ.val f x).symm
    apply (split_edge_mem_iff (rootedImage B ρ.val ρ.property) p.1 (p.2.image f)).mpr
    rw [rootedImage_toRGraph, ← image_disjSum_map, ← heq']
    exact ht

theorem Admissible.of_embedding [Fintype X] [Fintype Y] [Fintype Roots]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet]
    (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet) (spec : Specification Alphabet)
    (A : RGraph X 3) (B : RGraph Y 3) (hB : Admissible S color spec B)
    (f : X → Y) (hf : A.IsEmbedding B f) : Admissible S color spec A := by
  obtain ⟨ρ, hlegal⟩ := hB
  refine ⟨⟨ρ.val ∘ f, fun x y r hx hy => hf.1 (ρ.property (f x) (f y) r hx hy)⟩, ?_⟩
  exact (rootedImage_embedding A B f hf ρ).rootedLegal S color spec hlegal

end TuranUniversality.Selector
