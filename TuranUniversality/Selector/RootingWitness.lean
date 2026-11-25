/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootingSupport
public import TuranUniversality.Selector.LocalRootedWitness

/-! # Persistence of bounded witnesses under extensions of rootings -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

variable {Roots X Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Fintype X] [DecidableEq X]

/-- Every edge in a small rooted witness is retained when all old roots
and its data vertices survive, and their labels have not changed. -/
noncomputable def witness_embedding_on
    (G : RGraph X 3) (μ ν : Rooting Roots X) (W T : Finset X)
    (hST : μ.range ∪ W ⊆ T)
    (hagree : ∀ x ∈ μ.range ∪ W, ν.inverse.val x = μ.inverse.val x) :
    RootedEmbedding ((rootedImage G μ.inverse.val μ.inverse.property).restrictData W)
      (rootedOn G T ν) := by
  let incl : W ↪ T :=
    ⟨fun x => ⟨x.val, hST (Finset.mem_union_right _ x.property)⟩,
      fun x y h => Subtype.ext (congrArg (fun z : T => z.val) h)⟩
  refine ⟨incl, ?_⟩
  intro p hp
  have hM := ((rootedImage G μ.inverse.val μ.inverse.property).mem_restrictData W p.1 p.2).mp hp
  have hg := (split_edge_mem_iff (rootedImage G μ.inverse.val μ.inverse.property)
    p.1 (p.2.image Subtype.val)).mp hM
  rw [rootedImage_toRGraph] at hg
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hg
  have heSupport : e ⊆ μ.range ∪ W := by
    intro x hx
    cases hμ : μ.inverse.val x with
    | some r =>
        exact Finset.mem_union_left _ ((Rooting.mem_range μ x).mpr
          ⟨r, (Rooting.inverse_some_iff μ x r).mp hμ⟩)
    | none =>
        have hm : rootedVertex μ.inverse.val x ∈ p.1.disjSum (p.2.image Subtype.val) :=
          heq ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have hxdata : x ∈ p.2.image (Subtype.val : W → X) := by
          simpa [rootedVertex, hμ] using hm
        obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hxdata
        exact Finset.mem_union_right _ (hw ▸ w.property)
  have heT : e ⊆ T := heSupport.trans hST
  let eT := liftDataSet T e
  have him : eT.image Subtype.val = e := liftDataSet_image T e heT
  let GT := G.pullback (Function.Embedding.subtype (· ∈ T))
  have heGT : eT ∈ GT.edges := by
    apply (G.mem_pullback _ _).mpr
    constructor
    · calc
        eT.card = (eT.image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ = e.card := congrArg Finset.card him
        _ = 3 := G.uniform e he
    · rw [Finset.map_eq_image]
      change eT.image (Subtype.val : T → X) ∈ G.edges
      rw [him]
      exact he
  let ρ := ν.inverse.precompose (Function.Embedding.subtype (· ∈ T))
  have htarget := (rootedGraph_embedding GT ρ.val ρ.property).2 eT heGT
  have heqTarget : eT.image (rootedVertex ρ.val) = p.1.disjSum (p.2.image incl) := by
    apply Finset.image_injective (Function.injective_id.sumMap (Subtype.val_injective (p := (· ∈ T))))
    calc
      (eT.image (rootedVertex ρ.val)).image (Sum.map id (Subtype.val : T → X)) =
          eT.image (fun v : T => rootedVertex μ.inverse.val v.val) := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro v hv
        change Sum.map id (Subtype.val : T → X)
          (rootedVertex (ν.inverse.val ∘ Subtype.val) v) = rootedVertex μ.inverse.val v.val
        rw [rootedVertex_comp]
        unfold rootedVertex
        rw [hagree v.val (heSupport ((mem_liftDataSet T e v).mp hv))]
      _ = (eT.image (Subtype.val : T → X)).image (rootedVertex μ.inverse.val) :=
        by rw [Finset.image_image]; rfl
      _ = p.1.disjSum (p.2.image Subtype.val) := by rw [him, heq]
      _ = (p.1.disjSum (p.2.image incl)).image (Sum.map id (Subtype.val : T → X)) := by
        rw [image_disjSum_map, Finset.image_image]
        rfl
  apply (split_edge_mem_iff (rootedOn G T ν) p.1 (p.2.image incl)).mpr
  change p.1.disjSum (p.2.image incl) ∈ (rootedImage GT ρ.val ρ.property).toRGraph.edges
  rw [rootedImage_toRGraph]
  exact heqTarget ▸ htarget

variable [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet]

/-- A failed rooting has a bounded witness which can only be repaired by
assigning a fresh root to a vertex of that witness. -/
theorem failed_rooting_witness (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (G : RGraph X 3)
    (hG : ¬ Admissible S color spec G) (μ : Rooting Roots X) :
    ∃ W : Finset X, W.card ≤ Fintype.card Roots + rootedWitnessBound spec ∧
      ∀ T ν, W ⊆ T → Rooting.Extends μ ν → RootedLegal S (rootedOn G T ν) color spec →
        ∃ r x, μ.val r = none ∧ ν.val r = some x ∧ x ∈ W ∧ x ∉ μ.range := by
  classical
  have hbad : ¬ RootedLegal S (rootedImage G μ.inverse.val μ.inverse.property) color spec :=
    fun h => hG ⟨μ.inverse, h⟩
  obtain ⟨D, hD, hfailure⟩ := small_rooted_witness S
    (rootedImage G μ.inverse.val μ.inverse.property) color spec hbad
  refine ⟨μ.range ∪ D, ?_, ?_⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add (rooting_range_card μ) hD)
  · intro T ν hsub hext hlegal
    by_contra hnew
    have hagree := inverse_eq_on_of_no_new_root μ ν (μ.range ∪ D) hext hnew
    exact hfailure ((witness_embedding_on G μ ν D T hsub hagree).rootedLegal S color spec hlegal)

open scoped BigOperators

/-- The explicit finite search-tree bound after eliminating at most `q`
root labels, with local witness size at most `w`. -/
def rootSearchBound (q w : ℕ) : ℕ :=
  w * ∑ j ∈ Finset.range (q + 1), (q * w) ^ j

def admissibleWitnessBound (Roots : Type*) [Fintype Roots] (spec : Specification Alphabet) : ℕ :=
  rootSearchBound (Fintype.card Roots) (Fintype.card Roots + rootedWitnessBound spec)

/-- Every inadmissible actual graph contains an inadmissible induced
subgraph with the explicit order bound from finite root elimination. -/
theorem bounded_nonadmissible_subgraph (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (G : RGraph X 3)
    (hG : ¬ Admissible S color spec G) :
    ∃ T : Finset X, T.card ≤ admissibleWitnessBound Roots spec ∧
      ¬ Admissible S color spec (G.pullback (Function.Embedding.subtype (· ∈ T))) := by
  classical
  let LegalOn : Finset X → Rooting Roots X → Prop := fun T μ =>
    RootedLegal S (rootedOn G T μ) color spec
  have hfailed (μ : Rooting Roots X) : ¬ LegalOn Finset.univ μ :=
    fun h => hG (admissible_of_rootedOn_univ S color spec G μ h)
  have hwitness (μ : Rooting Roots X) (_ : ¬ LegalOn Finset.univ μ) :=
    failed_rooting_witness S color spec G hG μ
  obtain ⟨T, hT, hbad⟩ := Rooting.bounded_obstruction LegalOn
    (Fintype.card Roots + rootedWitnessBound spec) hfailed hwitness
  refine ⟨T, hT, ?_⟩
  intro h
  obtain ⟨ν, hν⟩ := exists_rootedOn_of_admissible S color spec G T h
  exact hbad ν hν

end TuranUniversality.Selector
