/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootedMonotonicity
public import TuranUniversality.Hypergraph.PartialRooting
public import TuranUniversality.Hypergraph.Relabel

/-! # Root assignments on retained vertex sets -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

variable {Roots X Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Fintype X] [DecidableEq X]

theorem rooting_range_card (μ : Rooting Roots X) : μ.range.card ≤ Fintype.card Roots := by
  have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset Roots)
    (fun r => (μ.val r).toFinset) 1 (by
      intro r _
      cases h : μ.val r <;> simp)
  simpa only [Rooting.range, Finset.card_univ, Nat.mul_one] using h

theorem inverse_none_iff (μ : Rooting Roots X) (x : X) :
    μ.inverse.val x = none ↔ x ∉ μ.range := by
  constructor
  · intro hnone hmem
    obtain ⟨r, hr⟩ := (Rooting.mem_range μ x).mp hmem
    have hi := (Rooting.inverse_some_iff μ x r).mpr hr
    rw [hnone] at hi
    cases hi
  · intro hnot
    cases h : μ.inverse.val x with
    | none => rfl
    | some r =>
        exact False.elim (hnot ((Rooting.mem_range μ x).mpr
          ⟨r, (Rooting.inverse_some_iff μ x r).mp h⟩))

/-- If no fresh root is assigned inside the witness, an extending rooting
has exactly the same inverse labels on that witness. -/
theorem inverse_eq_on_of_no_new_root (μ ν : Rooting Roots X) (S : Finset X)
    (hext : Rooting.Extends μ ν)
    (hnew : ¬ ∃ r x, μ.val r = none ∧ ν.val r = some x ∧ x ∈ S ∧ x ∉ μ.range) :
    ∀ x ∈ S, ν.inverse.val x = μ.inverse.val x := by
  intro x hx
  cases hμ : μ.inverse.val x with
  | some r =>
      exact (Rooting.inverse_some_iff ν x r).mpr
        (hext r x ((Rooting.inverse_some_iff μ x r).mp hμ))
  | none =>
      cases hν : ν.inverse.val x with
      | none => rfl
      | some r =>
          have hνr : ν.val r = some x := (Rooting.inverse_some_iff ν x r).mp hν
          have hμr : μ.val r = none := by
            cases hr : μ.val r with
            | none => rfl
            | some y =>
                have hyx : y = x := Option.some.inj ((hext r y hr).symm.trans hνr)
                have hi : μ.inverse.val x = some r := (Rooting.inverse_some_iff μ x r).mpr (hyx ▸ hr)
                rw [hμ] at hi
                cases hi
          exact False.elim (hnew ⟨r, x, hμr, hνr, hx, (inverse_none_iff μ x).mp hμ⟩)

noncomputable def rootedOn (G : RGraph X 3) (T : Finset X) (μ : Rooting Roots X) :
    RootedModel Roots T :=
  let ρ := μ.inverse.precompose (Function.Embedding.subtype (· ∈ T))
  rootedImage (G.pullback (Function.Embedding.subtype (· ∈ T))) ρ.val ρ.property

theorem inverse_map_precompose (T : Finset X) (ρ : VertexRooting Roots T) :
    (((Rooting.inverse ρ).map (Function.Embedding.subtype (· ∈ T))).inverse.precompose
      (Function.Embedding.subtype (· ∈ T))) = ρ := by
  apply Subtype.ext
  funext x
  have hiff (r : Roots) :
      ((Rooting.inverse ρ).map (Function.Embedding.subtype (· ∈ T))).inverse.val x.val = some r ↔
        ρ.val x = some r := by
    rw [Rooting.inverse_some_iff]
    exact (Rooting.map_some_iff (Rooting.inverse ρ) (Function.Embedding.subtype (· ∈ T)) r x).trans
      (Rooting.inverse_some_iff ρ r x)
  change ((Rooting.inverse ρ).map (Function.Embedding.subtype (· ∈ T))).inverse.val x.val = ρ.val x
  cases h : ρ.val x with
  | some r => exact (hiff r).mpr h
  | none =>
      cases hi : ((Rooting.inverse ρ).map (Function.Embedding.subtype (· ∈ T))).inverse.val x.val with
      | none => rfl
      | some r =>
          have he := (hiff r).mp hi
          rw [h] at he
          cases he

variable [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet]

theorem admissible_of_rootedOn_univ (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (G : RGraph X 3)
    (μ : Rooting Roots X) (h : RootedLegal S (rootedOn G Finset.univ μ) color spec) :
    Admissible S color spec G := by
  let T : Finset X := Finset.univ
  let ρ := μ.inverse.precompose (Function.Embedding.subtype (· ∈ T))
  have hsub : Admissible S color spec (G.pullback (Function.Embedding.subtype (· ∈ T))) := ⟨ρ, h⟩
  have hemb := RGraph.embedding_into_subset G G T
    (show G.IsEmbedding G id from ⟨Function.injective_id, RGraph.isHom_id G⟩)
    (fun x => Finset.mem_univ x)
  exact Admissible.of_embedding S color spec G _ hsub _ hemb

theorem exists_rootedOn_of_admissible (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (G : RGraph X 3) (T : Finset X)
    (h : Admissible S color spec (G.pullback (Function.Embedding.subtype (· ∈ T)))) :
    ∃ μ : Rooting Roots X, RootedLegal S (rootedOn G T μ) color spec := by
  obtain ⟨ρ, hρ⟩ := h
  let μ := (Rooting.inverse ρ).map (Function.Embedding.subtype (· ∈ T))
  refine ⟨μ, ?_⟩
  have heq := inverse_map_precompose T ρ
  change RootedLegal S (rootedImage (G.pullback (Function.Embedding.subtype (· ∈ T)))
    (μ.inverse.precompose (Function.Embedding.subtype (· ∈ T))).val
    (μ.inverse.precompose (Function.Embedding.subtype (· ∈ T))).property) color spec
  dsimp [μ]
  rw [heq]
  exact hρ

end TuranUniversality.Selector
