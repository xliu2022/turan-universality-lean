/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.FiniteBasis
public import TuranUniversality.Hypergraph.Clique

/-! # Nonemptiness of the actual guarded forbidden basis -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

variable {Roots X Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Fintype X] [DecidableEq X]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet]

/-- Four unrooted vertices already give four marker edges in a complete
3-graph. Thus a clique with at least `q + 4` vertices admits no legal rooting. -/
theorem clique_not_admissible (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet)
    (hX : Fintype.card Roots + 4 ≤ Fintype.card X) :
    ¬ Admissible S color spec (RGraph.clique X 3) := by
  classical
  rintro ⟨ρ, hinc, _⟩
  let μ : Rooting Roots X := Rooting.inverse ρ
  let D : Finset X := Finset.univ \ μ.range
  have hnone (x : X) : ρ.val x = none ↔ x ∉ μ.range := by
    simpa only [μ, Rooting.inverse_inverse] using inverse_none_iff μ x
  have hDcard : 4 ≤ D.card := by
    have hroot := rooting_range_card μ
    have hcard : D.card = Fintype.card X - μ.range.card := by
      simp [D, Finset.card_sdiff_of_subset]
    omega
  let M := rootedImage (RGraph.clique X 3) ρ.val ρ.property
  have hsub : D.powersetCard 3 ⊆ M.dataTriples := by
    intro e he
    obtain ⟨heD, hecard⟩ := Finset.mem_powersetCard.mp he
    apply (M.mem_dataTriples e).mpr
    apply (split_edge_mem_iff M ∅ e).mpr
    have heG : e ∈ (RGraph.clique X 3).edges := (RGraph.mem_clique e).mpr hecard
    have him := (rootedGraph_embedding (RGraph.clique X 3) ρ.val ρ.property).2 e heG
    have heq : e.image (rootedVertex ρ.val) = (∅ : Finset Roots).disjSum e := by
      calc
        e.image (rootedVertex ρ.val) = e.image (Sum.inr : X → Roots ⊕ X) := by
          apply Finset.image_congr
          intro x hx
          exact (rootedVertex_eq_inr ρ.val x x).mpr
            ⟨rfl, (hnone x).mpr (Finset.mem_sdiff.mp (heD hx)).2⟩
        _ = (∅ : Finset Roots).disjSum e := by
          rw [Finset.empty_disjSum, Finset.map_eq_image]
          rfl
    simpa only [M, rootedImage_toRGraph, heq] using him
  have hmarker : M.dataTriples.card ≤ 1 := hinc.oneMarker
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_powersetCard] at hcount
  have hfour := Nat.choose_le_choose 3 hDcard
  norm_num at hfour
  omega

omit [Fintype X] [DecidableEq X] in
/-- Every finite graph embeds in a clique of sufficiently large order. -/
theorem finiteGraph_contains_clique (G : FiniteGraph 3) (n : ℕ) (hn : G.1 ≤ n) :
    G.Contains ⟨n, RGraph.clique (Fin n) 3⟩ := by
  let f : Fin G.1 ↪ Fin n := Fin.castLEEmb hn
  refine ⟨f, f.injective, ?_⟩
  intro e he
  apply (RGraph.mem_clique _).mpr
  rw [Finset.card_image_of_injective _ f.injective]
  exact G.2.uniform e he

omit [Fintype X] [DecidableEq X] in
/-- The guarded basis is nonempty for every finite guard. A sufficiently
large clique contains that guard and violates the marker rule under every rooting. -/
theorem guardedAdmissibleBasis_nonempty (S : CompilerSignature Roots Code Kinds L)
    (color : Code → Alphabet) (spec : Specification Alphabet) (H : FiniteGraph 3) :
    (guardedAdmissibleBasis S color spec H).Nonempty := by
  classical
  let n := max (Fintype.card Roots + 4) H.1
  let G : FiniteGraph 3 := ⟨n, RGraph.clique (Fin n) 3⟩
  have hsize : Fintype.card Roots + 4 ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using (le_max_left (Fintype.card Roots + 4) H.1)
  have hbad : ¬ admissibleClass S color spec G :=
    clique_not_admissible S color spec hsize
  have hH : H.Contains G := finiteGraph_contains_clique H n (le_max_right _ _)
  by_contra hempty
  have havoid : ∀ A ∈ guardedAdmissibleBasis S color spec H, ¬ A.Contains G := by
    intro A hA
    exact False.elim (hempty ⟨A, hA⟩)
  rcases (guardedAdmissibleBasis_spec S color spec H G).mpr havoid with hG | hG
  · exact hbad hG
  · exact hG hH

end TuranUniversality.Selector
