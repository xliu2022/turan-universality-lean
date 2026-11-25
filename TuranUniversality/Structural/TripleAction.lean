module

public import TuranUniversality.Structural.TripleClasses

@[expose] public section

/-! # From actual support maps to the two neutral-pool actions

After Claim 8.3 each block map has a well-defined bit flip. These flips and
the actual permutation of blocks induce a cube isometry. Its action is
derived from images of support edges, and the neutral pool forces either
the identity or reversal of all blocks together with all bit flips.
-/

namespace TuranUniversality.Structural.TripleClasses

open Cube Support
open scoped symmDiff

/-- Flips are indexed in the target coordinate order. -/
def flipWord {b : ℕ} (π : Equiv.Perm (Fin b)) (f : Fin b → Bool) : Word b :=
  Finset.univ.filter fun j => f (π.symm j) = true

@[simp] theorem flipWord_bit {b : ℕ} (π : Equiv.Perm (Fin b))
    (f : Fin b → Bool) (i : Fin b) :
    decide (π i ∈ flipWord π f) = f i := by
  simp [flipWord]

theorem wordAction_bit {b : ℕ} (π : Equiv.Perm (Fin b))
    (f : Fin b → Bool) (w : Word b) (i : Fin b) :
    decide (π i ∈ wordAction π (flipWord π f) w) =
      switched (decide (i ∈ w)) (f i) := by
  cases hf : f i <;> by_cases hi : i ∈ w <;>
    simp [wordAction, flipWord, switched, Finset.mem_symmDiff,
      Finset.mem_map_equiv, hf, hi]

theorem blockGraph_wordAction {b : ℕ} (π : Equiv.Perm (Fin b))
    (f : Fin b → Bool) (w : Word b) (j : Fin b) :
    blockGraph (wordAction π (flipWord π f) w) j =
      Pentagon.graph (switched (decide (π.symm j ∈ w)) (f (π.symm j))) := by
  unfold blockGraph
  congr 1
  simpa only [Equiv.apply_symm_apply] using wordAction_bit π f w (π.symm j)

theorem pentagon_edges_nonempty (a : Bool) : (Pentagon.graph a).edges.Nonempty := by
  cases a <;> decide

theorem wordGraph_nonempty {b : ℕ} (w : Word b) : (wordGraph w).edges.Nonempty := by
  classical
  have h (i : Fin b) : (blockGraph w i).edges.Nonempty :=
    pentagon_edges_nonempty (decide (i ∈ w))
  choose es hes using h
  let c : Choice w := fun i => ⟨es i, hes i⟩
  exact ⟨choiceEdge w c, (mem_wordGraph w _).mpr ⟨c, rfl⟩⟩

/-- The image is an edge of the word selected by the actual coordinate
permutation and the actual blockwise triple-class actions. -/
theorem image_wordGraph_edge {b : ℕ} (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (f : Fin b → Bool)
    (hf : ∀ i a, imageEdges (τ i) a = (Pentagon.graph (switched a (f i))).edges)
    (w : Word b) (e : Finset (Vertex b)) (he : e ∈ (wordGraph w).edges) :
    e.image (blockMap π τ) ∈ (wordGraph (wordAction π (flipWord π f) w)).edges := by
  classical
  obtain ⟨c, rfl⟩ := (mem_wordGraph w e).mp he
  let d : Choice (wordAction π (flipWord π f) w) := fun j =>
    ⟨((c (π.symm j)).val).image (τ (π.symm j)), by
      rw [blockGraph_wordAction]
      rw [← hf (π.symm j) (decide (π.symm j ∈ w))]
      exact Finset.mem_image.mpr ⟨(c (π.symm j)).val, (c (π.symm j)).property, rfl⟩⟩
  apply (mem_wordGraph _ _).mpr
  refine ⟨d, ?_⟩
  exact (joinRows_image_blockMap π τ (fun i => (c i).val)).symm

/-- Support-edge preservation implies preservation of the underlying word
pool; no word-level preservation is assumed. -/
theorem pool_action_preservation {b : ℕ} (Ω : Finset (Word b))
    (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5)) (f : Fin b → Bool)
    (hf : ∀ i a, imageEdges (τ i) a = (Pentagon.graph (switched a (f i))).edges)
    (hmap : ∀ e ∈ (poolGraph Ω).edges,
      e.image (blockMap π τ) ∈ (poolGraph Ω).edges) :
    ∀ w ∈ Ω, wordAction π (flipWord π f) w ∈ Ω := by
  intro w hw
  obtain ⟨e, he⟩ := wordGraph_nonempty w
  have hm := hmap e (Finset.mem_biUnion.mpr ⟨w, hw, he⟩)
  obtain ⟨v, hv, hve⟩ := Finset.mem_biUnion.mp hm
  have hword : wordAction π (flipWord π f) w = v :=
    word_eq_of_common_edge (image_wordGraph_edge π τ f hf w e he) hve
  exact hword ▸ hv

theorem endpoint_mem_prefixPath (b : ℕ) (a : Bool) : endpoint b a ∈ prefixPath b := by
  cases a
  · simpa [endpoint] using prefix_mem_prefixPath b 0 (Nat.zero_le b)
  · simpa [endpoint] using prefix_mem_prefixPath b b (le_refl b)

/-- The actual blockwise stabilizer of a neutral support graph has only two
actions on blocks and triple classes. Internal pentagon automorphisms remain
free in each block. -/
theorem blockwise_pool_stabilizer {b : ℕ} (hb : 2 ≤ b)
    (extra : Finset (Word b)) (he : IsolatedExtras b extra)
    (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5))
    (hmap : ∀ e ∈ (poolGraph (prefixPath b ∪ extra)).edges,
      e.image (blockMap π τ) ∈ (poolGraph (prefixPath b ∪ extra)).edges) :
    (π = Equiv.refl (Fin b) ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph a).edges) ∨
      (π = Fin.revPerm ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph (!a)).edges) := by
  classical
  have hends : ∀ a : Bool, ∀ e ∈ (wordGraph (endpoint b a)).edges,
      e.image (blockMap π τ) ∈ (poolGraph (prefixPath b ∪ extra)).edges := by
    intro a e he'
    exact hmap e (Finset.mem_biUnion.mpr ⟨endpoint b a,
      Finset.mem_union_left _ (endpoint_mem_prefixPath b a), he'⟩)
  choose f hf using triple_class_preservation hb extra he π τ hends
  have hpool := pool_action_preservation (prefixPath b ∪ extra) π τ f hf hmap
  rcases action_stabilizer (by omega : 0 < b) he π (flipWord π f) hpool with
    ⟨hflips, hπ⟩ | ⟨hflips, hπ⟩
  · refine Or.inl ⟨hπ, ?_⟩
    intro i a
    have hfi : f i = false := by
      simpa only [flipWord_bit, Finset.notMem_empty, decide_false] using
        congrArg (fun w : Word b => decide (π i ∈ w)) hflips
    simpa [switched, hfi] using hf i a
  · refine Or.inr ⟨hπ, ?_⟩
    intro i a
    have hfi : f i = true := by
      simpa only [flipWord_bit, Finset.mem_univ, decide_true] using
        congrArg (fun w : Word b => decide (π i ∈ w)) hflips
    simpa [switched, hfi] using hf i a

/-- The two-action conclusion for the concrete seven-pool construction. -/
theorem actual_pool_stabilizer (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q)
    (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5))
    (hmap : ∀ e ∈ (poolGraph (CodePools.pool p q hpq CodePools.neutralLabel)).edges,
      e.image (blockMap π τ) ∈
        (poolGraph (CodePools.pool p q hpq CodePools.neutralLabel)).edges) :
    (π = Equiv.refl _ ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph a).edges) ∨
      (π = Fin.revPerm ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph (!a)).edges) := by
  apply blockwise_pool_stabilizer
    (le_trans (by decide : 2 ≤ 4) (CodePools.blockCount_ge_four q hq))
    (CodePools.extra p q hpq 0) (CodePools.neutral_extras_isolated p q hpq hq) π τ
  simpa only [CodePools.neutral_pool] using hmap

end TuranUniversality.Structural.TripleClasses
