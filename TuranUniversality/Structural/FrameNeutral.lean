module

public import TuranUniversality.Structural.FrameTransport

@[expose] public section

/-! # Neutrality of all image data records

A nonneutral word pool has a fixed zero coordinate. The two endpoint
support families together contain all ten triples in each block; no
five-point permutation can send them all into one five-triple class.
-/

namespace TuranUniversality.Structural.Frame

open Cube Support TripleClasses

def phaseBase (a : Bool) : Finset (Fin 5) := if a then {0, 1, 3} else {0, 1, 2}

theorem phaseBase_mem (a : Bool) : phaseBase a ∈ (Pentagon.graph a).edges := by
  cases a <;> decide

/-- Preserving supports from both constant endpoint words is incompatible
with a fixed coordinate in the target word pool. -/
theorem no_fixed_target_coordinate {b : ℕ} (Ωsrc Ωdst : Finset (Word b))
    (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5))
    (hends : ∀ a : Bool, endpoint b a ∈ Ωsrc)
    (hmap : ∀ Z ∈ (poolGraph Ωsrc).edges,
      Z.image (blockMap π τ) ∈ (poolGraph Ωdst).edges)
    (j : Fin b) (hj : ∀ w ∈ Ωdst, j ∉ w) : False := by
  classical
  have himage (a : Bool) (E : Finset (Fin 5)) (hE : E ∈ (Pentagon.graph a).edges) :
      E.image (τ (π.symm j)) ∈ Pentagon.P0.edges := by
    let src : Choice (endpoint b a) := fun i =>
      ⟨if i = π.symm j then E else phaseBase a, by
        rw [blockGraph_endpoint]
        by_cases h : i = π.symm j
        · simpa [h] using hE
        · simpa [h] using phaseBase_mem a⟩
    have hs : choiceEdge (endpoint b a) src ∈ (poolGraph Ωsrc).edges :=
      Finset.mem_biUnion.mpr ⟨endpoint b a, hends a,
        (mem_wordGraph _ _).mpr ⟨src, rfl⟩⟩
    obtain ⟨w, hw, hZw⟩ := Finset.mem_biUnion.mp (hmap _ hs)
    obtain ⟨dst, hdst⟩ := (mem_wordGraph w _).mp hZw
    have heq : joinRows (fun k => ((src (π.symm k)).val).image (τ (π.symm k))) =
        joinRows (fun k => (dst k).val) := by
      calc
        _ = (choiceEdge (endpoint b a) src).image (blockMap π τ) :=
          (joinRows_image_blockMap π τ (fun i => (src i).val)).symm
        _ = choiceEdge w dst := hdst.symm
        _ = _ := rfl
    have hrow : E.image (τ (π.symm j)) = (dst j).val := by
      simpa [src] using congrFun (joinRows_injective heq) j
    rw [hrow]
    simpa [blockGraph, hj w hw, Pentagon.graph] using (dst j).property
  have hfalse (a : Bool) : imageClasses (τ (π.symm j)) a ⊆ {false} := by
    intro c hc
    obtain ⟨E, hE, hc⟩ := (mem_imageClasses _ _ _).mp hc
    have heq := pentagon_phase_unique c false (E.image (τ (π.symm j))) hc (himage a E hE)
    simp [heq]
  have hall := (permutation_phase_data (τ (π.symm j))).2.1
  have ht : true ∈ imageClasses (τ (π.symm j)) false ∪ imageClasses (τ (π.symm j)) true := by
    rw [hall]; simp
  rcases Finset.mem_union.mp ht with ht | ht
  · simpa using hfalse false ht
  · simpa using hfalse true ht

theorem neutral_endpoints (p q : ℕ) (hpq : p ≤ q) (a : Bool) :
    endpoint (CodePools.blockCount q) a ∈ CodePools.pool p q hpq CodePools.neutralLabel := by
  rw [CodePools.neutral_pool]
  exact Finset.mem_union_left _ (endpoint_mem_prefixPath _ a)

/-- Every four-set of frame data is sent to an existing neutral record. -/
theorem image_records_neutral {V : Type*} [DecidableEq V] (p q : ℕ)
    (hpq : p ≤ q) (hq : 0 < q) {t : ℕ} {R : RecordSystem V}
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5)) (d : Fin 5 → V)
    (hf : (graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) R) (vertexMap σ π τ d))
    (X : Finset (Fin 5)) (hX : X.card = 4) :
    X.image d ∈ R.recorded.edges ∧ R.label (X.image d) = CodePools.neutralLabel := by
  have hmap (Z : Finset (Support.Vertex (CodePools.blockCount q)))
      (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq CodePools.neutralLabel)).edges) :
      Z.image (blockMap π τ) ∈ (poolGraph (CodePools.pool p q hpq (R.label (X.image d)))).edges :=
    (transported_support σ π τ d hf hX hZ).2
  have hrec : X.image d ∈ R.recorded.edges := by
    obtain ⟨Z, hZ⟩ := wordGraph_nonempty (endpoint (CodePools.blockCount q) false)
    exact (transported_support σ π τ d hf hX
      (Finset.mem_biUnion.mpr ⟨_, neutral_endpoints p q hpq false, hZ⟩)).1
  refine ⟨hrec, ?_⟩
  by_contra hnon
  exact no_fixed_target_coordinate
    (CodePools.pool p q hpq CodePools.neutralLabel) (CodePools.pool p q hpq (R.label (X.image d)))
    π τ (neutral_endpoints p q hpq) hmap (firstIndex (CodePools.exponent q))
    (fun w hw => (CodePools.nonneutral_word_fixed p q hpq hnon hw).2)

/-- Once roles are recovered, the block action must be exactly identity or
reverse-complementation; it cannot merge or permute the record labels. -/
theorem neutral_block_action {V : Type*} [DecidableEq V] (p q : ℕ)
    (hpq : p ≤ q) (hq : 0 < q) {t : ℕ} {R : RecordSystem V}
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5)) (d : Fin 5 → V)
    (hf : (graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) R) (vertexMap σ π τ d)) :
    (π = Equiv.refl _ ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph a).edges) ∨
      (π = Fin.revPerm ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph (!a)).edges) := by
  apply actual_pool_stabilizer p q hpq hq π τ
  intro Z hZ
  have hX : ({0, 1, 2, 3} : Finset (Fin 5)).card = 4 := by decide
  have hl := (image_records_neutral p q hpq hq σ π τ d hf _ hX).2
  simpa only [hl] using (transported_support σ π τ d hf hX hZ).2

end TuranUniversality.Structural.Frame
