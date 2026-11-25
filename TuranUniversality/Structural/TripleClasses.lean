module

public import TuranUniversality.Structural.CubeBoxes
public import TuranUniversality.Structural.BlockSupports
public import TuranUniversality.Structural.CodePools

@[expose] public section

/-! # Preservation of pentagon triple classes (Claim 8.3)

The hypotheses concern actual images of ordinary support edges under actual
five-point permutations in each block. Only the two endpoint support families
are needed. A mixed block would give two coordinate boxes in the neutral
pool that both vary in the same direction, contradicting the prefix geometry.
-/

namespace TuranUniversality.Structural.TripleClasses

open Cube Support

def imageEdges (τ : Equiv.Perm (Fin 5)) (a : Bool) : Finset (Finset (Fin 5)) :=
  (Pentagon.graph a).edges.image (fun e => e.image τ)

def imageClasses (τ : Equiv.Perm (Fin 5)) (a : Bool) : Finset Bool :=
  Finset.univ.filter fun c =>
    ∃ e ∈ (Pentagon.graph a).edges, e.image τ ∈ (Pentagon.graph c).edges

@[simp] theorem mem_imageClasses (τ : Equiv.Perm (Fin 5)) (a c : Bool) :
    c ∈ imageClasses τ a ↔
      ∃ e ∈ (Pentagon.graph a).edges, e.image τ ∈ (Pentagon.graph c).edges := by
  simp [imageClasses]

def switched (a flip : Bool) : Bool := if flip then !a else a

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem permutation_phase_data : ∀ τ : Equiv.Perm (Fin 5),
    (∀ a : Bool, (imageClasses τ a).Nonempty) ∧
    imageClasses τ false ∪ imageClasses τ true = Finset.univ ∧
    ((∃ flip : Bool, ∀ a : Bool,
      imageEdges τ a = (Pentagon.graph (switched a flip)).edges) ∨
      (imageClasses τ false = Finset.univ ∧ imageClasses τ true = Finset.univ)) := by
  decide

def blockMap {b : ℕ} (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5)) :
    Vertex b → Vertex b := fun v => ⟨π v.1, τ v.1 v.2⟩

theorem blockMap_injective {b : ℕ} (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) : Function.Injective (blockMap π τ) := by
  rintro ⟨i, a⟩ ⟨j, c⟩ h
  have hij : i = j := π.injective (congrArg Sigma.fst h)
  subst j
  have hac : a = c := (τ i).injective (by simpa [blockMap] using h)
  subst c
  rfl

theorem joinRows_image_blockMap {b : ℕ} (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (es : Fin b → Finset (Fin 5)) :
    (joinRows es).image (blockMap π τ) =
      joinRows (fun j => (es (π.symm j)).image (τ (π.symm j))) := by
  ext v
  rcases v with ⟨j, c⟩
  simp only [Finset.mem_image, mem_joinRows]
  constructor
  · rintro ⟨⟨i, a⟩, ha, heq⟩
    have hij : i = π.symm j := (Equiv.eq_symm_apply π).mpr (congrArg Sigma.fst heq)
    subst i
    refine ⟨a, (mem_joinRows es (π.symm j) a).mp ha, ?_⟩
    have h := congrArg (fun v : Vertex b => v.2) heq
    exact h
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨π.symm j, a⟩, (mem_joinRows es (π.symm j) a).mpr ha, ?_⟩
    simp [blockMap]

def endpoint (b : ℕ) (a : Bool) : Word b := if a then Finset.univ else ∅

@[simp] theorem blockGraph_endpoint {b : ℕ} (a : Bool) (i : Fin b) :
    blockGraph (endpoint b a) i = Pentagon.graph a := by
  cases a <;> simp [endpoint, blockGraph]

def targetBox {b : ℕ} (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5))
    (a : Bool) (j : Fin b) : Finset Bool := imageClasses (τ (π.symm j)) a

theorem targetBox_subset_pool {b : ℕ} (Ω : Finset (Word b))
    (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5)) (a : Bool)
    (hmap : ∀ e ∈ (wordGraph (endpoint b a)).edges,
      e.image (blockMap π τ) ∈ (poolGraph Ω).edges)
    (w : Word b) (hw : InBox (targetBox π τ a) w) : w ∈ Ω := by
  classical
  have hchoice (i : Fin b) : ∃ e ∈ (Pentagon.graph a).edges,
      e.image (τ i) ∈ (blockGraph w (π i)).edges := by
    have hi := hw (π i)
    simp only [targetBox, Equiv.symm_apply_apply, mem_imageClasses] at hi
    exact hi
  choose es hes hetarget using hchoice
  let source : Choice (endpoint b a) := fun i => ⟨es i, by simpa using hes i⟩
  let target : Choice w := fun j => ⟨(es (π.symm j)).image (τ (π.symm j)), by
    simpa only [Equiv.apply_symm_apply] using hetarget (π.symm j)⟩
  have heq : (choiceEdge (endpoint b a) source).image (blockMap π τ) = choiceEdge w target :=
    joinRows_image_blockMap π τ es
  have hsource : choiceEdge (endpoint b a) source ∈ (wordGraph (endpoint b a)).edges :=
    (mem_wordGraph _ _).mpr ⟨source, rfl⟩
  have htarget := hmap _ hsource
  rw [heq] at htarget
  obtain ⟨u, hu, hue⟩ := Finset.mem_biUnion.mp htarget
  have hwu : w = u := word_eq_of_common_edge
    ((mem_wordGraph w _).mpr ⟨target, rfl⟩) hue
  exact hwu ▸ hu

/-- Actual blockwise support preservation forces each five-point bijection
to preserve both triple classes or exchange them. -/
theorem triple_class_preservation {b : ℕ} (hb : 2 ≤ b)
    (extra : Finset (Word b)) (he : IsolatedExtras b extra)
    (π : Equiv.Perm (Fin b)) (τ : Fin b → Equiv.Perm (Fin 5))
    (hmap : ∀ a : Bool, ∀ e ∈ (wordGraph (endpoint b a)).edges,
      e.image (blockMap π τ) ∈ (poolGraph (prefixPath b ∪ extra)).edges) :
    ∀ i, ∃ flip : Bool, ∀ a : Bool,
      imageEdges (τ i) a = (Pentagon.graph (switched a flip)).edges := by
  have hD (a : Bool) (j : Fin b) : (targetBox π τ a j).Nonempty :=
    (permutation_phase_data (τ (π.symm j))).1 a
  have hcover (j : Fin b) : targetBox π τ false j ∪ targetBox π τ true j = Finset.univ :=
    (permutation_phase_data (τ (π.symm j))).2.1
  have hbox (a : Bool) (w : Word b) (hw : InBox (targetBox π τ a) w) :
      w ∈ prefixPath b ∪ extra := targetBox_subset_pool _ π τ a (hmap a) w hw
  intro i
  rcases (permutation_phase_data (τ i)).2.2 with h | h
  · exact h
  · exfalso
    apply boxes_not_both_full hb he (targetBox π τ) hD hcover hbox (π i)
    simpa only [targetBox, Equiv.symm_apply_apply] using h

/-- Specialization to the constructed neutral code pool. -/
theorem actual_pool_triple_classes (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q)
    (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5))
    (hmap : ∀ a : Bool, ∀ e ∈ (wordGraph (endpoint (CodePools.blockCount q) a)).edges,
      e.image (blockMap π τ) ∈
        (poolGraph (CodePools.pool p q hpq CodePools.neutralLabel)).edges) :
    ∀ i, ∃ flip : Bool, ∀ a : Bool,
      imageEdges (τ i) a = (Pentagon.graph (switched a flip)).edges := by
  apply triple_class_preservation (le_trans (by decide : 2 ≤ 4) (CodePools.blockCount_ge_four q hq))
    (CodePools.extra p q hpq 0) (CodePools.neutral_extras_isolated p q hpq hq) π τ
  simpa only [CodePools.neutral_pool] using hmap

end TuranUniversality.Structural.TripleClasses
