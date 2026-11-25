module

public import TuranUniversality.Structural.FrameNeutral
public import TuranUniversality.Structural.PentagonSymmetry

@[expose] public section

/-! # Neutral-frame rigidity and the converse support action

Every ordinary frame homomorphism has the stated root and data roles and
the identity/dihedral or reversed/exchanged block action. Conversely those
actions preserve each of the seven pools separately, and therefore act on
every completed record model.
-/

namespace TuranUniversality.Structural.Frame

open Cube Support TripleClasses

def AllowedBlockAction {b : ℕ} (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) : Prop :=
  (π = Equiv.refl _ ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph a).edges) ∨
    (π = Fin.revPerm ∧ ∀ i a, imageEdges (τ i) a = (Pentagon.graph (!a)).edges)

theorem allowed_pool_preservation (p q : ℕ) (hpq : p ≤ q)
    (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5)) (hact : AllowedBlockAction π τ)
    (l : Label) (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq l)).edges) :
    Z.image (blockMap π τ) ∈ (poolGraph (CodePools.pool p q hpq l)).edges := by
  obtain ⟨w, hw, hZw⟩ := Finset.mem_biUnion.mp hZ
  rcases hact with ⟨rfl, hτ⟩ | ⟨rfl, hτ⟩
  · have h := image_wordGraph_edge (Equiv.refl _) τ (fun _ => false)
      (by simpa [switched] using hτ) w Z hZw
    have hword : wordAction (Equiv.refl _) (flipWord (Equiv.refl _) (fun _ => false)) w = w := by
      simp [flipWord, wordAction]
    rw [hword] at h
    exact Finset.mem_biUnion.mpr ⟨w, hw, h⟩
  · have h := image_wordGraph_edge Fin.revPerm τ (fun _ => true)
      (by simpa [switched] using hτ) w Z hZw
    have hword : wordAction Fin.revPerm (flipWord Fin.revPerm (fun _ => true)) w =
        reverseComplement w := by
      simp only [flipWord, Finset.filter_true, ← reverseComplement_eq_action]
    rw [hword] at h
    exact Finset.mem_biUnion.mpr ⟨reverseComplement w,
      CodePools.reverseComplement_mem_pool p q hpq l hw, h⟩

/-- Ordinary frame homomorphisms recover the actual roles, neutral records,
and the only two possible actions on blocks and triple classes. -/
theorem rigidity {V : Type*} [DecidableEq V] (p q : ℕ)
    (hpq : p ≤ q) (hq : 0 < q) {t : ℕ} {R : RecordSystem V}
    {f : Compiled.Vertex (CodePools.blockCount q) t (Fin 5) →
      Compiled.Vertex (CodePools.blockCount q) t V}
    (hf : (graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) R) f) :
    ∃ σ : Equiv.Perm (Fin t), ∃ π : Equiv.Perm (Fin (CodePools.blockCount q)),
      ∃ τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5), ∃ d : Fin 5 → V,
        Function.Injective d ∧ f = vertexMap σ π τ d ∧ AllowedBlockAction π τ ∧
        (∀ X : Finset (Fin 5), X.card = 4 →
          X.image d ∈ R.recorded.edges ∧ R.label (X.image d) = CodePools.neutralLabel) := by
  have hzero : ∅ ∈ CodePools.pool p q hpq CodePools.neutralLabel :=
    neutral_endpoints p q hpq false
  obtain ⟨σ, π, τ, d, hd, hs, hb, hdata⟩ := roles hzero hf
  have hmap := roles_eq_map σ π τ d hs hb hdata
  have hf' : (graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) R) (vertexMap σ π τ d) := hmap ▸ hf
  exact ⟨σ, π, τ, d, hd, hmap, neutral_block_action p q hpq hq σ π τ d hf',
    image_records_neutral p q hpq hq σ π τ d hf'⟩

/-- The permitted actions act on any completed records, independently of
local legality. Each label's own supports are preserved. -/
theorem compiled_action (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5)) (hact : AllowedBlockAction π τ)
    (R : RecordSystem (Fin 5)) :
    (Compiled.graph t (CodePools.pool p q hpq) R).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) R) (vertexMap σ π τ id) := by
  intro e he
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (Compiled.mem_graph _ _ _).mp he
  rw [image_edge, Finset.image_id]
  exact (Compiled.mem_graph _ _ _).mpr ⟨X, hX, Z.image (blockMap π τ),
    allowed_pool_preservation p q hpq π τ hact _ Z hZ, rfl⟩

theorem frame_action (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5)) (hact : AllowedBlockAction π τ) :
    (graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel))
      (vertexMap σ π τ id) := by
  have hgraph : graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel) =
      Compiled.graph t (CodePools.pool p q hpq) neutralRecords := by
    rfl
  rw [hgraph]
  exact compiled_action p q hpq σ π τ hact neutralRecords

end TuranUniversality.Structural.Frame
