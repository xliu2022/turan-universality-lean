module

public import TuranUniversality.Structural.VertexExtensionFinite
public import TuranUniversality.Structural.ReplacementFrameTransport

@[expose] public section

/-! # Vertex extension formulated on the actual deleted-vertex graph

The old graph is the induced graph on a subtype. Its prescribed roles and
sampled frames are transported to the ambient carrier without requiring a
degree condition on the newly isolated vertex.
-/

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V]

def replacementSupportBound (B : Finset (FiniteGraph 3)) (b t : ℕ) : ℕ :=
  (t + (3 * b + 4)) * (t + 5 * b + 1) *
    ((t + (3 * b + 4)) * Ordinary.roleWitnessEdges B - 1)

theorem canonical_of_induced_frames
    (F : Finset (FiniteGraph 3)) (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    (G : RGraph V (t + (3 * CodePools.blockCount q + 4))) (v : V)
    (z : ↥(Finset.univ.erase v : Finset V))
    (σ : ↥(Finset.univ.erase v : Finset V) → Option (Roots (CodePools.blockCount q) t))
    (hσ : Admissible (homomorphicClosure F) (CodePools.pool p q hpq)
      (G.induced (Finset.univ.erase v)) σ)
    (hfree : familyFree (Ordinary.forbidden F (CodePools.pool p q hpq) t) G)
    (hinc : ∀ w : ↥(Finset.univ.erase v : Finset V),
      ∃ e ∈ (G.induced (Finset.univ.erase v)).edges, w ∈ e)
    (hframe : ∀ S : Finset ↥(Finset.univ.erase v : Finset V),
      S.card ≤ replacementSupportBound (homomorphicClosure F) (CodePools.blockCount q) t →
      HasReplacementFrame p q hpq (G.induced (Finset.univ.erase v)) σ S) :
    Canonical (homomorphicClosure F) (CodePools.pool p q hpq) G := by
  classical
  let D : Finset V := Finset.univ.erase v
  let G₀ := G.within D
  let ret := RGraph.subsetRetraction D z
  let ρ := σ ∘ ret
  have hproj : G₀.IsHom (G.induced D) ret := G.within_projection D z
  have hρ : Admissible (homomorphicClosure F) (CodePools.pool p q hpq) G₀ ρ :=
    hσ.comap F _ (fun _ _ h => CodePools.pools_disjoint p q hpq h) hproj
  have hι : (G.induced D).IsHom G₀ Subtype.val := (G.induced_within_embedding D).2
  apply canonical_of_replacement_frames F p q hpq hq G G₀ v ρ
    (G.within_erase_edges v) hρ hfree
  · intro w hw
    have hwD : w ∈ D := Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩
    obtain ⟨e, he, hwe⟩ := hinc ⟨w, hwD⟩
    exact ⟨e.image Subtype.val, hι e he, Finset.mem_image.mpr ⟨⟨w, hwD⟩, hwe, rfl⟩⟩
  · intro S hvS hS
    let S' : Finset D := Finset.univ.filter (fun w => w.val ∈ S)
    have himage : S'.image Subtype.val = S := by
      ext w
      constructor
      · intro hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hu).2
      · intro hw
        have hwD : w ∈ D := Finset.mem_erase.mpr
          ⟨fun h => hvS (h ▸ hw), Finset.mem_univ _⟩
        exact Finset.mem_image.mpr ⟨⟨w, hwD⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩
    have hS' : S'.card ≤ replacementSupportBound (homomorphicClosure F)
        (CodePools.blockCount q) t := by
      have hc := Finset.card_image_of_injective S' (Subtype.val_injective (p := (· ∈ D)))
      rw [himage] at hc
      simpa only [hc, replacementSupportBound] using hS
    have hroles : ∀ w ∈ S', ρ w.val = σ w := by
      intro w _
      change σ (ret w.val) = σ w
      congr 1
      apply Subtype.ext
      exact RGraph.subsetRetraction_val D z w.val w.property
    have h := (hframe S' hS').map p q hpq hι hroles
    simpa only [himage] using h

end TuranUniversality.Structural.Roles
