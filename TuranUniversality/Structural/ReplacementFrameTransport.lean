module

public import TuranUniversality.Structural.CommonFrameCondition
public import TuranUniversality.Structural.CanonicalRestriction
public import TuranUniversality.Hypergraph.InducedMaps

@[expose] public section

/-! # Transport of prescribed roles and replacement frames

These maps retain the prescribed role of every old vertex when passing
between an induced subtype and the original carrier with isolated vertices.
-/

namespace TuranUniversality

namespace RGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

theorem induced_within_embedding (G : RGraph V r) (S : Finset V) :
    (G.induced S).IsEmbedding (G.within S) Subtype.val :=
  ⟨Subtype.val_injective, IsHom.within (G.induced_isEmbedding S).2 S (fun x => x.property)⟩

theorem within_erase_edges (G : RGraph V r) (v : V) :
    (G.within (Finset.univ.erase v)).edges = G.edges.filter (fun e => v ∉ e) := by
  ext e
  simp only [mem_within, Finset.mem_filter]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨he, fun hv => (Finset.mem_erase.mp (h hv)).1 rfl⟩
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    intro w hw
    exact Finset.mem_erase.mpr ⟨fun h' => h (h' ▸ hw), Finset.mem_univ _⟩

end RGraph

namespace Structural.Roles

open Rooted

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
  {b t : ℕ}

theorem Admissible.comap (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    {G : RGraph V (t + (3 * b + 4))} {H : RGraph W (t + (3 * b + 4))}
    {f : V → W} (hf : G.IsHom H f) {ρ : W → Option (Roots b t)}
    (hρ : Admissible (homomorphicClosure F) Ω H ρ) :
    Admissible (homomorphicClosure F) Ω G (ρ ∘ f) := by
  obtain ⟨R, _, hR, hh⟩ := extract_records (homomorphicClosure F) Ω hdis H ρ hρ
  apply admissible_of_records (homomorphicClosure F) Ω G _ (R.clone f) (hR.clone f)
  intro e he
  apply (Compiled.mem_graph_clone Ω R f _).mpr
  have hi : (e.image (place (ρ ∘ f))).image (Compiled.mapData f) =
      (e.image f).image (place ρ) := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun v _ => place_comp ρ f v)
  have ht : (e.image (place (ρ ∘ f))).image (Compiled.mapData f) ∈
      (Compiled.graph t Ω R).edges := by
    rw [hi]
    exact hh _ (hf e he)
  refine ⟨?_, ht⟩
  have hc := (Compiled.graph t Ω R).uniform _ ht
  exact le_antisymm (Finset.card_image_le.trans_eq (G.uniform e he))
    (hc ▸ Finset.card_image_le)

theorem HasReplacementFrame.map (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    {G : RGraph V (t + (3 * CodePools.blockCount q + 4))}
    {H : RGraph W (t + (3 * CodePools.blockCount q + 4))}
    {ρ : V → Option (Roots (CodePools.blockCount q) t)}
    {σ : W → Option (Roots (CodePools.blockCount q) t)} {S : Finset V}
    (hframe : HasReplacementFrame p q hpq G ρ S) {g : V → W} (hg : G.IsHom H g)
    (hroles : ∀ y ∈ S, σ (g y) = ρ y) :
    HasReplacementFrame p q hpq H σ (S.image g) := by
  obtain ⟨f, hf, hr⟩ := hframe
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  intro y hy j hj
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hxj : ρ x = some j := (hroles x hx).symm.trans hj
  have hh := hg.comp (hr x hx j hxj)
  have heq : Function.update (g ∘ f) (rootVertex (Fin 5) j) (g x) =
      g ∘ Function.update f (rootVertex (Fin 5) j) x := by
    funext a
    by_cases ha : a = rootVertex (Fin 5) j
    · subst a; simp
    · simp [Function.update_of_ne ha]
  rw [heq]
  exact hh

end Structural.Roles

end TuranUniversality
