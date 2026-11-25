module

public import TuranUniversality.Structural.OrdinaryFamily

@[expose] public section

/-! # Small induced free graphs and zero-edge extension to the original carrier -/

namespace TuranUniversality

namespace RGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

def within (G : RGraph V r) (S : Finset V) : RGraph V r where
  edges := G.edges.filter (fun e => e ⊆ S)
  uniform e he := G.uniform e (Finset.mem_filter.mp he).1

@[simp] theorem mem_within (G : RGraph V r) (S e : Finset V) :
    e ∈ (G.within S).edges ↔ e ∈ G.edges ∧ e ⊆ S := Finset.mem_filter

theorem within_isHom (G : RGraph V r) (S : Finset V) : (G.within S).IsHom G id := by
  intro e he
  simpa using ((G.mem_within S e).mp he).1

theorem IsHom.within {U : Type*} [DecidableEq U]
    {F : RGraph U r} {G : RGraph V r} {f : U → V}
    (hf : F.IsHom G f) (S : Finset V) (hS : ∀ u, f u ∈ S) : F.IsHom (G.within S) f := by
  intro e he
  apply (G.mem_within S _).mpr
  refine ⟨hf e he, ?_⟩
  intro v hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact hS u

def subsetRetraction (S : Finset V) (z : S) (v : V) : S :=
  if h : v ∈ S then ⟨v, h⟩ else z

theorem subsetRetraction_val (S : Finset V) (z : S) (v : V) (hv : v ∈ S) :
    (subsetRetraction S z v).val = v := by simp [subsetRetraction, hv]

theorem within_projection (G : RGraph V r) (S : Finset V) (z : S) :
    (G.within S).IsHom (G.pullback (Function.Embedding.subtype (· ∈ S))) (subsetRetraction S z) := by
  classical
  intro e he
  obtain ⟨heG, heS⟩ := (G.mem_within S e).mp he
  have hm : (e.image (subsetRetraction S z)).map (Function.Embedding.subtype (· ∈ S)) = e := by
    rw [Finset.map_eq_image, Finset.image_image]
    calc
      _ = e.image id := Finset.image_congr (fun v hv => subsetRetraction_val S z v (heS hv))
      _ = e := Finset.image_id
  apply (G.mem_pullback _ _).mpr
  refine ⟨?_, by simpa only [hm] using heG⟩
  have hc := congrArg Finset.card hm
  simpa only [Finset.card_map, G.uniform e heG] using hc

end RGraph

namespace Structural.Ordinary

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem small_free_canonical (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (G : RGraph V (t + (3 * b + 4)))
    (hcard : Fintype.card V ≤ orderCutoff F Ω t) (hfree : familyFree (forbidden F Ω t) G) :
    Canonical (homomorphicClosure F) Ω G := by
  classical
  by_contra hbad
  let e := (Fintype.equivFin V).symm
  let K := G.pullback e.toEmbedding
  have hKbad : ¬ Canonical (homomorphicClosure F) Ω K :=
    fun h => hbad (Canonical.of_hom F Ω (G.pullback_equiv_inverse e).2 h)
  have hmem : (⟨Fintype.card V, K⟩ : FiniteGraph (t + (3 * b + 4))) ∈ forbidden F Ω t :=
    (mem_forbidden F Ω t _).mpr ⟨hcard, hKbad⟩
  exact hfree _ hmem ⟨e, G.pullback_equiv_embedding e⟩

theorem small_within_canonical (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (G : RGraph V (t + (3 * b + 4)))
    (hfree : familyFree (forbidden F Ω t) G) (S : Finset V) (hS : S.Nonempty)
    (hcard : S.card ≤ orderCutoff F Ω t) : Canonical (homomorphicClosure F) Ω (G.within S) := by
  classical
  obtain ⟨z, hz⟩ := hS
  let f : S ↪ V := Function.Embedding.subtype _
  have hcan := small_free_canonical F Ω (G.pullback f) (by simpa using hcard)
    (familyFree_pullback _ G f hfree)
  exact Canonical.of_hom F Ω (G.within_projection S ⟨z, hz⟩) hcan

end Structural.Ordinary

end TuranUniversality
