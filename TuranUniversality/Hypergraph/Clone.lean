module

public import TuranUniversality.Hypergraph.Degree
public import TuranUniversality.Density.WeightedHomPushforward

@[expose] public section

/-! # Cloning an actual vertex

Cloning is the complete inverse image under the map which sends one vertex
to another and fixes every other vertex. In particular its projection is an
actual edge-preserving map, so every homomorphism-free class is preserved.
For a nonadjacent pair it replaces precisely one link. We also record the
preservation of all other twin classes, needed by the finite Ψ argument.
-/

namespace TuranUniversality.RGraph

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable [Fintype V] {r : ℕ}

theorem inverseImage_link_eq (G : RGraph W r) (f : V → W) {u v : V}
    (ht : G.link (f u) = G.link (f v)) :
    (G.inverseImage f).link u = (G.inverseImage f).link v := by
  suffices h : ∀ (u v : V), G.link (f u) = G.link (f v) →
      (G.inverseImage f).link u ⊆ (G.inverseImage f).link v from
    Finset.Subset.antisymm (h u v ht) (h v u ht.symm)
  intro u v ht s hs
  obtain ⟨hu, he⟩ := ((G.inverseImage f).mem_link u s).mp hs
  have hi := (G.inverseImage_projection f).injOn_edge he
  have htarget := ((G.mem_inverseImage f _).mp he).2
  have hfu : f u ∉ s.image f := by
    rintro h
    obtain ⟨z, hz, hzu⟩ := Finset.mem_image.mp h
    exact hu (hi (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hz) hzu.symm ▸ hz)
  have hfv : f v ∉ s.image f := by
    intro hv
    by_cases huv : f u = f v
    · exact hfu (huv ▸ hv)
    · exact G.twins_not_cooccur huv ht htarget
        (Finset.mem_image.mpr ⟨u, Finset.mem_insert_self _ _, rfl⟩)
        (Finset.mem_image.mpr (by
          obtain ⟨z, hz, hzf⟩ := Finset.mem_image.mp hv
          exact ⟨z, Finset.mem_insert_of_mem hz, hzf⟩))
  have hv : v ∉ s := fun h => hfv (Finset.mem_image.mpr ⟨v, h, rfl⟩)
  apply ((G.inverseImage f).mem_link v s).mpr
  refine ⟨hv, (G.mem_inverseImage f _).mpr ⟨?_, ?_⟩⟩
  · rw [Finset.card_insert_of_notMem hv, ← Finset.card_insert_of_notMem hu]
    exact (G.inverseImage f).uniform _ he
  · have h := G.replace_twin ht htarget
      (Finset.mem_image.mpr ⟨u, Finset.mem_insert_self _ _, rfl⟩)
    simpa only [Finset.image_insert, Finset.erase_insert hfu] using h

def cloneMap (u v : V) (w : V) : V := if w = u then v else w

@[simp] theorem cloneMap_self (u v : V) : cloneMap u v u = v := by simp [cloneMap]

@[simp] theorem cloneMap_other (u v w : V) (hw : w ≠ u) : cloneMap u v w = w := by
  simp [cloneMap, hw]

def clone (G : RGraph V r) (u v : V) : RGraph V r := G.inverseImage (cloneMap u v)

theorem clone_isHom (G : RGraph V r) (u v : V) :
    (G.clone u v).IsHom G (cloneMap u v) := G.inverseImage_projection _

theorem cloneMap_image_of_notMem (u v : V) (e : Finset V) (hu : u ∉ e) :
    e.image (cloneMap u v) = e := by
  calc
    e.image (cloneMap u v) = e.image id := Finset.image_congr (fun w hw =>
      cloneMap_other u v w (fun h => hu (h ▸ hw)))
    _ = e := Finset.image_id

theorem mem_clone_of_notMem (G : RGraph V r) (u v : V) {e : Finset V} (hu : u ∉ e) :
    e ∈ (G.clone u v).edges ↔ e ∈ G.edges := by
  rw [clone, mem_inverseImage, cloneMap_image_of_notMem _ _ _ hu]
  exact ⟨And.right, fun h => ⟨G.uniform _ h, h⟩⟩

theorem clone_twins (G : RGraph V r) (u v : V) :
    (G.clone u v).link u = (G.clone u v).link v := by
  apply G.inverseImage_link_eq
  by_cases h : v = u
  · subst v
    rfl
  · simp [h]

theorem clone_preserves_twins (G : RGraph V r) (u v : V) {a b : V}
    (ha : a ≠ u) (hb : b ≠ u) (ht : G.link a = G.link b) :
    (G.clone u v).link a = (G.clone u v).link b := by
  apply G.inverseImage_link_eq
  simpa only [cloneMap_other u v a ha, cloneMap_other u v b hb] using ht

theorem clone_link_source (G : RGraph V r) {u v : V} (huv : u ≠ v)
    (hpair : ¬ ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e) :
    (G.clone u v).link u = G.link v := by
  ext s
  constructor
  · intro hs
    obtain ⟨hu, he⟩ := ((G.clone u v).mem_link u s).mp hs
    have hi := (G.clone_isHom u v).injOn_edge he
    have hv : v ∉ s := by
      intro hv
      have h := hi (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hv)
        (by simp [huv.symm])
      exact huv h
    apply (G.mem_link v s).mpr
    refine ⟨hv, ?_⟩
    have h := ((G.mem_inverseImage (cloneMap u v) _).mp he).2
    simpa only [Finset.image_insert, cloneMap_self,
      cloneMap_image_of_notMem u v s hu] using h
  · intro hs
    obtain ⟨hv, he⟩ := (G.mem_link v s).mp hs
    have hu : u ∉ s := fun h => hpair
      ⟨insert v s, he, Finset.mem_insert_of_mem h, Finset.mem_insert_self _ _⟩
    apply ((G.clone u v).mem_link u s).mpr
    refine ⟨hu, (G.mem_inverseImage (cloneMap u v) _).mpr ⟨?_, ?_⟩⟩
    · rw [Finset.card_insert_of_notMem hu, ← Finset.card_insert_of_notMem hv]
      exact G.uniform _ he
    · simpa only [Finset.image_insert, cloneMap_self,
        cloneMap_image_of_notMem u v s hu] using he

theorem clone_degree_source (G : RGraph V r) {u v : V} (huv : u ≠ v)
    (hpair : ¬ ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e) :
    (G.clone u v).degree u = G.degree v := by
  rw [← (G.clone u v).card_link, G.clone_link_source huv hpair, G.card_link]

theorem clone_edges_away (G : RGraph V r) (u v : V) :
    (G.clone u v).edges.filter (fun e => u ∉ e) = G.edges.filter (fun e => u ∉ e) := by
  ext e
  by_cases he : u ∈ e
  · simp [he]
  · simp only [Finset.mem_filter, G.mem_clone_of_notMem u v he]

theorem clone_card_edges (G : RGraph V r) {u v : V} (huv : u ≠ v)
    (hpair : ¬ ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e) :
    (G.clone u v).edges.card + G.degree u = G.edges.card + G.degree v := by
  have hG := Finset.card_filter_add_card_filter_not (s := G.edges) (fun e => u ∈ e)
  have hH := Finset.card_filter_add_card_filter_not (s := (G.clone u v).edges) (fun e => u ∈ e)
  change G.degree u + (G.edges.filter (fun e => u ∉ e)).card = G.edges.card at hG
  change (G.clone u v).degree u +
    ((G.clone u v).edges.filter (fun e => u ∉ e)).card = (G.clone u v).edges.card at hH
  rw [G.clone_edges_away, G.clone_degree_source huv hpair] at hH
  omega

end TuranUniversality.RGraph
