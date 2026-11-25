module

public import TuranUniversality.Hypergraph.Clone
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual induced graphs and the degree lost by deleting vertices -/

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

noncomputable def induced (G : RGraph V r) (S : Finset V) : RGraph S r :=
  G.pullback (Function.Embedding.subtype _)

theorem induced_isEmbedding (G : RGraph V r) (S : Finset V) :
    (G.induced S).IsEmbedding G Subtype.val :=
  ⟨Subtype.val_injective, G.pullback_isHom _⟩

def degreeOn (G : RGraph V r) (S : Finset V) (v : V) : ℕ :=
  (G.edges.filter (fun e => v ∈ e ∧ e ⊆ S)).card

theorem degree_induced (G : RGraph V r) (S : Finset V) (v : S) :
    (G.induced S).degree v = G.degreeOn S v.val := by
  classical
  let f : S ↪ V := Function.Embedding.subtype _
  have heq : ((G.induced S).edges.filter (fun e => v ∈ e)).image (fun e => e.map f) =
      G.edges.filter (fun e => v.val ∈ e ∧ e ⊆ S) := by
    ext e
    constructor
    · intro he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hd, hv⟩ := Finset.mem_filter.mp hd
      have hedge := ((G.mem_pullback f d).mp hd).2
      refine Finset.mem_filter.mpr ⟨hedge, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
      · intro w hw
        obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hw
        exact z.property
    · intro he
      obtain ⟨he, hv, hs⟩ := Finset.mem_filter.mp he
      have him : e ∈ (G.pullback f).edges.image (fun d => d.map f) := by
        rw [G.pullback_edges_image f]
        simp only [Finset.mem_filter]
        exact ⟨he, fun w hw => ⟨⟨w, hs hw⟩, rfl⟩⟩
      obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp him
      refine Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, ?_⟩, hde⟩
      rw [← hde] at hv
      exact (Finset.mem_map' f).mp hv
  have hcard := Finset.card_image_of_injOn
    (s := (G.induced S).edges.filter (fun e => v ∈ e))
    (fun _ _ _ _ h => Finset.map_injective f h)
  rw [heq] at hcard
  exact hcard.symm

theorem degreeOn_eq_link_filter (G : RGraph V r) (S : Finset V) {v : V} (hv : v ∈ S) :
    G.degreeOn S v = ((G.link v).filter (fun e => e ⊆ S)).card := by
  classical
  have heq : (G.edges.filter (fun e => v ∈ e ∧ e ⊆ S)).image (fun e => e.erase v) =
      (G.link v).filter (fun e => e ⊆ S) := by
    ext s
    constructor
    · intro hs
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨he, hev, hes⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨G.erase_mem_link he hev,
        (Finset.erase_subset _ _).trans hes⟩
    · intro hs
      obtain ⟨hs, hsub⟩ := Finset.mem_filter.mp hs
      obtain ⟨hvs, he⟩ := (G.mem_link v s).mp hs
      refine Finset.mem_image.mpr ⟨insert v s, Finset.mem_filter.mpr
        ⟨he, Finset.mem_insert_self _ _, Finset.insert_subset hv hsub⟩,
        Finset.erase_insert hvs⟩
  have hi : Set.InjOn (fun e : Finset V => e.erase v)
      (G.edges.filter (fun e => v ∈ e ∧ e ⊆ S)) := by
    intro e he d hd hed
    exact G.erase_injective_on_star v
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2.1⟩)
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2.1⟩) hed
  have hc := Finset.card_image_of_injOn hi
  rw [heq] at hc
  exact hc.symm

theorem edge_card_le_pow (G : RGraph V r) : G.edges.card ≤ Fintype.card V ^ r := by
  have hs : G.edges ⊆ (Finset.univ : Finset V).powersetCard r := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, G.uniform _ he⟩
  have h := Finset.card_le_card hs
  rw [Finset.card_powersetCard, Finset.card_univ] at h
  exact h.trans (Nat.choose_le_pow _ _)

theorem degree_le_pow (G : RGraph V r) (v : V) :
    G.degree v ≤ Fintype.card V ^ (r - 1) := by
  rw [← G.card_link]
  exact (G.linkGraph v).edge_card_le_pow

theorem edges_lost_le (G : RGraph V r) (S : Finset V) :
    (G.edges.filter (fun e => ¬ e ⊆ S)).card ≤
      (Finset.univ \ S).card * Fintype.card V ^ (r - 1) := by
  classical
  have hs : G.edges.filter (fun e => ¬ e ⊆ S) ⊆
      (Finset.univ \ S).biUnion (fun v => G.edges.filter (fun e => v ∈ e)) := by
    intro e he
    obtain ⟨he, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hv, hn⟩ := Finset.not_subset.mp hs
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩,
      Finset.mem_filter.mpr ⟨he, hv⟩⟩
  exact (Finset.card_le_card hs).trans
    (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => G.degree_le_pow v))

theorem degreeOn_loss (G : RGraph V r) (S : Finset V) {v : V} (hv : v ∈ S) :
    G.degree v ≤ G.degreeOn S v +
      (Finset.univ \ S).card * Fintype.card V ^ (r - 2) := by
  have hbad := (G.linkGraph v).edges_lost_le S
  have hp := Finset.card_filter_add_card_filter_not (s := G.link v) (fun e => e ⊆ S)
  have hr : r - 1 - 1 = r - 2 := by omega
  change ((G.link v).filter (fun e => ¬ e ⊆ S)).card ≤ _ at hbad
  rw [hr] at hbad
  rw [← G.card_link, G.degreeOn_eq_link_filter S hv]
  omega

theorem degree_induced_loss (G : RGraph V r) (S : Finset V) (v : S) :
    G.degree v.val ≤ (G.induced S).degree v +
      (Finset.univ \ S).card * Fintype.card V ^ (r - 2) := by
  rw [G.degree_induced]
  exact G.degreeOn_loss S v.property

end TuranUniversality.RGraph
