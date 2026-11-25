module

public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-! # Complete uniform hypergraphs and clique sets -/

namespace TuranUniversality.RGraph

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]

def clique (V : Type u) [DecidableEq V] [Fintype V] (r : ℕ) : RGraph V r where
  edges := Finset.univ.powersetCard r
  uniform e he := (Finset.mem_powersetCard.mp he).2

@[simp] theorem mem_clique [Fintype V] {r : ℕ} (e : Finset V) :
    e ∈ (clique V r).edges ↔ e.card = r := by simp [clique]

theorem clique_coversPairs [Fintype V] {r : ℕ} (hr : 2 ≤ r) (hV : r ≤ Fintype.card V) :
    (clique V r).CoversPairs := by
  intro a b hab
  have hcard : ({a, b} : Finset V).card ≤ r := by simp [hab]; omega
  obtain ⟨e, heab, _, he⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ ({a, b} : Finset V)) hcard (by simpa using hV)
  exact ⟨e, (mem_clique e).mpr he, heab (by simp), heab (by simp)⟩

def IsCliqueSet (G : RGraph V 3) (t : ℕ) (S : Finset V) : Prop :=
  S.card = t ∧ S.powersetCard 3 ⊆ G.edges

instance (G : RGraph V 3) (t : ℕ) (S : Finset V) : Decidable (G.IsCliqueSet t S) :=
  inferInstanceAs (Decidable (S.card = t ∧ S.powersetCard 3 ⊆ G.edges))

theorem IsCliqueSet.of_embedding {t : ℕ} (G : RGraph V 3) {f : Fin t → V}
    (hf : (clique (Fin t) 3).IsEmbedding G f) :
    G.IsCliqueSet t (Finset.univ.image f) := by
  refine ⟨by rw [Finset.card_image_of_injective _ hf.1]; simp, ?_⟩
  intro e he
  obtain ⟨heS, hecard⟩ := Finset.mem_powersetCard.mp he
  let d := Finset.univ.filter fun j => f j ∈ e
  have himage : d.image f = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hj).2
    · intro hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (heS hv)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  have hd : d ∈ (clique (Fin t) 3).edges := by
    apply (mem_clique d).mpr
    rw [← Finset.card_image_of_injective d hf.1, himage]
    exact hecard
  simpa only [himage] using hf.2 d hd

theorem IsCliqueSet.exists_embedding {t : ℕ} (G : RGraph V 3) {S : Finset V}
    (hS : G.IsCliqueSet t S) : ∃ f : Fin t → V, (clique (Fin t) 3).IsEmbedding G f := by
  classical
  let e : Fin t ≃ S := Fintype.equivOfCardEq (by simp [hS.1])
  refine ⟨fun j => (e j).val, ?_⟩
  refine ⟨fun a b h => e.injective (Subtype.ext h), ?_⟩
  intro d hd
  apply hS.2
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (e j).property
  · rw [Finset.card_image_of_injective _ (fun a b h => e.injective (Subtype.ext h))]
    exact (mem_clique d).mp hd

theorem clique_free_iff_no_cliqueSet [Fintype V] {t : ℕ} (ht : 3 ≤ t) (G : RGraph V 3) :
    (clique (Fin t) 3).HomFree G ↔ ¬ ∃ S, G.IsCliqueSet t S := by
  constructor
  · rintro h ⟨S, hS⟩
    obtain ⟨f, hf⟩ := hS.exists_embedding G
    exact h ⟨f, hf.isHom⟩
  · rintro h ⟨f, hf⟩
    have hcov := clique_coversPairs (V := Fin t) (by omega : 2 ≤ 3) (by simpa using ht)
    exact h ⟨_, IsCliqueSet.of_embedding G ⟨hcov.hom_injective hf, hf⟩⟩

end TuranUniversality.RGraph
