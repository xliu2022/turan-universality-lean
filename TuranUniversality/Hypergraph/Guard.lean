module

public import TuranUniversality.Hypergraph.Clique
public import TuranUniversality.Hypergraph.Relabel
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! # The actual disjoint-clique guard and its small hitting set -/

namespace TuranUniversality.RGraph

variable {V : Type*} [DecidableEq V]

def cliquePacking (s t : ℕ) : RGraph (Fin s × Fin t) 3 where
  edges := Finset.univ.biUnion fun i : Fin s =>
    (clique (Fin t) 3).edges.image fun e => e.image (Prod.mk i)
  uniform := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
    exact (mem_clique d).mp hd

theorem cliquePacking_edge {s t : ℕ} (i : Fin s) (e : Finset (Fin t)) (he : e.card = 3) :
    e.image (Prod.mk i) ∈ (cliquePacking s t).edges :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨e, (mem_clique e).mpr he, rfl⟩⟩

theorem cliquePacking_triple {s t : ℕ} (i : Fin s) (a b c : Fin t)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    {(i, a), (i, b), (i, c)} ∈ (cliquePacking s t).edges := by
  simpa using cliquePacking_edge i ({a, b, c} : Finset (Fin t)) (by simp [hab, hac, hbc])

theorem cliquePacking_embedding_of_sets (G : RGraph V 3) {s t : ℕ}
    (S : Fin s → Finset V) (hS : ∀ i, G.IsCliqueSet t (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ f, (cliquePacking s t).IsEmbedding G f := by
  classical
  let e (i : Fin s) : Fin t ≃ S i := Fintype.equivOfCardEq (by simp [(hS i).1])
  let f : Fin s × Fin t → V := fun p => (e p.1 p.2).val
  have hf : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ heq
    have hij : i = j := by
      by_contra hne
      have heq' : (e i a).val = (e j b).val := heq
      exact Finset.disjoint_left.mp (hdis hne) (e i a).property (heq'.symm ▸ (e j b).property)
    subst j
    have hab : a = b := (e i).injective (Subtype.ext heq)
    subst b
    rfl
  refine ⟨f, hf, ?_⟩
  intro d hd
  obtain ⟨i, _, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  rw [Finset.image_image]
  apply (hS i).2
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (e i j).property
  · have hinj : Function.Injective (f ∘ Prod.mk i) :=
      fun a b h => (e i).injective (Subtype.ext h)
    rw [Finset.card_image_of_injective _ hinj]
    exact (mem_clique a).mp ha

def IsCliquePacking (G : RGraph V 3) (t : ℕ) (F : Finset (Finset V)) : Prop :=
  (∀ S ∈ F, G.IsCliqueSet t S) ∧ Set.PairwiseDisjoint (F : Set (Finset V)) id

theorem packing_card_lt_of_free (G : RGraph V 3) {s t : ℕ}
    (hfree : ¬ ∃ f, (cliquePacking s t).IsEmbedding G f)
    (F : Finset (Finset V)) (hF : G.IsCliquePacking t F) : F.card < s := by
  classical
  by_contra h
  have hs : Fintype.card (Fin s) ≤ Fintype.card F := by simpa using Nat.le_of_not_gt h
  let a : Fin s ↪ F := Classical.choice (Function.Embedding.nonempty_of_card_le hs)
  apply hfree
  apply cliquePacking_embedding_of_sets G (fun i => (a i).val)
  · intro i
    exact hF.1 _ (a i).property
  · intro i j hij
    exact hF.2 (a i).property (a j).property
      (fun he => hij (a.injective (Subtype.ext he)))

/-- A maximal family of disjoint cliques has at most `s-1` members, and its
union meets every clique. This is an actual finite extremal construction. -/
theorem guard_hitting_set [Fintype V] (G : RGraph V 3) {s t : ℕ} (ht : 0 < t)
    (hfree : ¬ ∃ f, (cliquePacking s t).IsEmbedding G f) :
    ∃ S : Finset V, S.card ≤ t * (s - 1) ∧
      ∀ A, G.IsCliqueSet t A → ¬ Disjoint A S := by
  classical
  let U := Finset.univ.filter fun F : Finset (Finset V) => G.IsCliquePacking t F
  have hU : U.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    constructor
    · simp
    · intro a ha; simpa using ha
  obtain ⟨F, hF, hmax⟩ := U.exists_max_image Finset.card hU
  have hpack := (Finset.mem_filter.mp hF).2
  let S := F.biUnion id
  have hsize : S.card ≤ t * (s - 1) := by
    have hc := G.packing_card_lt_of_free hfree F hpack
    calc
      S.card = ∑ A ∈ F, A.card := Finset.card_biUnion hpack.2
      _ = ∑ _A ∈ F, t := Finset.sum_congr rfl (fun A hA => (hpack.1 A hA).1)
      _ = F.card * t := by simp
      _ ≤ t * (s - 1) := by nlinarith [Nat.le_sub_one_of_lt hc]
  refine ⟨S, hsize, ?_⟩
  intro A hA hAS
  have hAnot : A ∉ F := by
    intro hAF
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (hA.1.symm ▸ ht)
    exact Finset.disjoint_left.mp hAS hv (Finset.mem_biUnion.mpr ⟨A, hAF, hv⟩)
  have hnew : G.IsCliquePacking t (insert A F) := by
    constructor
    · intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hA
      · exact hpack.1 D hD
    · intro D hD E hE hDE
      have hD' : D = A ∨ D ∈ F := Finset.mem_insert.mp hD
      have hE' : E = A ∨ E ∈ F := Finset.mem_insert.mp hE
      rcases hD' with hDA | hDF
      · subst D
        rcases hE' with hEA | hEF
        · exact False.elim (hDE hEA.symm)
        · apply Finset.disjoint_left.mpr
          intro v hv hw
          exact Finset.disjoint_left.mp hAS hv (Finset.mem_biUnion.mpr ⟨E, hEF, hw⟩)
      · rcases hE' with hEA | hEF
        · subst E
          apply Finset.disjoint_left.mpr
          intro v hv hw
          exact Finset.disjoint_left.mp hAS hw (Finset.mem_biUnion.mpr ⟨D, hDF, hv⟩)
        · exact hpack.2 hDF hEF hDE
  have hbound := hmax (insert A F) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩)
  rw [Finset.card_insert_of_notMem hAnot] at hbound
  omega

end TuranUniversality.RGraph
