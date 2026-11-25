module

public import TuranUniversality.Effective.GraphRelations
public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-! # A semantic bridge for explicit bounded triple-list graph algorithms -/

namespace TuranUniversality.Effective

set_option backward.isDefEq.respectTransparency false

def predicateGraphCode (n : ℕ) (P : Triple → Prop) [DecidablePred P] : GraphCode :=
  (n, (allTriples n).filter P)

theorem decode_predicateGraphCode (n : ℕ) (P : Triple → Prop) [DecidablePred P]
    (G : RGraph (Fin n) 3)
    (hP : ∀ a b c : Fin n, P (a.val, b.val, c.val) ↔ {a, b, c} ∈ G.edges) :
    decodeGraph (predicateGraphCode n P) = G := by
  unfold predicateGraphCode
  apply RGraph.ext
  ext e
  rw [mem_decodeGraph]
  constructor
  · rintro ⟨_, t, ht, he⟩
    change t ∈ (allTriples n).filter P at ht
    obtain ⟨ht, hp⟩ := List.mem_filter.mp ht
    have ht' := (mem_allTriples n t).mp ht
    let a : Fin n := ⟨t.1, ht'.1⟩
    let b : Fin n := ⟨t.2.1, ht'.2.1⟩
    let c : Fin n := ⟨t.2.2, ht'.2.2⟩
    have heq : e = {a, b, c} := by
      apply Finset.image_injective Fin.val_injective
      simpa [tripleSet, a, b, c] using he
    rw [heq]
    exact (hP a b c).mp (of_decide_eq_true hp)
  · intro he
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (G.uniform e he)
    refine ⟨by simp [hab, hac, hbc], (a.val, b.val, c.val), ?_, ?_⟩
    · change (a.val, b.val, c.val) ∈ (allTriples n).filter P
      exact List.mem_filter.mpr ⟨(mem_allTriples n _).mpr ⟨a.isLt, b.isLt, c.isLt⟩,
        decide_eq_true ((hP a b c).mpr he)⟩
    · simp [tripleSet]

end TuranUniversality.Effective

namespace TuranUniversality.RGraph

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]

theorem isHom_of_triples (G : RGraph V 3) (H : RGraph W 3) (f : V → W)
    (hf : ∀ a b c, {a, b, c} ∈ G.edges → {f a, f b, f c} ∈ H.edges) :
    G.IsHom H f := by
  intro e he
  obtain ⟨a, b, c, _hab, _hac, _hbc, rfl⟩ := Finset.card_eq_three.mp (G.uniform e he)
  simpa using hf a b c he

end TuranUniversality.RGraph
