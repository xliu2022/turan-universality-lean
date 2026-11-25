module

public import TuranUniversality.Effective.UniformPrimrec

@[expose] public section

/-! # The exact edge count of a raw uniform-hypergraph code

Only well-formed rows contribute. Rows denoting the same unordered edge are
counted once, even when their order differs. The counting algorithm is primitive
recursive and agrees with the existing decoder on every raw code.
-/

namespace TuranUniversality.Effective.FiniteApproximation

open TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

/-- Count the distinct finite sets represented by a list of natural-number rows. -/
def rowCount : List (List ℕ) → ℕ
  | [] => 0
  | w :: ws => if ∃ t ∈ ws, SameSet w t then rowCount ws else rowCount ws + 1

theorem rowCount_card (ws : List (List ℕ)) :
    rowCount ws = ((ws.map List.toFinset).toFinset).card := by
  induction ws with
  | nil => simp [rowCount]
  | cons w ws ih =>
      have hm : w.toFinset ∈ (ws.map List.toFinset).toFinset ↔
          ∃ t ∈ ws, SameSet w t := by
        simp only [List.mem_toFinset, List.mem_map, sameSet_iff]
        constructor
        · rintro ⟨t, ht, he⟩
          exact ⟨t, ht, he.symm⟩
        · rintro ⟨t, ht, he⟩
          exact ⟨t, ht, he.symm⟩
      by_cases h : ∃ t ∈ ws, SameSet w t
      · simp [rowCount, h, ih, Finset.insert_eq_of_mem (hm.mpr h)]
      · simp [rowCount, h, ih, mt hm.mp h]

theorem rowCount_primrec : Primrec rowCount := by
  have hc : PrimrecPred (fun p : List (List ℕ) ×
      (List ℕ × List (List ℕ) × ℕ) => ∃ t ∈ p.2.2.1, SameSet p.2.1 t) :=
    (sameSet_primrec.swap.exists_mem_list).comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)
  have hs : Primrec (fun p : List (List ℕ) ×
      (List ℕ × List (List ℕ) × ℕ) =>
      if ∃ t ∈ p.2.2.1, SameSet p.2.1 t then p.2.2.2 else p.2.2.2 + 1) :=
    Primrec.ite hc (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.list_rec Primrec.id (Primrec.const (0 : ℕ)) hs.to₂).of_eq
    (fun ws => by induction ws <;> simp_all [rowCount])

/-- The finite algorithm removes invalid rows, then counts unordered edges. -/
def edgeCount (r : ℕ) (g : Code) : ℕ :=
  rowCount (g.2.filter fun w => Good r g.1 w)

theorem decoded_natural_edges (r : ℕ) (g : Code) :
    (decode r g).edges.image (fun e => e.image Fin.val) =
      ((g.2.filter fun w => Good r g.1 w).map List.toFinset).toFinset := by
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, w, hw, hlen, him⟩ := (mem_decode r g d).mp hd
    have hg : Good r g.1 w := ((edge_iff_of_image r g d w hlen him).mpr hd).1
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true hg⟩, him.symm⟩)
  · intro he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    obtain ⟨hmem, hgood⟩ := List.mem_filter.mp hw
    have hg : Good r g.1 w := of_decide_eq_true hgood
    have hed : Edge r g w := ⟨hg, w, hmem, hg.1, (sameSet_iff w w).mpr rfl⟩
    exact Finset.mem_image.mpr
      ⟨rowSet g.1 w, edge_rowSet r g w hed, rowSet_image g.1 w hg.2.2⟩

theorem edgeCount_eq_card (r : ℕ) (g : Code) :
    edgeCount r g = (decode r g).edges.card := by
  rw [edgeCount, rowCount_card, ← decoded_natural_edges]
  exact Finset.card_image_of_injective _ (Finset.image_injective Fin.val_injective)

theorem edgeCount_primrec : Primrec₂ edgeCount := by
  have hgood : PrimrecRel (fun p : ℕ × Code => Good p.1 p.2.1) :=
    good_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  exact rowCount_primrec.comp ((filter_primrec hgood).comp Primrec.id
    (Primrec.snd.comp Primrec.snd))

/-- The input list is kept intact. This test detects a decoded forbidden graph
with no edges, whose presence is handled separately by the approximation API. -/
def HasEdgeless (r : ℕ) (gs : List Code) : Prop :=
  ∃ g ∈ gs, edgeCount r g = 0

instance (r : ℕ) (gs : List Code) : Decidable (HasEdgeless r gs) := by
  unfold HasEdgeless
  infer_instance

theorem hasEdgeless_primrec : PrimrecRel HasEdgeless :=
  exists_mem_primrec Primrec.snd
    (Primrec.eq.comp
      (edgeCount_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.const 0))

end TuranUniversality.Effective.FiniteApproximation
