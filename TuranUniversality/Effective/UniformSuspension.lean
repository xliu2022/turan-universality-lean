module

public import TuranUniversality.Effective.UniformPrimrec
public import TuranUniversality.Uniformity.Suspension
public import TuranUniversality.Hypergraph.Relabel
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # An explicit jointly primitive-recursive suspension code -/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

def suspendRow (s : ℕ) (w : List ℕ) : List ℕ :=
  List.range s ++ w.map (s + ·)

def suspendCode (s : ℕ) (g : Code) : Code :=
  (s + g.1, g.2.map (suspendRow s))

theorem suspendRow_primrec : Primrec₂ suspendRow :=
  Primrec.list_append.comp (Primrec.list_range.comp Primrec.fst)
    (Primrec.list_map Primrec.snd
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

theorem suspendCode_primrec : Primrec₂ suspendCode :=
  Primrec.pair (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (suspendRow_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

theorem good_of_suspendRow (s n : ℕ) (w : List ℕ)
    (h : Good (s + 3) (s + n) (suspendRow s w)) : Good 3 n w := by
  refine ⟨?_, ?_, ?_⟩
  · have hl := h.1
    simpa only [suspendRow, List.length_append, List.length_range, List.length_map,
      Nat.add_left_cancel_iff] using hl
  · apply (distinct_iff w).mpr
    have hn := (distinct_iff (suspendRow s w)).mp h.2.1
    exact List.Nodup.of_map (s + ·) (List.nodup_append.mp hn).2.1
  · intro a ha
    have hb := h.2.2 (s + a) (show s + a ∈ suspendRow s w from
      List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    omega

theorem suspendEdge_natImage (s n : ℕ) (e : Finset (Fin n)) (w : List ℕ)
    (he : e.image Fin.val = w.toFinset) :
    ((RGraph.suspendEdge s e).image (finSumFinEquiv : Fin s ⊕ Fin n ≃ Fin (s + n))).image
      Fin.val = (suspendRow s w).toFinset := by
  rw [RGraph.suspendEdge, Finset.image_union, Finset.image_union]
  simp only [Finset.map_eq_image, Finset.image_image]
  have hl : (Finset.univ : Finset (Fin s)).image Fin.val = (List.range s).toFinset := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
      List.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      exact v.isLt
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have hr : e.image (fun a => s + a.val) = (w.map (s + ·)).toFinset := by
    rw [list_map_toFinset, ← he, Finset.image_image]
    rfl
  change (Finset.univ.image Fin.val ∪ e.image (fun a => s + a.val)) = _
  rw [hl, hr]
  ext a
  simp [suspendRow]

theorem mem_suspendCode (s : ℕ) (g : Code) (e : Finset (Fin (s + g.1))) :
    e ∈ (decode (s + 3) (suspendCode s g)).edges ↔
      ∃ d ∈ (decode 3 g).edges,
        (RGraph.suspendEdge s d).image
          (finSumFinEquiv : Fin s ⊕ Fin g.1 ≃ Fin (s + g.1)) = e := by
  constructor
  · intro he
    obtain ⟨hecard, w', hw', hwlen, hew⟩ :=
      (mem_decode (s + 3) (suspendCode s g) e).mp he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    have hgood : Good (s + 3) (s + g.1) (suspendRow s w) :=
      ((edge_iff_of_image (s + 3) (suspendCode s g) e _ hwlen hew).mpr he).1
    have hwgood := good_of_suspendRow s g.1 w hgood
    have hwed : Edge 3 g w :=
      ⟨hwgood, w, hw, hwgood.1, (sameSet_iff w w).mpr rfl⟩
    refine ⟨rowSet g.1 w, edge_rowSet 3 g w hwed, ?_⟩
    apply Finset.image_injective Fin.val_injective
    exact (suspendEdge_natImage s g.1 _ w (rowSet_image g.1 w hwgood.2.2)).trans hew.symm
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨_, w, hw, hwlen, hwd⟩ := (mem_decode 3 g d).mp hd
    apply (mem_decode _ _ _).mpr
    refine ⟨?_, suspendRow s w, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (finSumFinEquiv : Fin s ⊕ Fin g.1 ≃
        Fin (s + g.1)).injective, RGraph.suspendEdge_card, (decode 3 g).uniform d hd]
    · simp [suspendRow, hwlen]
    · exact suspendEdge_natImage s g.1 d w hwd

theorem decode_suspendCode (s : ℕ) (g : Code) :
    decode (s + 3) (suspendCode s g) =
      ((decode 3 g).suspension s).pullback
        (finSumFinEquiv.symm : Fin (s + g.1) ≃ Fin s ⊕ Fin g.1).toEmbedding := by
  change decode (s + 3) (s + g.1, g.2.map (suspendRow s)) = _
  apply RGraph.ext
  ext e
  refine (mem_suspendCode s g e).trans ?_
  rw [RGraph.mem_pullback]
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding, RGraph.mem_suspension]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨?_, d, hd, ?_⟩
    · rw [Finset.card_image_of_injective _ finSumFinEquiv.injective,
        RGraph.suspendEdge_card, (decode 3 g).uniform d hd]
    · rw [Finset.image_image]
      have hc : (finSumFinEquiv.symm : Fin (s + g.1) → Fin s ⊕ Fin g.1) ∘
          (finSumFinEquiv : Fin s ⊕ Fin g.1 → Fin (s + g.1)) = id := by
        funext x
        exact (finSumFinEquiv : Fin s ⊕ Fin g.1 ≃ Fin (s + g.1)).symm_apply_apply x
      rw [hc, Finset.image_id]
  · rintro ⟨_, d, hd, he⟩
    refine ⟨d, hd, ?_⟩
    have h := congrArg (fun a => a.image
      (finSumFinEquiv : Fin s ⊕ Fin g.1 ≃ Fin (s + g.1))) he
    rw [Finset.image_image] at h
    have hc : (finSumFinEquiv : Fin s ⊕ Fin g.1 → Fin (s + g.1)) ∘
        (finSumFinEquiv.symm : Fin (s + g.1) → Fin s ⊕ Fin g.1) = id := by
      funext x
      exact (finSumFinEquiv : Fin s ⊕ Fin g.1 ≃ Fin (s + g.1)).apply_symm_apply x
    simpa only [hc, Finset.image_id] using h

end TuranUniversality.Effective.Uniform
