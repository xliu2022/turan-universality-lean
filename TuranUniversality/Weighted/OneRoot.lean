module

public import TuranUniversality.Weighted.Incidence
public import TuranUniversality.Weighted.TypedLink

/-! # The declared and ambiguous parts of each actual one-root link -/

@[expose] public section

namespace TuranUniversality.Weighted.CompilerSignature

open scoped BigOperators

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

def declaredDataLink (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (r : Roots) : Finset (Finset Data) :=
  M.dataLink r ∩ (S.codes.declaredVertices M).powersetCard 2

abbrev partition (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.codes.HasCandidates M) :=
  S.codes.physicalPartition M S.physical h

omit [DecidableEq Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem declared_code_exists (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.codes.HasCandidates M)
    (d : Data) (hd : d ∈ S.codes.declaredVertices M) : ∃ c, S.codes.Declared M d c := by
  rcases S.codes.declared_or_ambiguous M d (h d) with hc | ha
  · exact hc
  · exact False.elim ((S.codes.mem_declaredVertices M d).mp hd ha)

omit [DecidableEq Code] [Fintype Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem cell_color_source_target (S : CompilerSignature Roots Code Kinds L)
    (e : Fin 3) (k : Kinds) (hk : k = S.cellKind ∨ k = S.colorKind) :
    k = S.sourceKind e ∨ k = S.targetKind e := by
  unfold sourceKind targetKind
  split_ifs <;> tauto

/-- At an indexed root the actual declared link is contained in the precise
complete-cross / two-clique / partial-matching permitted pair set. -/
theorem declaredDataLink_subset_indexed (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M) (e : Fin 3) (j : Fin L) :
    S.declaredDataLink M (S.copyRoot (e, j)) ⊆
      (S.partition M h.candidates).matchedLink (S.sourceKind e) (S.targetKind e)
        (S.copyMatching M e j (h.matching e)) := by
  intro p hp
  obtain ⟨hpL, hpD⟩ := Finset.mem_inter.mp hp
  obtain ⟨a, b, hab, hpab⟩ := Finset.card_eq_two.mp (M.dataLink_uniform _ p hpL)
  have hpSub := (Finset.mem_powersetCard.mp hpD).1
  have ha : a ∈ p := by rw [hpab]; simp
  have hb : b ∈ p := by rw [hpab]; simp
  obtain ⟨c, hc⟩ := S.declared_code_exists M h.candidates a (hpSub ha)
  obtain ⟨d, hd⟩ := S.declared_code_exists M h.candidates b (hpSub hb)
  have haB : a ∈ (S.partition M h.candidates).block (S.physical c) :=
    (S.codes.mem_typeVertices M S.physical _ a).mpr ⟨c, hc, rfl⟩
  have hbB : b ∈ (S.partition M h.candidates).block (S.physical d) :=
    (S.codes.mem_typeVertices M S.physical _ b).mpr ⟨d, hd, rfl⟩
  by_cases hcd : S.physical c = S.physical d
  · have hkind := (h.oneRoot _ p hpL a ha b hb hab c d hc hd hcd).2
    have hchoices := S.cell_color_source_target e (S.physical c) hkind
    have hwithin : p ∈ ((S.partition M h.candidates).block (S.physical c)).powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, M.dataLink_uniform _ p hpL⟩
      rw [hpab]
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro haB (hcd ▸ hbB)
    unfold TypePartition.matchedLink
    rcases hchoices with hs | ht
    · rw [hs] at hwithin
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hwithin))
    · rw [ht] at hwithin
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hwithin)
  · have hcross : p ∈ (S.partition M h.candidates).crossPairs := by
      apply (S.partition M h.candidates).completePairs_subset_cross (S.physical c) (S.physical d) hcd
      apply Finset.mem_image.mpr
      exact ⟨(a, b), Finset.mem_product.mpr ⟨haB, hbB⟩, hpab.symm⟩
    by_cases hpST : p ∈ completePairs (S.typeClass M (S.sourceKind e)) (S.typeClass M (S.targetKind e))
    · obtain ⟨⟨u, v⟩, huv, hpUV⟩ := Finset.mem_image.mp hpST
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      have hedges : ({S.copyRoot (e, j)}, {u, v}) ∈ M.edges := by
        have hedge := (M.mem_dataLink _ p).mp hpL
        simpa only [← hpUV] using hedge
      have hpair : (u, v) ∈ (S.copyMatching M e j (h.matching e)).pairs :=
        (S.mem_relationCopy M e j (u, v)).mpr ⟨hu, hv, hedges⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v), hpair, hpUV⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hcross, hpST⟩)))

/-- An additional root permits only the complete cross-type declared link. -/
theorem declaredDataLink_subset_additional (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M) (r : Roots)
    (hr : ¬ ∃ e j, S.copyRoot (e, j) = r) :
    S.declaredDataLink M r ⊆ (S.partition M h.candidates).crossPairs := by
  intro p hp
  obtain ⟨hpL, hpD⟩ := Finset.mem_inter.mp hp
  obtain ⟨a, b, hab, hpab⟩ := Finset.card_eq_two.mp (M.dataLink_uniform r p hpL)
  have hpSub := (Finset.mem_powersetCard.mp hpD).1
  have ha : a ∈ p := by rw [hpab]; simp
  have hb : b ∈ p := by rw [hpab]; simp
  obtain ⟨c, hc⟩ := S.declared_code_exists M h.candidates a (hpSub ha)
  obtain ⟨d, hd⟩ := S.declared_code_exists M h.candidates b (hpSub hb)
  have hcd : S.physical c ≠ S.physical d := by
    intro hcd
    exact hr (h.oneRoot r p hpL a ha b hb hab c d hc hd hcd).1
  apply (S.partition M h.candidates).completePairs_subset_cross (S.physical c) (S.physical d) hcd
  apply Finset.mem_image.mpr
  refine ⟨(a, b), Finset.mem_product.mpr ⟨?_, ?_⟩, hpab.symm⟩
  · exact (S.codes.mem_typeVertices M S.physical _ a).mpr ⟨c, hc, rfl⟩
  · exact (S.codes.mem_typeVertices M S.physical _ b).mpr ⟨d, hd, rfl⟩

omit [DecidableEq Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem dataLink_split (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (r : Roots) (x : Data → ℝ) :
    (∑ p ∈ M.dataLink r, ∏ d ∈ p, x d) =
      (∑ p ∈ S.declaredDataLink M r, ∏ d ∈ p, x d) +
      ∑ p ∈ S.codes.ambiguousDataLink M r, ∏ d ∈ p, x d := by
  have h := Finset.sum_inter_add_sum_sdiff (M.dataLink r)
    ((S.codes.declaredVertices M).powersetCard 2) (fun p => ∏ d ∈ p, x d)
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem indexed_dataLink_bound (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M) (e : Fin 3) (j : Fin L)
    (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    (∑ p ∈ M.dataLink (S.copyRoot (e, j)), ∏ d ∈ p, x d) ≤
      elementary Finset.univ ((S.partition M h.candidates).mass x) 2 +
        ((S.partition M h.candidates).mass x (S.sourceKind e) -
          (S.partition M h.candidates).mass x (S.targetKind e)) ^ 2 / 2 -
        (S.copyMatching M e j (h.matching e)).defect x x / 2 +
        (∑ d, x d) * S.codes.ambiguousWeight M x - (S.codes.ambiguousWeight M x) ^ 2 / 2 := by
  rw [S.dataLink_split]
  have hd : (∑ p ∈ S.declaredDataLink M (S.copyRoot (e, j)), ∏ d ∈ p, x d) ≤
      ∑ p ∈ (S.partition M h.candidates).matchedLink (S.sourceKind e) (S.targetKind e)
        (S.copyMatching M e j (h.matching e)), ∏ d ∈ p, x d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (S.declaredDataLink_subset_indexed M h e j)
    exact fun p hp hnot => Finset.prod_nonneg fun d hd => hx d
  have hb := (S.partition M h.candidates).matchedLink_bound
    (S.sourceKind e) (S.targetKind e) (S.source_ne_target e)
    (S.copyMatching M e j (h.matching e)) x hx
  have ha := S.codes.ambiguousDataLink_bound M x (S.copyRoot (e, j)) hx
  have hh := add_le_add (hd.trans hb) ha
  simpa only [sub_eq_add_neg, add_assoc] using hh

theorem additional_dataLink_bound (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M) (r : Roots)
    (hr : ¬ ∃ e j, S.copyRoot (e, j) = r) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) :
    (∑ p ∈ M.dataLink r, ∏ d ∈ p, x d) ≤
      elementary Finset.univ ((S.partition M h.candidates).mass x) 2 +
        (∑ d, x d) * S.codes.ambiguousWeight M x - (S.codes.ambiguousWeight M x) ^ 2 / 2 := by
  rw [S.dataLink_split]
  have hd : (∑ p ∈ S.declaredDataLink M r, ∏ d ∈ p, x d) ≤
      (S.partition M h.candidates).crossWeight x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (S.declaredDataLink_subset_additional M h r hr)
    exact fun p hp hnot => Finset.prod_nonneg fun d hd => hx d
  rw [(S.partition M h.candidates).crossWeight_eq] at hd
  have ha := S.codes.ambiguousDataLink_bound M x r hx
  linarith

end TuranUniversality.Weighted.CompilerSignature
