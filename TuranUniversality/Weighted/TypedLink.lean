module

public import TuranUniversality.Weighted.Types
public import TuranUniversality.Weighted.Matching

/-! # Actual pair sets in a typed one-root link -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

universe u v
variable {V : Type u} [DecidableEq V]

def unorderedPairs (R : Finset (V × V)) : Finset (Finset V) :=
  R.image fun p => {p.1, p.2}

def completePairs (U W : Finset V) : Finset (Finset V) := unorderedPairs (U ×ˢ W)

omit [DecidableEq V] in
theorem pair_endpoints_ne {U W : Finset V} (h : Disjoint U W) {a b : V}
    (ha : a ∈ U) (hb : b ∈ W) : a ≠ b := by
  intro hab
  subst b
  exact Finset.disjoint_left.mp h ha hb

theorem unordered_pair_injective {U W : Finset V} (h : Disjoint U W)
    {R : Finset (V × V)} (hR : R ⊆ U ×ˢ W) :
    Set.InjOn (fun p : V × V => ({p.1, p.2} : Finset V)) (R : Set (V × V)) := by
  intro p hp q hq heq
  change ({p.1, p.2} : Finset V) = {q.1, q.2} at heq
  have hpU := (Finset.mem_product.mp (hR hp)).1
  have hpW := (Finset.mem_product.mp (hR hp)).2
  have hqU := (Finset.mem_product.mp (hR hq)).1
  have hqW := (Finset.mem_product.mp (hR hq)).2
  have hfst : p.1 = q.1 := by
    have hmem : p.1 ∈ ({q.1, q.2} : Finset V) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with he | he
    · exact he
    · exact False.elim ((pair_endpoints_ne h hpU hqW) he)
  have hsnd : p.2 = q.2 := by
    have hmem : p.2 ∈ ({q.1, q.2} : Finset V) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with he | he
    · exact False.elim ((pair_endpoints_ne h hqU hpW) he.symm)
    · exact he
  exact Prod.ext hfst hsnd

theorem unorderedPairs_weight {U W : Finset V} (h : Disjoint U W)
    (R : Finset (V × V)) (hR : R ⊆ U ×ˢ W) (x : V → ℝ) :
    (∑ p ∈ unorderedPairs R, ∏ a ∈ p, x a) = ∑ p ∈ R, x p.1 * x p.2 := by
  rw [unorderedPairs, Finset.sum_image (unordered_pair_injective h hR)]
  apply Finset.sum_congr rfl
  intro p hp
  exact Finset.prod_pair (pair_endpoints_ne h
    (Finset.mem_product.mp (hR hp)).1 (Finset.mem_product.mp (hR hp)).2)

theorem completePairs_weight {U W : Finset V} (h : Disjoint U W) (x : V → ℝ) :
    (∑ p ∈ completePairs U W, ∏ a ∈ p, x a) = (∑ a ∈ U, x a) * (∑ b ∈ W, x b) := by
  rw [completePairs, unorderedPairs_weight h _ (Finset.Subset.refl _)]
  rw [Finset.sum_product, Finset.sum_mul_sum]

theorem nonneg_sum_union_le {α : Type*} [DecidableEq α]
    (I J : Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ I ∪ J, f a) ≤ (∑ a ∈ I, f a) + ∑ a ∈ J, f a := by
  have h := Finset.sum_union_inter (s₁ := I) (s₂ := J) (f := f)
  have hn : 0 ≤ ∑ a ∈ I ∩ J, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

namespace TypePartition

variable {I : Finset V} {Kinds : Type v} [Fintype Kinds]

theorem block_index_unique (P : TypePartition I Kinds) {s t : Kinds} {a : V}
    (hs : a ∈ P.block s) (ht : a ∈ P.block t) : s = t := by
  by_contra hst
  exact Finset.disjoint_left.mp (P.disjoint (Set.mem_univ _) (Set.mem_univ _) hst) hs ht

theorem completePairs_subset_cross (P : TypePartition I Kinds) (s t : Kinds) (hst : s ≠ t) :
    completePairs (P.block s) (P.block t) ⊆ P.crossPairs := by
  intro p hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have hdisj := P.disjoint (Set.mem_univ s) (Set.mem_univ t) hst
  have hne := pair_endpoints_ne hdisj ha hb
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    exact ⟨by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro (P.block_subset s ha) (P.block_subset t hb), Finset.card_pair hne⟩
  · intro hwithin
    obtain ⟨k, hk, hpair⟩ := Finset.mem_biUnion.mp hwithin
    have hsub := (Finset.mem_powersetCard.mp hpair).1
    have hsk := P.block_index_unique ha (hsub (by simp))
    have htk := P.block_index_unique hb (hsub (by simp))
    exact hst (hsk.trans htk.symm)

def matchedLink (P : TypePartition I Kinds) (s t : Kinds)
    (D : PartialMatching (P.block s) (P.block t)) : Finset (Finset V) :=
  ((P.crossPairs \ completePairs (P.block s) (P.block t)) ∪
    (P.block s).powersetCard 2 ∪ (P.block t).powersetCard 2) ∪ unorderedPairs D.pairs

theorem within_block_subset (P : TypePartition I Kinds) (t : Kinds) :
    (P.block t).powersetCard 2 ⊆ P.withinPairs := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hp⟩

theorem cross_disjoint_within (P : TypePartition I Kinds) (t : Kinds) :
    Disjoint P.crossPairs ((P.block t).powersetCard 2) := by
  apply Finset.disjoint_left.mpr
  intro p hp hpt
  exact (Finset.mem_sdiff.mp hp).2 (P.within_block_subset t hpt)

theorem matchingPairs_subset_complete (P : TypePartition I Kinds) (s t : Kinds)
    (D : PartialMatching (P.block s) (P.block t)) :
    unorderedPairs D.pairs ⊆ completePairs (P.block s) (P.block t) := by
  apply Finset.image_mono
  exact fun p hp => Finset.mem_product.mpr ⟨D.left_mem p hp, D.right_mem p hp⟩

theorem matchedLink_uniform (P : TypePartition I Kinds) (s t : Kinds) (hst : s ≠ t)
    (D : PartialMatching (P.block s) (P.block t)) (p : Finset V)
    (hp : p ∈ P.matchedLink s t D) : p.card = 2 := by
  rcases Finset.mem_union.mp hp with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1).2
      · exact (Finset.mem_powersetCard.mp h).2
    · exact (Finset.mem_powersetCard.mp h).2
  · have hc := P.completePairs_subset_cross s t hst (P.matchingPairs_subset_complete s t D h)
    exact (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hc).1).2

theorem pair_mem_matchedLink_iff (P : TypePartition I Kinds) (s t : Kinds) (hst : s ≠ t)
    (D : PartialMatching (P.block s) (P.block t)) (a b : V)
    (ha : a ∈ P.block s) (hb : b ∈ P.block t) :
    {a, b} ∈ P.matchedLink s t D ↔ (a, b) ∈ D.pairs := by
  have hdisj := P.disjoint (Set.mem_univ _) (Set.mem_univ _) hst
  have hcomplete : {a, b} ∈ completePairs (P.block s) (P.block t) :=
    Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_union.mp h with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact False.elim ((Finset.mem_sdiff.mp h).2 hcomplete)
        · have hsub := (Finset.mem_powersetCard.mp h).1
          exact False.elim (Finset.disjoint_left.mp hdisj (hsub (by simp)) hb)
      · have hsub := (Finset.mem_powersetCard.mp h).1
        exact False.elim (Finset.disjoint_left.mp hdisj ha (hsub (by simp)))
    · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
      have hpab : p = (a, b) := unordered_pair_injective hdisj (Finset.Subset.refl _)
        (Finset.mem_product.mpr ⟨D.left_mem p hp, D.right_mem p hp⟩)
        (Finset.mem_product.mpr ⟨ha, hb⟩) heq
      simpa only [hpab] using hp
  · intro hp
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩)

theorem matchedLink_same_type (P : TypePartition I Kinds) (s t : Kinds) (hst : s ≠ t)
    (D : PartialMatching (P.block s) (P.block t)) (k : Kinds) (p : Finset V)
    (hp : p ∈ P.matchedLink s t D) (hwithin : p ∈ (P.block k).powersetCard 2) :
    k = s ∨ k = t := by
  have hcard := (Finset.mem_powersetCard.mp hwithin).2
  have hnonempty : p.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hnonempty
  have hak := (Finset.mem_powersetCard.mp hwithin).1 ha
  rcases Finset.mem_union.mp hp with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact False.elim (Finset.disjoint_left.mp (P.cross_disjoint_within k)
          (Finset.mem_sdiff.mp h).1 hwithin)
      · exact Or.inl (P.block_index_unique hak ((Finset.mem_powersetCard.mp h).1 ha))
    · exact Or.inr (P.block_index_unique hak ((Finset.mem_powersetCard.mp h).1 ha))
  · have hcross := P.completePairs_subset_cross s t hst (P.matchingPairs_subset_complete s t D h)
    exact False.elim (Finset.disjoint_left.mp (P.cross_disjoint_within k) hcross hwithin)

/-- Exact polynomial of the completed link, valid also for signed weights. -/
theorem matchedLink_weight [DecidableEq Kinds] (P : TypePartition I Kinds)
    (s t : Kinds) (hst : s ≠ t) (D : PartialMatching (P.block s) (P.block t)) (x : V → ℝ) :
    (∑ p ∈ P.matchedLink s t D, ∏ a ∈ p, x a) =
      elementary Finset.univ (P.mass x) 2 +
        (P.mass x s - P.mass x t) ^ 2 / 2 - D.defect x x / 2 := by
  let A := P.crossPairs \ completePairs (P.block s) (P.block t)
  let B := (P.block s).powersetCard 2
  let C := (P.block t).powersetCard 2
  let E := unorderedPairs D.pairs
  have hAB : Disjoint A B :=
    (P.cross_disjoint_within s).mono_left Finset.sdiff_subset
  have hAC : Disjoint A C :=
    (P.cross_disjoint_within t).mono_left Finset.sdiff_subset
  have hBC : Disjoint B C := P.pair_classes_disjoint (Set.mem_univ _) (Set.mem_univ _) hst
  have hEsub : E ⊆ P.crossPairs :=
    (P.matchingPairs_subset_complete s t D).trans (P.completePairs_subset_cross s t hst)
  have hAE : Disjoint A E := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpE
    exact (Finset.mem_sdiff.mp hpA).2 (P.matchingPairs_subset_complete s t D hpE)
  have hBE : Disjoint B E := ((P.cross_disjoint_within s).mono_left hEsub).symm
  have hCE : Disjoint C E := ((P.cross_disjoint_within t).mono_left hEsub).symm
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hABCE : Disjoint ((A ∪ B) ∪ C) E :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hAE, hBE⟩, hCE⟩
  change (∑ p ∈ ((A ∪ B) ∪ C) ∪ E, ∏ a ∈ p, x a) = _
  rw [Finset.sum_union hABCE, Finset.sum_union hABC, Finset.sum_union hAB]
  have hdisj := P.disjoint (Set.mem_univ s) (Set.mem_univ t) hst
  have hcross := Finset.sum_sdiff (P.completePairs_subset_cross s t hst)
    (f := fun p => ∏ a ∈ p, x a)
  rw [completePairs_weight hdisj] at hcross
  change (∑ p ∈ A, ∏ a ∈ p, x a) + P.mass x s * P.mass x t = P.crossWeight x at hcross
  have hmatch : (∑ p ∈ E, ∏ a ∈ p, x a) = D.weight x x :=
    unorderedPairs_weight hdisj _ (fun p hp => Finset.mem_product.mpr
      ⟨D.left_mem p hp, D.right_mem p hp⟩) x
  rw [hmatch]
  have hidentity := D.completed_link_identity x x (∑ p ∈ A, ∏ a ∈ p, x a)
  change elementary (P.block s) x 2 + elementary (P.block t) x 2 + D.weight x x +
    (∑ p ∈ A, ∏ a ∈ p, x a) =
      ((∑ p ∈ A, ∏ a ∈ p, x a) + P.mass x s * P.mass x t) +
        (P.mass x s - P.mass x t) ^ 2 / 2 - D.defect x x / 2 at hidentity
  rw [hcross, P.crossWeight_eq] at hidentity
  dsimp [B, C]
  unfold elementary at hidentity ⊢
  linarith

/-- The real permitted pair set has the expected upper polynomial. The
matching defect is computed from its actual present and missing incidences. -/
theorem matchedLink_bound [DecidableEq Kinds] (P : TypePartition I Kinds)
    (s t : Kinds) (hst : s ≠ t) (D : PartialMatching (P.block s) (P.block t))
    (x : V → ℝ) (hx : ∀ a, 0 ≤ x a) :
    (∑ p ∈ P.matchedLink s t D, ∏ a ∈ p, x a) ≤
      elementary Finset.univ (P.mass x) 2 +
        (P.mass x s - P.mass x t) ^ 2 / 2 - D.defect x x / 2 := by
  have hdisj := P.disjoint (Set.mem_univ s) (Set.mem_univ t) hst
  have hcross := Finset.sum_sdiff (P.completePairs_subset_cross s t hst)
    (f := fun p => ∏ a ∈ p, x a)
  rw [completePairs_weight hdisj] at hcross
  change (∑ p ∈ P.crossPairs \ completePairs (P.block s) (P.block t), ∏ a ∈ p, x a) +
    P.mass x s * P.mass x t = P.crossWeight x at hcross
  have hmatch : (∑ p ∈ unorderedPairs D.pairs, ∏ a ∈ p, x a) = D.weight x x :=
    unorderedPairs_weight hdisj _ (fun p hp => Finset.mem_product.mpr
      ⟨D.left_mem p hp, D.right_mem p hp⟩) x
  have hidentity := D.completed_link_identity x x
    (∑ p ∈ P.crossPairs \ completePairs (P.block s) (P.block t), ∏ a ∈ p, x a)
  change elementary (P.block s) x 2 + elementary (P.block t) x 2 + D.weight x x +
    (∑ p ∈ P.crossPairs \ completePairs (P.block s) (P.block t), ∏ a ∈ p, x a) =
    ((∑ p ∈ P.crossPairs \ completePairs (P.block s) (P.block t), ∏ a ∈ p, x a) +
      P.mass x s * P.mass x t) + (P.mass x s - P.mass x t) ^ 2 / 2 -
      D.defect x x / 2 at hidentity
  rw [hcross, P.crossWeight_eq] at hidentity
  have hf : ∀ p : Finset V, 0 ≤ ∏ a ∈ p, x a :=
    fun p => Finset.prod_nonneg fun a _ => hx a
  have h1 := nonneg_sum_union_le
    (P.crossPairs \ completePairs (P.block s) (P.block t)) ((P.block s).powersetCard 2)
    (fun p => ∏ a ∈ p, x a) hf
  have h2 := nonneg_sum_union_le
    ((P.crossPairs \ completePairs (P.block s) (P.block t)) ∪ (P.block s).powersetCard 2)
    ((P.block t).powersetCard 2) (fun p => ∏ a ∈ p, x a) hf
  have h3 := nonneg_sum_union_le
    (((P.crossPairs \ completePairs (P.block s) (P.block t)) ∪
      (P.block s).powersetCard 2) ∪ (P.block t).powersetCard 2)
    (unorderedPairs D.pairs) (fun p => ∏ a ∈ p, x a) hf
  change (∑ p ∈ P.matchedLink s t D, ∏ a ∈ p, x a) ≤ _ at h3
  rw [hmatch] at h3
  unfold elementary at hidentity ⊢
  linarith

end TypePartition

end TuranUniversality.Weighted
