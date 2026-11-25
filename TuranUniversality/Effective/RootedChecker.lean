module

public import TuranUniversality.Effective.RootedEncoding

/-! # Bounded incidence checks and their exact rooted-graph meaning -/

@[expose] public section

namespace TuranUniversality.Effective.RootedCode

open Weighted Selector Computation.MatchingSystem

variable {Roots Code Kinds : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Primcodable Roots]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]

def CandidatesOK (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) : Prop :=
  ∀ x < c.size, ∃ a, Candidate S c x a

def OneRootOK (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) : Prop :=
  ∀ r, ∀ x < c.size, ∀ y < c.size, ∀ a b,
    c.RootEdge r x y → Declared S c x a → Declared S c y b → S.physical a = S.physical b →
      (∃ e j, S.copyRoot (e, j) = r) ∧ (S.physical a = S.cellKind ∨ S.physical a = S.colorKind)

def MatchingOK (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) : Prop :=
  ∀ e, ∀ x < c.size, ∀ y < c.size, ∀ z < c.size,
    (Relation S c e x y → Relation S c e x z → y = z) ∧
    (Relation S c e y x → Relation S c e z x → y = z)

def OneMarkerOK (c : RootedCode Roots) : Prop :=
  ∀ t ∈ allTriples c.size, ∀ s ∈ allTriples c.size,
    c.DataEdge t.1 t.2.1 t.2.2 → c.DataEdge s.1 s.2.1 s.2.2 → SameTriple t s

def MarkerTypesOK (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) : Prop :=
  ∀ x < c.size, ∀ y < c.size, ∀ z < c.size, ∀ a,
    c.DataEdge x y z → Declared S c x a → S.physical a = S.cellKind

def IncidenceOK (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) : Prop :=
  CandidatesOK S c ∧ OneRootOK S c ∧ MatchingOK S c ∧ OneMarkerOK c ∧ MarkerTypesOK S c

set_option synthInstance.maxSize 4096 in
instance (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots) :
    Decidable (IncidenceOK S c) := by
  haveI : Decidable (CandidatesOK S c) := by unfold CandidatesOK; infer_instance
  haveI : Decidable (OneRootOK S c) := by unfold OneRootOK; infer_instance
  haveI : Decidable (MatchingOK S c) := by unfold MatchingOK; infer_instance
  haveI : Decidable (OneMarkerOK c) := by unfold OneMarkerOK; infer_instance
  haveI : Decidable (MarkerTypesOK S c) := by unfold MarkerTypesOK; infer_instance
  unfold IncidenceOK
  infer_instance

theorem candidatesOK_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) : CandidatesOK S c ↔ S.codes.HasCandidates (c.model h) := by
  constructor
  · intro hc x
    obtain ⟨a, ha⟩ := hc x.val x.isLt
    exact ⟨a, (candidate_iff S c h x a).mp ha⟩
  · intro hc x hx
    obtain ⟨a, ha⟩ := hc ⟨x, hx⟩
    exact ⟨a, (candidate_iff S c h ⟨x, hx⟩ a).mpr ha⟩

theorem oneRootOK_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) : OneRootOK S c ↔ S.OneRootRules (c.model h) := by
  constructor
  · intro hc r p hp x hx y hy hxy a b ha hb hab
    have hpeq : {x, y} = p := by
      apply Finset.eq_of_subset_of_card_le
      · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hx hy
      · rw [(c.model h).dataLink_uniform r p hp]
        simp [hxy]
    have he : c.RootEdge r x.val y.val := (c.rootEdge_iff h r x y).mpr
      (hpeq ▸ ((c.model h).mem_dataLink r p).mp hp)
    exact hc r x.val x.isLt y.val y.isLt a b he
      ((declared_iff S c h x a).mpr ha) ((declared_iff S c h y b).mpr hb) hab
  · intro hc r x hx y hy a b he ha hb hab
    let x' : Fin c.size := ⟨x, hx⟩
    let y' : Fin c.size := ⟨y, hy⟩
    have hp := ((c.model h).mem_dataLink r {x', y'}).mpr ((c.rootEdge_iff h r x' y').mp he)
    have hxy : x' ≠ y' := by
      intro hxy
      have hp2 := (c.model h).dataLink_uniform r {x', y'} hp
      simp [hxy] at hp2
    exact hc r {x', y'} hp x' (by simp) y' (by simp) hxy a b
      ((declared_iff S c h x' a).mp ha) ((declared_iff S c h y' b).mp hb) hab

theorem matchingOK_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) : MatchingOK S c ↔ ∀ e, S.IsMatching (c.model h) e := by
  constructor
  · intro hc e
    constructor
    · rintro ⟨x, y⟩ hp ⟨z, w⟩ hq heq
      change x = z at heq
      subst z
      refine Prod.ext (by rfl) ?_
      exact Fin.ext ((hc e x.val x.isLt y.val y.isLt w.val w.isLt).1
        ((relation_iff S c h e x y).mpr hp) ((relation_iff S c h e x w).mpr hq))
    · rintro ⟨x, y⟩ hp ⟨z, w⟩ hq heq
      change y = w at heq
      subst w
      refine Prod.ext ?_ (by rfl)
      exact Fin.ext ((hc e y.val y.isLt x.val x.isLt z.val z.isLt).2
        ((relation_iff S c h e x y).mpr hp) ((relation_iff S c h e z y).mpr hq))
  · intro hc e x hx y hy z hz
    let x' : Fin c.size := ⟨x, hx⟩
    let y' : Fin c.size := ⟨y, hy⟩
    let z' : Fin c.size := ⟨z, hz⟩
    constructor
    · intro hxy hxz
      exact congrArg (fun p : Fin c.size × Fin c.size => p.2.val)
        ((hc e).1 ((relation_iff S c h e x' y').mp hxy)
          ((relation_iff S c h e x' z').mp hxz) rfl)
    · intro hyx hzx
      exact congrArg (fun p : Fin c.size × Fin c.size => p.1.val)
        ((hc e).2 ((relation_iff S c h e y' x').mp hyx)
          ((relation_iff S c h e z' x').mp hzx) rfl)

theorem oneMarkerOK_iff (c : RootedCode Roots) (h : c.Valid) :
    OneMarkerOK c ↔ (c.model h).dataTriples.card ≤ 1 := by
  constructor
  · intro hc
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨a, b, d, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((c.model h).dataTriples_uniform p hp)
    obtain ⟨u, v, w, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((c.model h).dataTriples_uniform q hq)
    have ht := hc (a.val, b.val, d.val) ((mem_allTriples _ _).mpr ⟨a.isLt, b.isLt, d.isLt⟩)
      (u.val, v.val, w.val) ((mem_allTriples _ _).mpr ⟨u.isLt, v.isLt, w.isLt⟩)
      ((c.dataEdge_iff h a b d).mpr (((c.model h).mem_dataTriples _).mp hp))
      ((c.dataEdge_iff h u v w).mpr (((c.model h).mem_dataTriples _).mp hq))
    apply Finset.image_injective Fin.val_injective
    simpa only [Finset.image_insert, Finset.image_singleton, tripleSet] using (sameTriple_iff _ _).mp ht
  · intro hc t ht s hs het hes
    obtain ⟨hta, htb, htd⟩ := (mem_allTriples _ _).mp ht
    obtain ⟨hsa, hsb, hsd⟩ := (mem_allTriples _ _).mp hs
    let a : Fin c.size := ⟨t.1, hta⟩
    let b : Fin c.size := ⟨t.2.1, htb⟩
    let d : Fin c.size := ⟨t.2.2, htd⟩
    let u : Fin c.size := ⟨s.1, hsa⟩
    let v : Fin c.size := ⟨s.2.1, hsb⟩
    let w : Fin c.size := ⟨s.2.2, hsd⟩
    have hp := ((c.model h).mem_dataTriples _).mpr ((c.dataEdge_iff h a b d).mp het)
    have hq := ((c.model h).mem_dataTriples _).mpr ((c.dataEdge_iff h u v w).mp hes)
    have heq := Finset.card_le_one.mp hc _ hp _ hq
    apply (sameTriple_iff t s).mpr
    simpa only [Finset.image_insert, Finset.image_singleton, a, b, d, u, v, w, tripleSet]
      using congrArg (Finset.image (Fin.val : Fin c.size → ℕ)) heq

theorem markerTypesOK_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) : MarkerTypesOK S c ↔ S.MarkerTypes (c.model h) := by
  constructor
  · intro hc p hp x hx a ha
    obtain ⟨u, v, w, _, _, _, rfl⟩ := Finset.card_eq_three.mp ((c.model h).dataTriples_uniform p hp)
    have he := ((c.model h).mem_dataTriples _).mp hp
    have hd := (declared_iff S c h x a).mpr ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hc x.val x.isLt v.val v.isLt w.val w.isLt a ((c.dataEdge_iff h x v w).mpr he) hd
    · exact hc x.val x.isLt u.val u.isLt w.val w.isLt a
        ((c.dataEdge_iff h x u w).mpr (by simpa only [Finset.insert_comm] using he)) hd
    · exact hc x.val x.isLt u.val u.isLt v.val v.isLt a
        ((c.dataEdge_iff h x u v).mpr (by convert he using 1 <;> ext z <;> simp; tauto)) hd
  · intro hc x hx y hy z hz a he ha
    let x' : Fin c.size := ⟨x, hx⟩
    let y' : Fin c.size := ⟨y, hy⟩
    let z' : Fin c.size := ⟨z, hz⟩
    exact hc {x', y', z'} (((c.model h).mem_dataTriples _).mpr ((c.dataEdge_iff h x' y' z').mp he))
      x' (by simp) a ((declared_iff S c h x' a).mp ha)

/-- Every bounded incidence check is equivalent to its actual H1--H4 rule. -/
theorem incidenceOK_iff (S : CompilerSignature Roots Code Kinds L) (c : RootedCode Roots)
    (h : c.Valid) : IncidenceOK S c ↔ S.IncidenceLegal (c.model h) := by
  rw [IncidenceOK, candidatesOK_iff S c h, oneRootOK_iff S c h,
    matchingOK_iff S c h, oneMarkerOK_iff c h, markerTypesOK_iff S c h]
  exact ⟨fun ⟨hc, hr, hm, he, ht⟩ => ⟨hc, hr, hm, he, ht⟩,
    fun h => ⟨h.candidates, h.oneRoot, h.matching, h.oneMarker, h.markerTypes⟩⟩

end TuranUniversality.Effective.RootedCode
