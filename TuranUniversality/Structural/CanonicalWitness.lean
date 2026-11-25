module

public import TuranUniversality.Structural.CanonicalLocal
public import TuranUniversality.Structural.OrdinaryFamily

@[expose] public section

/-! # Bounded edge witnesses excluding a prescribed vertex role

For each data four-set and label, one actual declaring edge suffices. Thus
the witness has at most `max 2 (7 * choose Q 4)` edges, independently of
the sizes of the root classes. Retaining those edges and their old roles
retains the failure in every larger graph.
-/

namespace TuranUniversality.Structural.Roles

open Cube Support Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem Admissible.mono_edges {B : Finset (FiniteGraph 3)}
    {Ω : Label → Finset (Word b)} {G H : RGraph V (t + (3 * b + 4))}
    {ρ : V → Option (Roots b t)} (hG : Admissible B Ω G ρ) (hHG : H.edges ⊆ G.edges) :
    Admissible B Ω H ρ := by
  refine ⟨fun e he => hG.1 e (hHG he), ?_⟩
  intro S hS
  obtain ⟨O, hO, hh⟩ := hG.2 S hS
  exact ⟨O, hO, fun e he heS => hh e (hHG he) heS⟩

theorem Admissible.congr_roles {B : Finset (FiniteGraph 3)}
    {Ω : Label → Finset (Word b)} {G : RGraph V (t + (3 * b + 4))}
    {ρ σ : V → Option (Roots b t)} (hG : Admissible B Ω G ρ)
    (h : ∀ e ∈ G.edges, ∀ v ∈ e, ρ v = σ v) : Admissible B Ω G σ := by
  refine ⟨fun e he => (goodEdge_congr Ω ρ σ e (h e he)).mp (hG.1 e he), ?_⟩
  intro S hS
  obtain ⟨O, hO, hh⟩ := hG.2 S hS
  refine ⟨O, hO, ?_⟩
  intro e he heS
  apply (fits_congr Ω ρ σ O e (h e he)).mp
  apply hh e he
  rwa [dataSet_congr ρ σ e (h e he)]

theorem failed_role_witness (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (ρ : V → Option (Roots b t))
    (hbad : ¬ Admissible B Ω G ρ) :
    ∃ E : Finset (Finset V), E ⊆ G.edges ∧ E.card ≤ Ordinary.roleWitnessEdges B ∧
      ∀ (H : RGraph V (t + (3 * b + 4))) (σ : V → Option (Roots b t)),
        E ⊆ H.edges → (∀ e ∈ E, ∀ v ∈ e, σ v = ρ v) → ¬ Admissible B Ω H σ := by
  classical
  by_cases hgood : ∀ e ∈ G.edges, GoodEdge Ω ρ e
  · have hlocal : ¬ LocallyLegal B Ω G ρ := fun h => hbad ⟨hgood, h⟩
    unfold LocallyLegal at hlocal
    push Not at hlocal
    obtain ⟨S, hScard, hfailure⟩ := hlocal
    let I : Finset (Finset V × Label) :=
      (S.powersetCard 4 ×ˢ (Finset.univ : Finset Label)).filter fun a =>
        ∃ e ∈ G.edges, dataSet ρ e = a.1 ∧ Declares Ω ρ e a.2
    have hw (a : I) : ∃ e ∈ G.edges, dataSet ρ e = a.val.1 ∧ Declares Ω ρ e a.val.2 :=
      (Finset.mem_filter.mp a.property).2
    choose edge hedge hdata hdecl using hw
    let E := Finset.univ.image edge
    have hE (a : I) : edge a ∈ E := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      exact hedge a
    · calc
        E.card ≤ Fintype.card I := by simpa [E] using (Finset.card_image_le (s := Finset.univ) (f := edge))
        _ = I.card := Fintype.card_coe _
        _ ≤ (S.powersetCard 4 ×ˢ (Finset.univ : Finset Label)).card := Finset.card_filter_le _ _
        _ = 7 * S.card.choose 4 := by simp [Finset.card_product, Label.card, Nat.mul_comm]
        _ ≤ 7 * (RecordSystem.cutoff B).choose 4 := Nat.mul_le_mul_left 7 (Nat.choose_le_choose 4 hScard)
        _ ≤ Ordinary.roleWitnessEdges B := le_max_right _ _
    · intro H σ hEH hagree hH
      obtain ⟨O, hOS, hfits⟩ := hH.2 S hScard
      obtain ⟨e, he, heS, hnot⟩ := hfailure O hOS
      apply hnot
      obtain ⟨hc, l, hl⟩ := hgood e he
      have hi : (dataSet ρ e, l) ∈ I := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨heS, hc⟩,
          Finset.mem_univ _⟩, e, he, rfl, hl⟩
      let a : I := ⟨(dataSet ρ e, l), hi⟩
      have hde : dataSet ρ (edge a) = dataSet ρ e := hdata a
      have hsame : ∀ v ∈ edge a, σ v = ρ v := hagree (edge a) (hE a)
      have hfσ := hfits (edge a) (hEH (hE a)) (by
        rw [dataSet_congr σ ρ (edge a) hsame, hde]
        exact heS)
      have hfρ := (fits_congr Ω σ ρ O (edge a) hsame).mp hfσ
      have hlabel := declares_unique Ω hdis ρ (edge a) (hdecl a)
        ((fits_iff_declares Ω ρ O (edge a) (by rw [hde]; exact hc)).mp hfρ)
      change l = O.label (dataSet ρ (edge a)) at hlabel
      rw [hde] at hlabel
      apply (fits_iff_declares Ω ρ O e hc).mpr
      rw [← hlabel]
      exact hl
  · push Not at hgood
    obtain ⟨e, he, hfail⟩ := hgood
    refine ⟨{e}, Finset.singleton_subset_iff.mpr he, ?_, ?_⟩
    · simp only [Finset.card_singleton]
      exact (by omega : 1 ≤ 2).trans (le_max_left _ _)
    · intro H σ hEH hagree hH
      exact hfail ((goodEdge_congr Ω σ ρ e (hagree e (Finset.mem_singleton_self _))).mp
        (hH.1 e (hEH (Finset.mem_singleton_self _))))

end TuranUniversality.Structural.Roles
