module

public import TuranUniversality.Stability.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Iterating a genuine one-vertex extension theorem

The starting set may omit a small number of vertices. Degree losses are
counted in the original graph, and every intermediate graph is an actual
induced subgraph. This is the finite extension step in the Ψ proof.
-/

namespace TuranUniversality.Stability

universe u
variable {r : ℕ} {V : Type u} [DecidableEq V] [Fintype V]

theorem minimumDegree_induced_of_loss (G : RGraph V r) (hr : 2 ≤ r)
    (S : Finset V) {d ρ : ℝ} (hd : 0 ≤ d)
    (hsmall : ((Finset.univ \ S).card : ℝ) ≤ ρ * Fintype.card V)
    (hdeg : ∀ v ∈ S, (d + ρ) * (Fintype.card V : ℝ) ^ (r - 1) ≤ (G.degree v : ℝ)) :
    MinimumDegree (G.induced S) d := by
  intro v
  have hl : (G.degree v.val : ℝ) ≤ ((G.induced S).degree v : ℝ) +
      ((Finset.univ \ S).card : ℝ) * (Fintype.card V : ℝ) ^ (r - 2) := by
    exact_mod_cast G.degree_induced_loss S v
  have he : r - 2 + 1 = r - 1 := by omega
  have hm := mul_le_mul_of_nonneg_right hsmall
    (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) (r - 2))
  rw [mul_assoc, ← pow_succ', he] at hm
  have hp : (S.card : ℝ) ^ (r - 1) ≤ (Fintype.card V : ℝ) ^ (r - 1) := by
    gcongr
    exact_mod_cast Finset.card_le_univ S
  have hmul := mul_le_mul_of_nonneg_left hp hd
  have hv := hdeg v.val v.property
  simp only [Fintype.card_coe]
  nlinarith

theorem extend_induced_of_small_complement (B C : GraphClass.{u} r)
    (hB : HomClosed B) (hC : EmbeddingClosed C) (hr : 2 ≤ r)
    {d ρ : ℝ} (hd : 0 ≤ d) {N : ℕ} (hext : VertexExtendable B C d N)
    (G : RGraph V r) (hG : B G) (R S : Finset V) (hRS : R ⊆ S)
    (hN : N ≤ R.card) (hsmall : ((Finset.univ \ R).card : ℝ) ≤ ρ * Fintype.card V)
    (hdeg : ∀ v ∈ S, (d + ρ) * (Fintype.card V : ℝ) ^ (r - 1) ≤ (G.degree v : ℝ))
    (hstart : C (G.induced R)) : C (G.induced S) := by
  classical
  let Tset := S.powerset.filter (fun T => R ⊆ T ∧ C (G.induced T))
  have hR : R ∈ Tset := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hRS, Finset.Subset.refl _, hstart⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image Tset Finset.card ⟨R, hR⟩
  obtain ⟨hTS, hRT, hCT⟩ := (show T ⊆ S ∧ R ⊆ T ∧ C (G.induced T) from
    ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1, (Finset.mem_filter.mp hT).2⟩)
  by_cases heq : T = S
  · subst T
    exact hCT
  have hproper : ¬ S ⊆ T := fun h => heq (Finset.Subset.antisymm hTS h)
  obtain ⟨v, hvS, hvT⟩ := Finset.not_subset.mp hproper
  let T' := insert v T
  have hTT' : T ⊆ T' := Finset.subset_insert _ _
  have hRT' : R ⊆ T' := hRT.trans hTT'
  have hT'S : T' ⊆ S := Finset.insert_subset hvS hTS
  have hmin : MinimumDegree (G.induced T') d := by
    apply minimumDegree_induced_of_loss G hr T' hd
    · have hsub : Finset.univ \ T' ⊆ Finset.univ \ R := by
        intro w hw
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hw).1,
          fun h => (Finset.mem_sdiff.mp hw).2 (hRT' h)⟩
      have hc : ((Finset.univ \ T').card : ℝ) ≤ (Finset.univ \ R).card := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc.trans hsmall
    · exact fun w hw => hdeg w (hT'S hw)
  have hfree : B (G.induced T') := hB (G.induced_isEmbedding T').2 hG
  have hsize : N ≤ Fintype.card T' := by
    simpa only [Fintype.card_coe] using hN.trans (Finset.card_le_card hRT')
  obtain ⟨f, hf⟩ := G.exists_embedding_deleted_insert T v
  have hnext : C (G.induced T') := hext _ hfree hsize hmin
    ⟨v, Finset.mem_insert_self _ _⟩ (hC hf hCT)
  have hnextmem : T' ∈ Tset := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hT'S, hRT', hnext⟩
  have hc := hmax T' hnextmem
  have hcard : T'.card = T.card + 1 := Finset.card_insert_of_notMem hvT
  omega

end TuranUniversality.Stability
