module

public import TuranUniversality.Stability.VertexExtension
public import TuranUniversality.Hypergraph.Symmetrization

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The genuine finite Ψ trick

A counterexample is chosen among actual graphs on the fixed finite carrier,
maximizing edge count and ordered twin pairs lexicographically. A single
clone increases this score. The larger graph supplies a good induced
subgraph; deleting the two small exceptional sets and the cloned vertex
makes it an induced subgraph of the original graph. The one-vertex
extension theorem then adds back every desired vertex.
-/

namespace TuranUniversality.Stability

universe u
variable {r : ℕ} {V : Type u} [DecidableEq V] [Fintype V]

noncomputable def goodVertices (G : RGraph V r) (Λ δ : ℝ) : Finset V :=
  Finset.univ \ G.lowDegreeSet Λ δ

theorem degree_gt_of_good (G : RGraph V r) {Λ δ : ℝ} {v : V}
    (hv : v ∈ goodVertices G Λ δ) :
    ((r : ℝ) * Λ - δ) * (Fintype.card V : ℝ) ^ (r - 1) < (G.degree v : ℝ) := by
  classical
  have h := (Finset.mem_sdiff.mp hv).2
  simpa only [RGraph.lowDegreeSet, Finset.mem_filter, Finset.mem_univ, true_and,
    not_le] using h

/-- The near-extremal conclusion underlying degree stability. All its
inputs are genuine hom-closure, polynomial, symmetrization, and one-vertex
extension properties of the specified classes. -/
theorem good_induced_of_near (B C : GraphClass.{u} r)
    (hr : 2 ≤ r) (hB : HomClosed B) (hC : EmbeddingClosed C)
    {Λ δ εs : ℝ} {Ns Nv : ℕ} (hbound : PolynomialBound B Λ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 6) (hd : 0 ≤ (r : ℝ) * Λ - 4 * δ)
    (hsym : SymmetrizedStable B C Λ εs Ns)
    (hext : VertexExtendable B C ((r : ℝ) * Λ - 4 * δ) Nv)
    (G : RGraph V r) (hG : B G) (hn : 0 < Fintype.card V)
    (hNs : Ns ≤ Fintype.card V) (hNv : 2 * Nv ≤ Fintype.card V)
    (hscale : 1 ≤ δ * Fintype.card V)
    (hnear : (Λ - min εs (Density.lowDegreeTolerance r δ)) *
      (Fintype.card V : ℝ) ^ r ≤ (G.edges.card : ℝ)) :
    C (G.induced (goodVertices G Λ δ)) := by
  classical
  let ε := min εs (Density.lowDegreeTolerance r δ)
  let T := Finset.univ.filter (fun H : RGraph V r => B H ∧
    (Λ - ε) * (Fintype.card V : ℝ) ^ r ≤ (H.edges.card : ℝ) ∧
    ¬ C (H.induced (goodVertices H Λ δ)))
  by_contra hfail
  have hGT : G ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG, hnear, hfail⟩
  obtain ⟨H, hHT, hmax⟩ := Finset.exists_max_image T RGraph.cloneScore ⟨G, hGT⟩
  obtain ⟨hH, hHnear, hHbad⟩ := (Finset.mem_filter.mp hHT).2
  have hpower : 0 ≤ (Fintype.card V : ℝ) ^ r := by positivity
  have hsymnear : (Λ - εs) * (Fintype.card V : ℝ) ^ r ≤ (H.edges.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left (min_le_left _ _) _) hpower).trans hHnear
  have hnotsym : ¬ H.Symmetrized := fun hs =>
    hHbad (hC (H.induced_isEmbedding _) (hsym H hH hNs hsymnear hs))
  obtain ⟨u, v, _, _, he, hscore⟩ := H.exists_clone_improvement hnotsym
  let J := H.clone u v
  have hJ : B J := hB (H.clone_isHom u v) hH
  have hJnear : (Λ - ε) * (Fintype.card V : ℝ) ^ r ≤ (J.edges.card : ℝ) := by
    have he' : (H.edges.card : ℝ) ≤ J.edges.card := by exact_mod_cast he
    exact hHnear.trans he'
  have hCJ : C (J.induced (goodVertices J Λ δ)) := by
    by_contra h
    have hm : J ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ, hJnear, h⟩
    exact (not_lt_of_ge (hmax J hm)) hscore
  have hnearLow (K : RGraph V r)
      (hk : (Λ - ε) * (Fintype.card V : ℝ) ^ r ≤ (K.edges.card : ℝ)) :
      (Λ - Density.lowDegreeTolerance r δ) * (Fintype.card V : ℝ) ^ r ≤
        (K.edges.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left (min_le_right _ _) _) hpower).trans hk
  have hZH := H.lowDegreeSet_card_le hn hδ (hbound H hH) (hnearLow H hHnear)
  have hZJ := J.lowDegreeSet_card_le hn hδ (hbound J hJ) (hnearLow J hJnear)
  let R := Finset.univ \ insert u (H.lowDegreeSet Λ δ ∪ J.lowDegreeSet Λ δ)
  have hRS : R ⊆ goodVertices H Λ δ := by
    intro w hw
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hz
    exact (Finset.mem_sdiff.mp hw).2
      (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
  have hRT : R ⊆ goodVertices J Λ δ := by
    intro w hw
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hz
    exact (Finset.mem_sdiff.mp hw).2
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
  have huR : u ∉ R := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
  have hCR : C (H.induced R) :=
    hC (H.induced_clone_away_embedding u v hRT huR) hCJ
  have hRsmall : ((Finset.univ \ R).card : ℝ) ≤ (3 * δ) * Fintype.card V := by
    have hcomp : Finset.univ \ R = insert u (H.lowDegreeSet Λ δ ∪ J.lowDegreeSet Λ δ) :=
      Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
    have hc : (Finset.univ \ R).card ≤
        (H.lowDegreeSet Λ δ).card + (J.lowDegreeSet Λ δ).card + 1 := by
      rw [hcomp]
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) 1)
    have hc' : ((Finset.univ \ R).card : ℝ) ≤
        (H.lowDegreeSet Λ δ).card + (J.lowDegreeSet Λ δ).card + 1 := by exact_mod_cast hc
    nlinarith
  have hNR : Nv ≤ R.card := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
    have hc : ((Finset.univ \ R).card : ℝ) + R.card = Fintype.card V := by
      exact_mod_cast hcard
    have hnv' : 2 * (Nv : ℝ) ≤ Fintype.card V := by exact_mod_cast hNv
    have hδn := mul_le_mul_of_nonneg_right hδsmall (Nat.cast_nonneg (Fintype.card V))
    have hreal : (Nv : ℝ) ≤ R.card := by nlinarith
    exact_mod_cast hreal
  apply hHbad
  apply extend_induced_of_small_complement B C hB hC hr hd hext H hH R
    (goodVertices H Λ δ) hRS hNR hRsmall _ hCR
  intro w hw
  have h := (degree_gt_of_good H hw).le
  convert h using 1 <;> ring

end TuranUniversality.Stability
