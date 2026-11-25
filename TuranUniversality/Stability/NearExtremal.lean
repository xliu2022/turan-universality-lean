module

public import TuranUniversality.Stability.Degree
public import TuranUniversality.Density.LowDegreeConvergence

@[expose] public section

/-! # Canonical induced subgraphs of ordinary near-extremal graphs

Degree stability and the exact global weighted bound imply that deleting
the actual low-degree vertices leaves a graph in the target class. The
deleted proportion tends to zero. The carrier and graph may vary along
an arbitrary filter.
-/

open Filter Topology

namespace TuranUniversality.Stability

universe u v

theorem eventually_good_induced_of_degreeStable
    {r : ℕ} (B C : GraphClass.{u} r) (hr : 2 ≤ r)
    (hB : HomClosed B) {Λ : ℝ} (hΛ : 0 < Λ)
    (hbound : PolynomialBound B Λ) (hstable : DegreeStable B C Λ)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) r) (hG : ∀ i, B (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ r) l (𝓝 Λ)) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun i => (((G i).lowDegreeSet Λ δ).card : ℝ) /
        Fintype.card (V i)) l (𝓝 0) ∧
      ∀ᶠ i in l, 0 < (goodVertices (G i) Λ δ).card ∧
        C ((G i).induced (goodVertices (G i) Λ δ)) := by
  classical
  obtain ⟨ε, hε, N, hstable⟩ := hstable
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let ζ : ℝ := min ε ((r : ℝ) * Λ / 2)
  have hζ : 0 < ζ := lt_min hε (by positivity)
  have hζε : ζ ≤ ε := min_le_left _ _
  have hζΛ : ζ ≤ (r : ℝ) * Λ / 2 := min_le_right _ _
  let δ : ℝ := ζ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hratio := Density.lowDegreeSet_ratio_tendsto_zero G hn hδ
    (fun i => hbound (G i) (hG i)) l hlim
  refine ⟨δ, hδ, hratio, ?_⟩
  have hsmall := (tendsto_order.1 hratio).2 (min δ (1 / 2)) (by positivity)
  have hlarge := hsize.eventually (eventually_ge_atTop (2 * (N + 1)))
  filter_upwards [hsmall, hlarge] with i hi hNi
  let S := goodVertices (G i) Λ δ
  have hcomp : Finset.univ \ S = (G i).lowDegreeSet Λ δ := by
    exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
  have hn0 : (0 : ℝ) < Fintype.card (V i) := by exact_mod_cast hn i
  have hbad : (((G i).lowDegreeSet Λ δ).card : ℝ) ≤
      δ * Fintype.card (V i) := by
    exact ((div_le_iff₀ hn0).mp (hi.le.trans (min_le_left _ _)))
  have hhalf : (((G i).lowDegreeSet Λ δ).card : ℝ) ≤
      (1 / 2 : ℝ) * Fintype.card (V i) := by
    exact ((div_le_iff₀ hn0).mp (hi.le.trans (min_le_right _ _)))
  have hcard : (((G i).lowDegreeSet Λ δ).card : ℝ) + S.card =
      Fintype.card (V i) := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [hcomp, Finset.card_univ] at h
    exact_mod_cast h
  have hNi' : 2 * ((N : ℝ) + 1) ≤ Fintype.card (V i) := by exact_mod_cast hNi
  have hNS : N + 1 ≤ S.card := by
    have h : (N : ℝ) + 1 ≤ S.card := by linarith
    exact_mod_cast h
  refine ⟨show 0 < S.card from lt_of_lt_of_le (by omega : 0 < N + 1) hNS, ?_⟩
  have hmin : MinimumDegree ((G i).induced S) ((r : ℝ) * Λ - ζ) := by
    apply minimumDegree_induced_of_loss (G i) hr S (ρ := δ) (by linarith)
    · simpa only [hcomp] using hbad
    · intro w hw
      have hd := (degree_gt_of_good (G i) hw).le
      convert hd using 1 <;> dsimp [δ] <;> ring
  apply hstable ((G i).induced S)
    (hB ((G i).induced_isEmbedding S).2 (hG i))
    (by simpa only [Fintype.card_coe] using (show N ≤ S.card by omega))
  exact hmin.mono (sub_le_sub_left hζε _)

end TuranUniversality.Stability
