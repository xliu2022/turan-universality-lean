module

public import TuranUniversality.Density.NearMaxLinks
public import TuranUniversality.Density.WeightedHomCoupling

@[expose] public section

/-! # Actual missing links of a near-optimal completion

The missing-link polynomial is the exact difference of the two link
polynomials. A global polynomial bound on the completion and a minimum
link bound on the original graph make every missing link uniformly small.
-/

open Filter Topology

namespace TuranUniversality.RGraph

variable {V : Type*} [DecidableEq V] {r : ℕ}

theorem linkGraph_edgeDifference (H G : RGraph V r) (v : V) :
    (H.edgeDifference G).linkGraph v = (H.linkGraph v).edgeDifference (G.linkGraph v) := by
  apply RGraph.ext
  ext s
  change s ∈ (H.edgeDifference G).link v ↔ s ∈ H.link v \ G.link v
  simp only [mem_link, Finset.mem_sdiff, edgeDifference]
  tauto

theorem linkGraph_subset (G H : RGraph V r) (hsub : G.edges ⊆ H.edges) (v : V) :
    (G.linkGraph v).edges ⊆ (H.linkGraph v).edges := by
  intro s hs
  obtain ⟨hv, hs⟩ := (G.mem_link v s).mp hs
  exact (H.mem_link v s).mpr ⟨hv, hsub hs⟩

theorem linkPolynomial_edgeDifference (H G : RGraph V r)
    (hsub : G.edges ⊆ H.edges) (x : V → ℝ) (v : V) :
    (H.edgeDifference G).linkPolynomial x v = H.linkPolynomial x v - G.linkPolynomial x v := by
  rw [← (H.edgeDifference G).linkGraph_polynomial, linkGraph_edgeDifference,
    edgeDifference_polynomial _ _ (linkGraph_subset G H hsub v),
    H.linkGraph_polynomial, G.linkGraph_polynomial]

end TuranUniversality.RGraph

namespace TuranUniversality.Density

theorem eventually_uniform_missing_link_bound {r : ℕ} {V : ℕ → Type*}
    [∀ n, DecidableEq (V n)] [∀ n, Fintype (V n)]
    (G H : ∀ n, RGraph (V n) r) (hsub : ∀ n, (G n).edges ⊆ (H n).edges)
    (x : ∀ n, V n → ℝ) (hx : ∀ n, ProbabilityWeights (x n)) {Λ : ℝ}
    (hbound : ∀ n y, ProbabilityWeights y → (H n).edgePolynomial y ≤ Λ)
    (hlim : Tendsto (fun n => (G n).edgePolynomial (x n)) atTop (𝓝 Λ))
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v,
      (r : ℝ) * Λ - ε ≤ (G n).linkPolynomial (x n) v)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v, ((H n).edgeDifference (G n)).linkPolynomial (x n) v ≤ ε := by
  have hH : Tendsto (fun n => (H n).edgePolynomial (x n)) atTop (𝓝 Λ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
      (fun n => (G n).edgePolynomial_mono (H n) (hsub n) (hx n).1)
      (fun n => hbound n (x n) (hx n))
  have hup := eventually_uniform_link_bound H x hx hbound hH (show 0 < ε / 2 by positivity)
  have hlo := hlower (ε / 2) (by positivity)
  filter_upwards [hup, hlo] with n hn hn' v
  rw [(H n).linkPolynomial_edgeDifference (G n) (hsub n)]
  have h1 := hn v
  have h2 := hn' v
  linarith

end TuranUniversality.Density
