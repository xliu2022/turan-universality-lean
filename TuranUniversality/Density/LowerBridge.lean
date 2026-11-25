module

public import TuranUniversality.Density.SampleMoments
public import TuranUniversality.Density.Extremal
public import TuranUniversality.Hypergraph.BlowupCount

@[expose] public section

/-!
# Ordinary Turán lower bounds from finite hom-free templates

Every sampled graph is ordinary forbidden-free by projection. Its expected
edge count therefore lies below the actual extremal number. This proves the
normalized uniform template lower bound directly, without a blowup limit.
-/

open Filter Topology

namespace TuranUniversality

open Selector Density

universe u

theorem homFree_uniform_le_extremalDensity {k n : ℕ} {V : Type u}
    [DecidableEq V] [Fintype V] [Nonempty V]
    (F : RGraph (Fin k) 3) (G : RGraph V 3) (hfree : F.HomFree G)
    (hn : 3 ≤ n) :
    (RGraph.oneEdge 3).homDensity G ≤ extremalDensity F n := by
  have hpoint (f : Fin n → V) : ((G.sample n f).edges.card : ℝ) ≤
      (extremalNumber F n : ℝ) := by
    exact_mod_cast F.edge_card_le_extremalNumber (G.sample n f)
      (F.sample_homFree G hfree n f).free
  have hmean := mean_mono hpoint
  rw [G.mean_sample_card, mean_const] at hmean
  have hc : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
  apply (le_div_iff₀ hc).mpr
  simpa [mul_comm] using hmean

/-- Every finite hom-free template supplies the usual uniform density lower
bound for the ordinary Turán density. -/
theorem turanDensity_lower_of_homFree {k : ℕ} {V : Type u}
    [DecidableEq V] [Fintype V] [Nonempty V]
    (F : RGraph (Fin k) 3) (hF : 1 ≤ F.edges.card)
    (G : RGraph V 3) (hfree : F.HomFree G) :
    (RGraph.oneEdge 3).homDensity G ≤ turanDensity F := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (extremalDensity_tendsto F hF)
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact homFree_uniform_le_extremalDensity F G hfree hn

theorem turanDensity_lower_uniform_polynomial {k : ℕ} {V : Type u}
    [DecidableEq V] [Fintype V] [Nonempty V]
    (F : RGraph (Fin k) 3) (hF : 1 ≤ F.edges.card)
    (G : RGraph V 3) (hfree : F.HomFree G) :
    6 * G.edgePolynomial (fun _ => (Fintype.card V : ℝ)⁻¹) ≤ turanDensity F := by
  have h := turanDensity_lower_of_homFree F hF G hfree
  rw [G.oneEdge_homDensity_polynomial] at h
  norm_num at h ⊢
  exact h

/-- Integer clone counts supply exact rational-weight lower certificates. -/
theorem turanDensity_lower_integer_weights {k : ℕ} {V : Type u}
    [DecidableEq V] [Fintype V]
    (F : RGraph (Fin k) 3) (hF : 1 ≤ F.edges.card)
    (G : RGraph V 3) (hfree : F.HomFree G) (sizes : V → ℕ)
    (hsizes : 0 < ∑ v, sizes v) :
    6 * G.edgePolynomial (fun v => (sizes v : ℝ) / (∑ w, sizes w : ℕ)) ≤
      turanDensity F := by
  have hcard : 0 < Fintype.card (RGraph.BlowupVertex sizes) := by
    rwa [RGraph.blowup_vertex_card]
  let : Nonempty (RGraph.BlowupVertex sizes) := Fintype.card_pos_iff.mp hcard
  have h := turanDensity_lower_uniform_polynomial F hF (G.blowup sizes)
    (F.blowup_homFree G hfree sizes)
  rwa [G.blowup_polynomial] at h

end TuranUniversality
