module

public import TuranUniversality.Structural.ExtremalProfiles

@[expose] public section

/-! # Ordinary hom-free sequences realizing the inner profile space

The sequence consists of genuine labelled finite graphs of positive order.
Its orders tend to infinity. Hom-freeness is obtained by applying ordinary
free realization to the finite homomorphic closure, retaining all vertices.
-/

open Filter Topology

namespace TuranUniversality.SetFamily

variable {r : ℕ}

theorem exists_positive_homFree_sequence (F : Finset (FiniteGraph r))
    (W : Profile r) (hW : W ∈ freeLimitProfiles (F : Set (FiniteGraph r))) :
    ∃ G : ℕ → FiniteGraph r,
      (∀ n, 0 < (G n).1) ∧ (∀ n, familyHomFree F (G n).2) ∧
      Tendsto (fun n => (G n).1) atTop atTop ∧
      Tendsto (fun n => profile (G n)) atTop (𝓝 W) := by
  have hB := (hW.1.vanishes_homomorphicClosure_iff W F).mpr hW.2
  obtain ⟨G, hG, hsize, hlim⟩ := isFreeLimit_of_vanishing
    (TuranUniversality.homomorphicClosure F : Set (FiniteGraph r)) W hW.1 hB
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsize.eventually (eventually_ge_atTop 1))
  refine ⟨fun n => G (n + N), ?_, ?_, hsize.comp (tendsto_add_atTop_nat N),
    hlim.comp (tendsto_add_atTop_nat N)⟩
  · intro n
    exact lt_of_lt_of_le Nat.zero_lt_one (hN _ (Nat.le_add_left N n))
  · intro n
    exact (familyFree_homomorphicClosure_iff F (G (n + N)).2).mp (hG (n + N))

theorem exists_extremal_homFree_sequence (F : Finset (FiniteGraph r))
    (W : Profile r) (hW : W ∈ extremalProfiles F) :
    ∃ G : ℕ → FiniteGraph r,
      (∀ n, 0 < (G n).1) ∧ (∀ n, familyHomFree F (G n).2) ∧
      Tendsto (fun n => (G n).1) atTop atTop ∧
      Tendsto (fun n => profile (G n)) atTop (𝓝 W) ∧
      Tendsto (fun n => (RGraph.oneEdge r).homDensity (G n).2) atTop
        (𝓝 (familyTuranDensity F)) := by
  obtain ⟨G, hpos, hfree, hsize, hlim⟩ := exists_positive_homFree_sequence F W hW.1
  refine ⟨G, hpos, hfree, hsize, hlim, ?_⟩
  have h := (tendsto_pi_nhds.mp hlim) (edgeTest r)
  rw [hW.2] at h
  exact h

end TuranUniversality.SetFamily
