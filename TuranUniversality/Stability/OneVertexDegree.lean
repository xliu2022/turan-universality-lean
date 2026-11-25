module

public import TuranUniversality.Stability.Degree

@[expose] public section

/-! # Minimum degree after deleting one vertex

An explicit order condition absorbs the lost link edges. This supplies
the finite tolerance needed to pass from common-frame existence in large
canonical graphs to genuine vertex extendability.
-/

namespace TuranUniversality.Stability

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

theorem MinimumDegree.induced_erase {G : RGraph V r} (hr : 2 ≤ r)
    {d η : ℝ} (hmin : MinimumDegree G d) (hd : 0 ≤ d - η)
    (hscale : 1 ≤ η * Fintype.card V) (v : V) :
    MinimumDegree (G.induced (Finset.univ.erase v)) (d - η) := by
  classical
  intro w
  have hcard : Fintype.card ↥(Finset.univ.erase v : Finset V) ≤ Fintype.card V := by
    simp
  have hloss : (G.degree w.val : ℝ) ≤
      ((G.induced (Finset.univ.erase v)).degree w : ℝ) +
        (Fintype.card V : ℝ) ^ (r - 2) := by
    have h := G.degree_induced_loss (Finset.univ.erase v) w
    have hs : (Finset.univ \ (Finset.univ.erase v : Finset V)).card = 1 := by
      have heq : Finset.univ \ (Finset.univ.erase v : Finset V) = {v} := by
        ext w
        simp
      rw [heq, Finset.card_singleton]
    rw [hs, one_mul] at h
    exact_mod_cast h
  have hpow : (Fintype.card V : ℝ) ^ (r - 1) =
      (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (r - 2) := by
    have he : r - 1 = r - 2 + 1 := by omega
    rw [he, pow_succ']
  have hsmall : (Fintype.card V : ℝ) ^ (r - 2) ≤
      η * (Fintype.card V : ℝ) ^ (r - 1) := by
    calc
      _ ≤ (η * Fintype.card V) * (Fintype.card V : ℝ) ^ (r - 2) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale
          (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) _)
      _ = _ := by rw [hpow]; ring
  have hcardR : (Fintype.card ↥(Finset.univ.erase v : Finset V) : ℝ) ≤
      (Fintype.card V : ℝ) := by exact_mod_cast hcard
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (by positivity) hcardR (r - 1)) hd).trans
  have h := hmin w.val
  nlinarith

theorem incident_edge_of_minimumDegree {G : RGraph V r} {d : ℝ}
    (hd : 0 < d) (hmin : MinimumDegree G d) (v : V) : ∃ e ∈ G.edges, v ∈ e := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hdeg : (0 : ℝ) < G.degree v := (mul_pos hd (pow_pos hn' _)).trans_le (hmin v)
  have hcard : 0 < (G.edges.filter (fun e => v ∈ e)).card := by exact_mod_cast hdeg
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

end TuranUniversality.Stability
