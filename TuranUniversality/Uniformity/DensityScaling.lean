module

public import TuranUniversality.Uniformity.Transfer
public import TuranUniversality.Uniformity.AdmissibleWeights
public import TuranUniversality.Density.FamilyUpper
public import TuranUniversality.Density.UpperBridge

@[expose] public section

/-! # Exact ordinary density scaling for the actual finite extension family

The upper bound compresses every ordinary family-free host into an admissible
support. The reverse inequality suspends every hom-free inner template and
then invokes the already proved single-three-graph upper bridge. No class
supremum or assumed density identity is used.
-/

namespace TuranUniversality.Uniformity

theorem family_density_upper (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r) :
    familyTuranDensity (family P r) ≤
      (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) * turanDensity P.2 := by
  apply familyTuranDensity_upper_of_weighted_free (family P r)
    (fun _ h => family_has_edges P r h)
  intro n G x hfree hx
  obtain ⟨y, hy, hxy, hcover⟩ := G.exists_compressed_weights x hx
  have hadm := compressed_support_admissible P r hr G hfree y hcover
  have hb := admissible_weighted_bound P (G.supportGraph y) hadm
    (fun v => y v.val) (support_probability y hy)
  calc
    (r.factorial : ℝ) * G.edgePolynomial x ≤
        (r.factorial : ℝ) * G.edgePolynomial y :=
      mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg _)
    _ = (r.factorial : ℝ) * (G.supportGraph y).edgePolynomial (fun v => y v.val) := by
      rw [G.supportGraph_polynomial]
    _ ≤ _ := hb

theorem family_density_lower_add_three (P : FiniteGraph 3)
    (hP : P.2.edges.Nonempty) (s : ℕ) :
    (27 * ((s + 3).factorial : ℝ) / (6 * ((s + 3 : ℕ) : ℝ) ^ (s + 3))) *
      turanDensity P.2 ≤ familyTuranDensity (family P (s + 3)) := by
  let c : ℝ := 27 * ((s + 3).factorial : ℝ) / (6 * ((s + 3 : ℕ) : ℝ) ^ (s + 3))
  let d : ℝ := familyTuranDensity (family P (s + 3))
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 ≤ d := familyTuranDensity_nonneg _
  have hinner : turanDensity P.2 ≤ d / c := by
    apply turanDensity_upper_of_homFree P.2 (Finset.card_pos.mpr hP) (d / c)
      (div_nonneg hd hc.le)
    intro n G hfree
    by_cases hn : n = 0
    · subst n
      simpa [RGraph.oneEdge_homDensity] using div_nonneg hd hc.le
    · let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      let x : Fin n → ℝ := fun _ => (Fintype.card (Fin n) : ℝ)⁻¹
      have hx : ProbabilityWeights x := probabilityWeights_uniform
      have hadm : Admissible P.2 (G.suspension s) := Admissible.suspension P.2 G s hfree
      have hout := familyTuranDensity_lower_of_homFree (family P (s + 3))
        (G.suspension s) (familyHomFree_of_admissible P (s + 3) _ hadm)
        (RGraph.suspensionWeights s x) (RGraph.suspensionWeights_probability s x hx)
      rw [G.suspensionWeights_value] at hout
      have hvalue : ((s + 3).factorial : ℝ) *
          (27 / (s + 3 : ℝ) ^ (s + 3) * G.edgePolynomial x) =
          c * (RGraph.oneEdge 3).homDensity G := by
        rw [G.oneEdge_homDensity_polynomial]
        rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num]
        dsimp only [c, x]
        simp only [Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
        ring
      rw [hvalue] at hout
      apply (le_div_iff₀ hc).mpr
      simpa [mul_comm] using hout
  have h := (le_div_iff₀ hc).mp hinner
  simpa only [c, d, mul_comm] using h

theorem family_density_lower (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r)
    (hP : P.2.edges.Nonempty) :
    (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) * turanDensity P.2 ≤
      familyTuranDensity (family P r) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, (Nat.sub_add_cancel hr).symm⟩
  exact family_density_lower_add_three P hP s

/-- The exact scale factor for the concrete bounded-basis extension family. -/
theorem family_density_eq (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r)
    (hP : P.2.edges.Nonempty) :
    familyTuranDensity (family P r) =
      (27 * (r.factorial : ℝ) / (6 * (r : ℝ) ^ r)) * turanDensity P.2 :=
  le_antisymm (family_density_upper P r hr) (family_density_lower P r hr hP)

end TuranUniversality.Uniformity
