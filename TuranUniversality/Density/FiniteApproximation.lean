module

public import TuranUniversality.Density.HomFreeMax
public import TuranUniversality.Density.FamilyHomUpper

@[expose] public section

/-! # Explicit finite approximation of ordinary Turán densities

For a finite forbidden family `F`, let `a` be the maximum number of edges of
an `F`-hom-free graph on `m` vertices. The ordinary density lies between
`r! * a / m^r` and `a / choose m r`. Their difference is at most
`r * (r - 1) / (2 * m)`. Every quantity in the endpoints is a finite integer
calculation; the effectiveness of the enumeration is treated separately.
-/

namespace TuranUniversality

variable {r : ℕ}

/-- The lower endpoint supplied by an actual finite hom-free extremizer. -/
noncomputable def homFreeLower (F : Finset (FiniteGraph r)) (m : ℕ) : ℝ :=
  (r.factorial : ℝ) * homFreeMax F m / (m : ℝ) ^ r

/-- The upper endpoint obtained by sampling a fixed number of vertices. -/
noncomputable def homFreeUpper (F : Finset (FiniteGraph r)) (m : ℕ) : ℝ :=
  (homFreeMax F m : ℝ) / (m.choose r : ℝ)

theorem homFreeLower_nonneg (F : Finset (FiniteGraph r)) (m : ℕ) :
    0 ≤ homFreeLower F m := by
  unfold homFreeLower
  positivity

theorem homFreeUpper_nonneg (F : Finset (FiniteGraph r)) (m : ℕ) :
    0 ≤ homFreeUpper F m := by
  unfold homFreeUpper
  positivity

theorem samplingFactor_nonneg (r m : ℕ) : 0 ≤ samplingFactor r m := by
  unfold samplingFactor
  positivity

theorem samplingFactor_pos (r m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    0 < samplingFactor r m := by
  have hchoose : (0 : ℝ) < m.choose r := by exact_mod_cast Nat.choose_pos hr
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  unfold samplingFactor
  positivity

theorem samplingFactor_le_one (r m : ℕ) (hm : 0 < m) :
    samplingFactor r m ≤ 1 := by
  rw [samplingFactor_descFactorial]
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  apply (div_le_one (pow_pos hmreal r)).mpr
  exact_mod_cast Nat.descFactorial_le_pow m r

/-- The chance of a collision among `r` independent samples is at most the
sum of the pairwise collision probabilities. This algebraic proof applies
directly to the descending-factorial sampling factor. -/
theorem samplingFactor_deficit_bound (r m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    1 - samplingFactor r m ≤ (r : ℝ) * ((r : ℝ) - 1) / (2 * (m : ℝ)) := by
  induction r generalizing m with
  | zero => simp [samplingFactor]
  | succ r ih =>
    have hrm : r ≤ m := by omega
    have hih := ih m hm hrm
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have hterm : samplingFactor r m * ((r : ℝ) / (m : ℝ)) ≤
        (r : ℝ) / (m : ℝ) :=
      mul_le_of_le_one_left (by positivity) (samplingFactor_le_one r m hm)
    rw [samplingFactor_succ hrm (Nat.ne_of_gt hm)]
    calc
      1 - samplingFactor r m * (1 - (r : ℝ) / (m : ℝ)) =
          (1 - samplingFactor r m) + samplingFactor r m * ((r : ℝ) / (m : ℝ)) := by
        ring
      _ ≤ (r : ℝ) * ((r : ℝ) - 1) / (2 * (m : ℝ)) + (r : ℝ) / (m : ℝ) :=
        add_le_add hih hterm
      _ = ((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 1) / (2 * (m : ℝ)) := by
        push_cast
        field_simp
        ring

theorem homFreeUpper_le_one (F : Finset (FiniteGraph r)) (m : ℕ) (hr : r ≤ m) :
    homFreeUpper F m ≤ 1 := by
  have hc : (0 : ℝ) < m.choose r := by exact_mod_cast Nat.choose_pos hr
  apply (div_le_one hc).mpr
  exact_mod_cast homFreeMax_le_choose F m

theorem homFreeLower_eq_factor_mul_upper (F : Finset (FiniteGraph r))
    (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    homFreeLower F m = samplingFactor r m * homFreeUpper F m := by
  have hc : (m.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hr)
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold homFreeLower homFreeUpper samplingFactor
  field_simp

theorem homFreeLower_le_density (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) (hm : 0 < m) :
    homFreeLower F m ≤ familyTuranDensity F := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨G, hG, hcard⟩ := exists_homFreeMax F hedges m
  have h := familyTuranDensity_lower_uniform F G hG
  rw [RGraph.oneEdge_homDensity, Fintype.card_fin, hcard] at h
  exact h

theorem density_le_homFreeUpper (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    familyTuranDensity F ≤ homFreeUpper F m := by
  have hclass (G : RGraph (Fin m) r) (hG : familyHomFree F G) :
      (RGraph.oneEdge r).homDensity G ≤ homFreeLower F m := by
    rw [RGraph.oneEdge_homDensity]
    simp only [Fintype.card_fin]
    unfold homFreeLower
    gcongr
    exact_mod_cast edge_card_le_homFreeMax F G hG
  have h := family_samplingFactor_mul_density_le F hedges m hm
    (homFreeLower F m) (homFreeLower_nonneg F m) hclass
  rw [homFreeLower_eq_factor_mul_upper F m hm hr] at h
  exact le_of_mul_le_mul_left h (samplingFactor_pos r m hm hr)

/-- The two explicit rational expressions enclose the ordinary Turán density. -/
theorem homFreeMax_bounds (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    homFreeLower F m ≤ familyTuranDensity F ∧
      familyTuranDensity F ≤ homFreeUpper F m :=
  ⟨homFreeLower_le_density F hedges m hm, density_le_homFreeUpper F hedges m hm hr⟩

/-- The complete enclosing interval has this explicit, family-independent
width. Its proof does not require any nondegeneracy hypothesis on `F`. -/
theorem homFreeMax_interval_width (F : Finset (FiniteGraph r))
    (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    homFreeUpper F m - homFreeLower F m ≤
      (r : ℝ) * ((r : ℝ) - 1) / (2 * (m : ℝ)) := by
  rw [homFreeLower_eq_factor_mul_upper F m hm hr]
  calc
    homFreeUpper F m - samplingFactor r m * homFreeUpper F m =
        homFreeUpper F m * (1 - samplingFactor r m) := by ring
    _ ≤ 1 - samplingFactor r m :=
      mul_le_of_le_one_left (sub_nonneg.mpr (samplingFactor_le_one r m hm))
        (homFreeUpper_le_one F m hr)
    _ ≤ _ := samplingFactor_deficit_bound r m hm hr

/-- In particular the upper endpoint approximates the density with the
same explicit error bound. -/
theorem homFreeUpper_error (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    0 ≤ homFreeUpper F m - familyTuranDensity F ∧
      homFreeUpper F m - familyTuranDensity F ≤
        (r : ℝ) * ((r : ℝ) - 1) / (2 * (m : ℝ)) := by
  obtain ⟨hl, hu⟩ := homFreeMax_bounds F hedges m hm hr
  constructor
  · linarith
  · exact (sub_le_sub_left hl _).trans (homFreeMax_interval_width F m hm hr)

end TuranUniversality
