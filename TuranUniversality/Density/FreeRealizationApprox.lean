module

public import TuranUniversality.Density.GeneralSamplingEvents
public import TuranUniversality.Density.SetFamilyVariational

@[expose] public section

/-! # Finite-coordinate free approximation of a dense limit profile

Profiles are indexed by every labelled finite test graph. The dense-limit
space is the closure of the profiles of nonempty finite hosts. Requiring a
nonempty host is the usual dense-limit convention and avoids the exceptional
zero-denominator profile of an empty target.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.SetFamily

variable {r : ℕ}
noncomputable section

abbrev Profile (r : ℕ) := FiniteGraph r → ℝ

def profile (G : FiniteGraph r) : Profile r := fun A => A.2.homDensity G.2

def finiteProfiles (r : ℕ) : Set (Profile r) :=
  {W | ∃ G : FiniteGraph r, 0 < G.1 ∧ W = profile G}

def IsLimitProfile (W : Profile r) : Prop := W ∈ closure (finiteProfiles r)

theorem testBudget_tendsto_zero (tests : Finset (FiniteGraph r)) (ε : ℝ) :
    Tendsto (fun m : ℕ => ∑ A ∈ tests, 6 * (A.1 : ℝ) ^ 2 / (m * ε ^ 2))
      atTop (𝓝 0) := by
  have hz : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht (A : FiniteGraph r) :
      Tendsto (fun m : ℕ => 6 * (A.1 : ℝ) ^ 2 / (m * ε ^ 2)) atTop (𝓝 0) := by
    have h := hz.const_mul (6 * (A.1 : ℝ) ^ 2 / ε ^ 2)
    convert h using 1
    · funext m
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum tests (fun A _ => ht A)

theorem exists_large_small_testBudget (tests : Finset (FiniteGraph r)) (ε : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧
      (∑ A ∈ tests, 6 * (A.1 : ℝ) ^ 2 / (m * ε ^ 2)) < 1 / 2 := by
  have h := (testBudget_tendsto_zero tests ε).eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
  have he : ∀ᶠ m : ℕ in atTop, N ≤ m ∧ 0 < m ∧
      (∑ A ∈ tests, 6 * (A.1 : ℝ) ^ 2 / (m * ε ^ 2)) < 1 / 2 := by
    filter_upwards [h, eventually_ge_atTop N, eventually_ge_atTop 1] with m hb hN hp
    exact ⟨hN, by omega, hb⟩
  exact he.exists

/-- Every finite list of coordinates of a vanishing limit profile can be
approximated by an actual free graph of arbitrarily large order. -/
theorem exists_free_close_of_vanishing (F : Set (FiniteGraph r)) (W : Profile r)
    (hW : IsLimitProfile W) (hzero : ∀ A ∈ F, W A = 0)
    (tests : Finset (FiniteGraph r)) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ G : FiniteGraph r, N ≤ G.1 ∧ 0 < G.1 ∧ Free F G.2 ∧
      ∀ A ∈ tests, |profile G A - W A| < ε := by
  classical
  obtain ⟨m, hmN, hm, htest⟩ := exists_large_small_testBudget tests (ε / 2) N
  let E := truncate F m
  let O₁ : Set (Profile r) := {p | ∀ A ∈ tests, |p A - W A| < ε / 2}
  let O₂ : Set (Profile r) := {p | (∑ A ∈ E, (m : ℝ) ^ A.1 * p A) < 1 / 2}
  have hO₁ : IsOpen O₁ := by
    have h : IsOpen (⋂ A ∈ tests, {p : Profile r | |p A - W A| < ε / 2}) :=
      isOpen_biInter_finset (fun A _ =>
        isOpen_lt ((continuous_apply A).sub continuous_const).abs continuous_const)
    convert h using 1
    ext p
    simp [O₁]
  have hO₂ : IsOpen O₂ := by
    apply isOpen_lt _ continuous_const
    fun_prop
  have hW₁ : W ∈ O₁ := by
    intro A hA
    simp only [sub_self, abs_zero]
    positivity
  have hW₂ : W ∈ O₂ := by
    have hz : (∑ A ∈ E, (m : ℝ) ^ A.1 * W A) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      rw [hzero A (truncate_subset F m hA), mul_zero]
    change (∑ A ∈ E, (m : ℝ) ^ A.1 * W A) < 1 / 2
    rw [hz]
    norm_num
  obtain ⟨p, hpO, hpfinite⟩ := (mem_closure_iff.mp hW) (O₁ ∩ O₂)
    (hO₁.inter hO₂) ⟨hW₁, hW₂⟩
  obtain ⟨G, hGpos, rfl⟩ := hpfinite
  let : Nonempty (Fin G.1) := ⟨⟨0, hGpos⟩⟩
  have hbudget : (∑ A ∈ truncate F m, (m : ℝ) ^ A.1 * A.2.homDensity G.2) +
      (∑ A ∈ tests, 6 * (A.1 : ℝ) ^ 2 / (m * (ε / 2) ^ 2)) < 1 := by
    have hforbid := hpO.2
    change (∑ A ∈ truncate F m, (m : ℝ) ^ A.1 * A.2.homDensity G.2) < 1 / 2 at hforbid
    linarith
  obtain ⟨f, hfree, hclose⟩ := exists_free_sample_close F tests G.2 m hm (ε / 2)
    (by positivity) hbudget
  refine ⟨⟨m, G.2.sample m f⟩, hmN, hm, hfree, ?_⟩
  intro A hA
  calc
    |profile ⟨m, G.2.sample m f⟩ A - W A| ≤
        |A.2.homDensity (G.2.sample m f) - A.2.homDensity G.2| +
        |profile G A - W A| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hclose A hA) (hpO.1 A hA)
    _ = ε := by ring

end
end TuranUniversality.SetFamily
