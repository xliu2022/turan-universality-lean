module

public import TuranUniversality.Weighted.Baseline

/-! # Explicit integer clone sizes for the lower witnesses

There are `q` roots and `m * N` data vertices, with `N` vertices in each
physical type. The baseline uses `N = 1`; the marked construction uses three
copies of the closed computation and hence `N = 3 * historyArea`.
-/

@[expose] public section

namespace TuranUniversality.Weighted

def kappaNumerator (m : ℕ) : ℕ := (m - 2) * (m + 1)

def kappaDenominator (m : ℕ) : ℕ := 2 * (m - 1)

def rootClones (m N : ℕ) : ℕ := m * N * kappaDenominator m

def dataClones (m : ℕ) : ℕ := kappaNumerator m

def totalClones (q m N : ℕ) : ℕ := q * rootClones m N + (m * N) * dataClones m

def rootWeightRat (q m N : ℕ) : ℚ := (rootClones m N : ℚ) / totalClones q m N

def dataWeightRat (q m N : ℕ) : ℚ := (dataClones m : ℚ) / totalClones q m N

theorem kappaNumerator_pos (m : ℕ) (hm : 3 ≤ m) : 0 < kappaNumerator m := by
  unfold kappaNumerator
  exact Nat.mul_pos (by omega) (by omega)

theorem kappaDenominator_pos (m : ℕ) (hm : 3 ≤ m) : 0 < kappaDenominator m := by
  unfold kappaDenominator
  exact Nat.mul_pos (by omega) (by omega)

theorem rootClones_pos (m N : ℕ) (hm : 3 ≤ m) (hN : 0 < N) : 0 < rootClones m N := by
  unfold rootClones
  exact Nat.mul_pos (Nat.mul_pos (by omega) hN) (kappaDenominator_pos m hm)

theorem totalClones_pos (q m N : ℕ) (hq : 0 < q) (hm : 3 ≤ m) (hN : 0 < N) :
    0 < totalClones q m N := by
  unfold totalClones
  exact Nat.add_pos_left (Nat.mul_pos hq (rootClones_pos m N hm hN)) _

theorem totalClones_factor (q m N : ℕ) :
    totalClones q m N = m * N * (q * kappaDenominator m + kappaNumerator m) := by
  unfold totalClones rootClones dataClones
  ring

theorem kappa_integer_ratio (m : ℕ) (hm : 3 ≤ m) :
    kappa (m : ℝ) = (kappaNumerator m : ℝ) / kappaDenominator m := by
  have hm1 : (1 : ℕ) ≤ m := by omega
  have hm2 : (2 : ℕ) ≤ m := by omega
  have hmr : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [kappa_factorization (m : ℝ) (by linarith)]
  simp only [kappaNumerator, kappaDenominator, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_sub hm1, Nat.cast_sub hm2]

theorem root_clone_weight (q m N : ℕ) (hq : 0 < q) (hm : 3 ≤ m) (hN : 0 < N) :
    (rootClones m N : ℝ) / totalClones q m N =
      (1 - criticalMass (m : ℝ) (q : ℝ)) / (q : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hB : (kappaDenominator m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (kappaDenominator_pos m hm))
  have hsum : (q : ℝ) * (kappaDenominator m : ℝ) + (kappaNumerator m : ℝ) ≠ 0 := by
    have hqp : (0 : ℝ) < (q : ℝ) := by positivity
    have hBp : (0 : ℝ) < (kappaDenominator m : ℝ) := by exact_mod_cast kappaDenominator_pos m hm
    have hAp : (0 : ℝ) < (kappaNumerator m : ℝ) := by exact_mod_cast kappaNumerator_pos m hm
    positivity
  rw [totalClones_factor]
  unfold rootClones criticalMass
  rw [kappa_integer_ratio m hm]
  push_cast
  field_simp
  ring

theorem data_clone_weight (q m N : ℕ) (hq : 0 < q) (hm : 3 ≤ m) (hN : 0 < N) :
    (dataClones m : ℝ) / totalClones q m N =
      criticalMass (m : ℝ) (q : ℝ) / ((m * N : ℕ) : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hB : (kappaDenominator m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (kappaDenominator_pos m hm))
  have hsum : (q : ℝ) * (kappaDenominator m : ℝ) + (kappaNumerator m : ℝ) ≠ 0 := by
    have hqp : (0 : ℝ) < (q : ℝ) := by positivity
    have hBp : (0 : ℝ) < (kappaDenominator m : ℝ) := by exact_mod_cast kappaDenominator_pos m hm
    have hAp : (0 : ℝ) < (kappaNumerator m : ℝ) := by exact_mod_cast kappaNumerator_pos m hm
    positivity
  rw [totalClones_factor]
  unfold dataClones criticalMass
  rw [kappa_integer_ratio m hm]
  push_cast
  field_simp

theorem rootWeightRat_cast (q m N : ℕ) (hq : 0 < q) (hm : 3 ≤ m) (hN : 0 < N) :
    (rootWeightRat q m N : ℝ) = (1 - criticalMass (m : ℝ) (q : ℝ)) / (q : ℝ) := by
  unfold rootWeightRat
  push_cast
  exact root_clone_weight q m N hq hm hN

theorem dataWeightRat_cast (q m N : ℕ) (hq : 0 < q) (hm : 3 ≤ m) (hN : 0 < N) :
    (dataWeightRat q m N : ℝ) = criticalMass (m : ℝ) (q : ℝ) / ((m * N : ℕ) : ℝ) := by
  unfold dataWeightRat
  push_cast
  simpa only [Nat.cast_mul] using data_clone_weight q m N hq hm hN

theorem clone_weight_normalization (q m N : ℕ) (hq : 0 < q) (hm : 3 ≤ m) (hN : 0 < N) :
    (q : ℚ) * rootWeightRat q m N + ((m * N : ℕ) : ℚ) * dataWeightRat q m N = 1 := by
  have htotal : (totalClones q m N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (totalClones_pos q m N hq hm hN))
  unfold rootWeightRat dataWeightRat
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  have hnum : (q : ℚ) * (rootClones m N : ℚ) + ((m * N : ℕ) : ℚ) * (dataClones m : ℚ) =
      (totalClones q m N : ℚ) := by simp [totalClones]
  rw [hnum, div_self htotal]

end TuranUniversality.Weighted
