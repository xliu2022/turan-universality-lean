module

public import TuranUniversality.Construction.Parameters
public import TuranUniversality.Density.GuardSplit

@[expose] public section

/-! # The fixed guard parameters lie strictly below the rational baseline -/

namespace TuranUniversality.Construction

open Weighted

theorem guard_cubic_gap (q k δ a u : ℝ) (hq : 0 < q) (hk : 100 ≤ k)
    (hkq : k ≤ 24 * q / 25) (hδ : 6000000 / q ≤ δ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hsum : a + u = 1) :
    6 * coeffA k * a ^ 3 + 3 * (1 - 1 / k) * a ^ 2 * u + 3 * a * u ^ 2 +
      (1 - δ) * u ^ 3 < 1 - 3 / q := by
  have hk0 : 0 < k := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hδ0 : 0 ≤ δ := (div_nonneg (by norm_num) hq.le).trans hδ
  have hiden : 6 * coeffA k * a ^ 3 + 3 * (1 - 1 / k) * a ^ 2 * u + 3 * a * u ^ 2 +
      (1 - δ) * u ^ 3 = 1 - (3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2) - δ * u ^ 3 := by
    have hueq : u = 1 - a := by linarith
    rw [hueq]
    unfold coeffA
    field_simp
    ring
  rw [hiden]
  have hid : 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 = (3 * k - 2 * a) * a ^ 2 / k ^ 2 := by
    field_simp
  have hnonneg : 0 ≤ 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 := by
    rw [hid]
    exact div_nonneg (mul_nonneg (by linarith) (sq_nonneg a)) (sq_nonneg k)
  by_cases huLarge : 1 / 100 ≤ u
  · have hcube : 1 / 1000000 ≤ u ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 100) huLarge 3
      norm_num at h
      exact h
    have hmul := mul_le_mul_of_nonneg_left hcube hδ0
    have hlow : 6 / q ≤ δ * u ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hδ (by norm_num : (0 : ℝ) ≤ 1 / 1000000)
      have heq : 6000000 / q * (1 / 1000000) = 6 / q := by ring
      rw [heq] at h
      exact h.trans hmul
    have hgap : 3 / q < 6 / q := div_lt_div_of_pos_right (by norm_num) hq
    linarith
  · have ha99 : 99 / 100 < a := by linarith
    have hfactor : (149 / 50 : ℝ) * k ≤ 3 * k - 2 * a := by linarith
    have hfactorMul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg a)
    have hAlow : (149 / 50 : ℝ) * a ^ 2 / k ≤ 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 := by
      rw [hid]
      apply (div_le_div_iff₀ hk0 (sq_pos_of_pos hk0)).mpr
      have hmul := mul_le_mul_of_nonneg_right hfactorMul hk0.le
      nlinarith only [hmul]
    have haSq : (99 / 100 : ℝ) ^ 2 < a ^ 2 := by nlinarith
    have hnum : (29 / 10 : ℝ) < (149 / 50 : ℝ) * a ^ 2 := by nlinarith
    have hfrac : (29 / 10 : ℝ) / k < 3 * a ^ 2 / k - 2 * a ^ 3 / k ^ 2 :=
      (div_lt_div_of_pos_right hnum hk0).trans_le hAlow
    have hqfrac : 3 / q < (29 / 10 : ℝ) / k := by
      apply (div_lt_div_iff₀ hq hk0).mpr
      nlinarith
    have hdu : 0 ≤ δ * u ^ 3 := mul_nonneg hδ0 (pow_nonneg hu 3)
    linarith

def guardProfiles (A : ℕ) : ℕ := 8 * codeCount A
def guardCliqueSize (A : ℕ) : ℕ := 8 * guardProfiles A
def guardCopies (q t : ℕ) : ℕ := 24 * q / (25 * t)

theorem guard_sizes (q t : ℕ) (ht : 4 ≤ t) (hq : 1000000 * t ^ 3 ≤ q) :
    2 ≤ guardCopies q t ∧ 100 ≤ t * (guardCopies q t - 1) ∧
      19 * (q : ℝ) / 20 < (t * (guardCopies q t - 1) : ℕ) ∧
      t * (guardCopies q t - 1) < t * guardCopies q t ∧
      (t * guardCopies q t : ℕ) ≤ 24 * (q : ℝ) / 25 ∧
      1048576 ≤ t * guardCopies q t := by
  let s := guardCopies q t
  have ht0 : 0 < t := by omega
  have hd : 0 < 25 * t := by omega
  have htCube : t ≤ t ^ 3 := by
    have hsq : 1 ≤ t ^ 2 := Nat.succ_le_of_lt (pow_pos ht0 2)
    nlinarith [Nat.mul_le_mul_left t hsq]
  have htCube64 : 64 ≤ t ^ 3 := by
    have h := Nat.pow_le_pow_left ht 3
    norm_num at h
    exact h
  have hqmin : 64000000 ≤ q := by omega
  have hqt : 1000000 * t ≤ q := by nlinarith
  have hs : 2 ≤ s := by
    dsimp [s, guardCopies]
    apply (Nat.le_div_iff_mul_le hd).mpr
    nlinarith
  have hlo : 25 * t * s ≤ 24 * q := by
    have h := Nat.div_mul_le_self (24 * q) (25 * t)
    change s * (25 * t) ≤ 24 * q at h
    nlinarith
  have hhi : 24 * q < 25 * t * (s + 1) := by
    have hm := Nat.mod_add_div (24 * q) (25 * t)
    have hr := Nat.mod_lt (24 * q) hd
    change 24 * q % (25 * t) + (25 * t) * s = 24 * q at hm
    nlinarith
  have hkt : t * (s - 1) + t = t * s := by
    have h := Nat.sub_add_cancel (show 1 ≤ s by omega)
    nlinarith [congrArg (t * ·) h]
  have hkq : 19 * (q : ℝ) / 20 < (t * (s - 1) : ℕ) := by
    have hhi' : 24 * (q : ℝ) < 25 * (t : ℝ) * ((s : ℝ) + 1) := by exact_mod_cast hhi
    have hkt' : (t * (s - 1) : ℕ) + (t : ℝ) = (t : ℝ) * s := by exact_mod_cast hkt
    have hqt' : 1000000 * (t : ℝ) ≤ q := by exact_mod_cast hqt
    have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  have hk100 : 100 ≤ t * (s - 1) := by
    have hqmin' : (64000000 : ℝ) ≤ q := by exact_mod_cast hqmin
    have h : (100 : ℝ) ≤ (t * (s - 1) : ℕ) := by linarith
    exact_mod_cast h
  have hn : 1048576 ≤ t * s := by
    have hqmin' : (64000000 : ℝ) ≤ q := by exact_mod_cast hqmin
    have h : (1048576 : ℝ) ≤ (t * (s - 1) : ℕ) := by linarith
    have h' : 1048576 ≤ t * (s - 1) := by exact_mod_cast h
    omega
  refine ⟨hs, hk100, hkq, ?_, ?_, hn⟩
  · change t * (s - 1) < t * s
    omega
  · have hlo' : 25 * ((t * s : ℕ) : ℝ) ≤ 24 * (q : ℝ) := by
      exact_mod_cast (show 25 * (t * s) ≤ 24 * q by simpa [Nat.mul_assoc] using hlo)
    linarith

theorem guardCliqueSize_ge (A : ℕ) : 4 ≤ guardCliqueSize A := by
  have := codeCount_pos A
  unfold guardCliqueSize guardProfiles
  omega

theorem rootNumber_guard_large (A : ℕ) :
    1000000 * guardCliqueSize A ^ 3 ≤ rootNumber (chosenParameter A) := by
  let m : ℝ := physicalCount (chosenParameter A)
  have hm : 40000000000000000 ≤ m := by
    dsimp [m, physicalCount, chosenParameter]
    push_cast
    linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hm0 : 0 ≤ m := by linarith
  have ht0 : (0 : ℝ) ≤ guardCliqueSize A := Nat.cast_nonneg _
  have ht : (guardCliqueSize A : ℝ) ≤ 128 * m := by
    have h := codeCount_le A
    have h' : (codeCount A : ℝ) ≤ 2 * m := by dsimp [m]; exact_mod_cast h
    dsimp [guardCliqueSize, guardProfiles]
    push_cast
    linarith
  have ht3 := pow_le_pow_left₀ ht0 ht 3
  have hq := (rootNumber_bounds (chosenParameter A)).1
  change m ^ 4 / 12 ≤ (rootNumber (chosenParameter A) : ℝ) at hq
  have hmul := mul_le_mul_of_nonneg_right (show (25165824000000 : ℝ) ≤ m by linarith)
    (pow_nonneg hm0 3)
  have hreal : 1000000 * (guardCliqueSize A : ℝ) ^ 3 ≤ rootNumber (chosenParameter A) := by
    nlinarith [ht3, hmul]
  exact_mod_cast hreal

theorem guard_free_strict_bound {V : Type*} [Fintype V] [DecidableEq V]
    (q t : ℕ) (ht : 4 ≤ t) (hq : 1000000 * t ^ 3 ≤ q)
    (G : RGraph V 3)
    (hfree : ¬ ∃ f, (RGraph.cliquePacking (guardCopies q t) t).IsEmbedding G f)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    6 * G.edgePolynomial x < 1 - 3 / (q : ℝ) := by
  obtain ⟨hs, hk, hklow, hkn, hnup, hnlarge⟩ := guard_sizes q t ht hq
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast (show 0 < q from lt_of_lt_of_le (by positivity) hq)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hδ : 6000000 / (q : ℝ) ≤ 1 / (t.choose 3 : ℝ) := by
    apply le_trans (b := 6 / (t : ℝ) ^ 3)
    · apply (div_le_div_iff₀ hq0 (pow_pos ht0 3)).mpr
      have hq' : 1000000 * (t : ℝ) ^ 3 ≤ q := by exact_mod_cast hq
      linarith
    · exact RGraph.clique_deficit_lower (by omega)
  obtain ⟨a, u, ha, hu, hsum, hbound⟩ := G.guard_polynomial_split (by omega : 3 ≤ t)
    (by omega : 12 ≤ t * (guardCopies q t - 1)) hfree x hx
  apply hbound.trans_lt
  apply guard_cubic_gap (q : ℝ) (t * (guardCopies q t - 1) : ℕ) (1 / (t.choose 3 : ℝ)) a u
    hq0 (by exact_mod_cast hk) ?_ hδ ha hu hsum
  have hkn' : ((t * (guardCopies q t - 1) : ℕ) : ℝ) < (t * guardCopies q t : ℕ) := by
    exact_mod_cast hkn
  linarith

def fixedGuard (A : ℕ) : RGraph
    (Fin (guardCopies (rootNumber (chosenParameter A)) (guardCliqueSize A)) ×
      Fin (guardCliqueSize A)) 3 :=
  RGraph.cliquePacking (guardCopies (rootNumber (chosenParameter A)) (guardCliqueSize A))
    (guardCliqueSize A)

theorem guard_free_below_threshold {V : Type*} [Fintype V] [DecidableEq V]
    (A : ℕ) (G : RGraph V 3) (hfree : ¬ ∃ f, (fixedGuard A).IsEmbedding G f)
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    6 * G.edgePolynomial x < (threshold A : ℝ) := by
  have hb := guard_free_strict_bound (rootNumber (chosenParameter A)) (guardCliqueSize A)
    (guardCliqueSize_ge A) (rootNumber_guard_large A) G hfree x hx
  have hm : (30 : ℝ) ≤ physicalCount (chosenParameter A) := by
    exact_mod_cast physicalCount_ge (chosenParameter A)
  have hbase := (baselineMax_strict_bounds _ hm).1
  rw [← rootNumber_cast] at hbase
  have hq0 : (0 : ℝ) < rootNumber (chosenParameter A) := by
    have h := rootNumber_large (chosenParameter A)
    exact_mod_cast (show 0 < rootNumber (chosenParameter A) by
      have := physicalCount_ge (chosenParameter A); omega)
  have hlow : 1 - 3 / (rootNumber (chosenParameter A) : ℝ) <
      6 * coeffA (rootNumber (chosenParameter A)) := by
    have hid : 6 * coeffA (rootNumber (chosenParameter A)) -
        (1 - 3 / (rootNumber (chosenParameter A) : ℝ)) =
        2 / (rootNumber (chosenParameter A) : ℝ) ^ 2 := by
      unfold coeffA
      field_simp
      ring
    have hpos : 0 < 2 / (rootNumber (chosenParameter A) : ℝ) ^ 2 := by positivity
    linarith
  rw [threshold_cast]
  linarith

end TuranUniversality.Construction
