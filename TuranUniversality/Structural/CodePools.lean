module

public import TuranUniversality.Structural.CodeAllocation
public import TuranUniversality.Structural.RecordPayoff
public import Mathlib.Data.Nat.Log

@[expose] public section

/-! # The seven actual code-word pools of Section 8

The width is exactly `2 + 2 * ceil(log₂(1127*q))`, formalized with `Nat.clog`.
The neutral pool consists of the prefix path followed by its allocated
lexicographic interval of fixed words. The other six labels receive the next
disjoint intervals. Every pool has exactly the corresponding integer payoff.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.CodePools

open Cube

def exponent (q : ℕ) : ℕ := Nat.clog 2 (1127 * q)
def blockCount (q : ℕ) : ℕ := 2 + 2 * exponent q
def background (q : ℕ) : ℕ := 160 * q
def neutralLabel : Label := .inl 0

def poolSize (p q : ℕ) : Label → ℕ
  | .inl j => if j = 3 then 160 * q - p else if j = 4 then 156 * q else 160 * q
  | .inr _ => 161 * q - p

theorem poolSize_bounds (p q : ℕ) (hpq : p ≤ q) (l : Label) :
    156 * q ≤ poolSize p q l ∧ poolSize p q l ≤ 161 * q := by
  cases l with
  | inl j => fin_cases j <;> norm_num [poolSize] <;> omega
  | inr a => dsimp [poolSize]; omega

theorem poolSize_cast (p q : ℕ) (hpq : p ≤ q) (l : Label) :
    (poolSize p q l : ℝ) = Label.payoff (p : ℝ) (q : ℝ) l := by
  have h160 : p ≤ 160 * q := by omega
  have h161 : p ≤ 161 * q := by omega
  cases l with
  | inl j =>
    fin_cases j <;>
      norm_num [poolSize, Label.payoff, Label.correction, Nat.cast_sub h160] <;> ring
  | inr a =>
    simp only [poolSize, Label.payoff, Label.correction, Nat.cast_sub h161,
      Nat.cast_mul, Nat.cast_ofNat]
    ring

@[simp] theorem poolSize_neutral (p q : ℕ) : poolSize p q neutralLabel = background q := rfl

theorem capacity (q : ℕ) : 1127 * q ≤ 2 ^ exponent q :=
  Nat.le_pow_clog (by decide) _

theorem exponent_pos (q : ℕ) (hq : 0 < q) : 1 ≤ exponent q := by
  have h : 0 < Nat.clog 2 (1127 * q) :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by norm_num; omega)
  exact h

theorem linear_le_power (q : ℕ) (hq : 0 < q) : 1127 * q ≤ 2 ^ (q + 10) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      1127 * (n + 1 + 1) ≤ 2 * (1127 * (n + 1)) := by omega
      _ ≤ 2 * 2 ^ (n + 1 + 10) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = 2 ^ (n + 1 + 1 + 10) := by
        rw [show n + 1 + 1 + 10 = (n + 1 + 10) + 1 by omega, pow_succ]
        ring

theorem blockCount_path_fits (q : ℕ) (hq : 0 < q) : blockCount q + 1 ≤ background q := by
  have h := Nat.clog_le_of_le_pow (linear_le_power q hq)
  dsimp [blockCount, background, exponent]
  omega

def labelEquiv : Fin 7 ≃ Label where
  toFun i := if h : i.val < 5 then .inl ⟨i.val, h⟩ else .inr (decide (i.val = 6))
  invFun
    | .inl j => ⟨j.val, by omega⟩
    | .inr false => 5
    | .inr true => 6
  left_inv i := by fin_cases i <;> decide
  right_inv l := by
    cases l with
    | inl j => fin_cases j <;> decide
    | inr a => cases a <;> decide

@[simp] theorem labelEquiv_zero : labelEquiv 0 = neutralLabel := rfl
@[simp] theorem labelEquiv_symm_neutral : labelEquiv.symm neutralLabel = 0 := rfl

def demand (p q : ℕ) (i : Fin 7) : ℕ :=
  if i = 0 then background q - (blockCount q + 1) else poolSize p q (labelEquiv i)

theorem demand_le (p q : ℕ) (hpq : p ≤ q) (i : Fin 7) : demand p q i ≤ 161 * q := by
  by_cases hi : i = 0
  · simp only [demand, hi, ite_true, background]
    omega
  · simpa only [demand, hi, ite_false] using (poolSize_bounds p q hpq (labelEquiv i)).2

theorem demand_capacity (p q : ℕ) (hpq : p ≤ q) : (∑ i, demand p q i) ≤ 2 ^ exponent q := by
  calc
    _ ≤ ∑ _i : Fin 7, 161 * q := Finset.sum_le_sum (fun i _ => demand_le p q hpq i)
    _ = 1127 * q := by simp; omega
    _ ≤ _ := capacity q

noncomputable def extra (p q : ℕ) (hpq : p ≤ q) (i : Fin 7) : Finset (Word (blockCount q)) :=
  allocatedWords (exponent q) (demand p q) (demand_capacity p q hpq) i

theorem extra_card (p q : ℕ) (hpq : p ≤ q) (i : Fin 7) :
    (extra p q hpq i).card = demand p q i :=
  allocatedWords_card _ _ _ _

theorem extra_subset (p q : ℕ) (hpq : p ≤ q) (i : Fin 7) :
    extra p q hpq i ⊆ fixedStartWords (exponent q) :=
  allocatedWords_subset _ _ _ _

theorem extra_disjoint (p q : ℕ) (hpq : p ≤ q) {i j : Fin 7} (hij : i ≠ j) :
    Disjoint (extra p q hpq i) (extra p q hpq j) :=
  allocatedWords_disjoint _ _ _ hij

theorem extra_disjoint_prefixPath (p q : ℕ) (hpq : p ≤ q) (i : Fin 7) :
    Disjoint (extra p q hpq i) (prefixPath (blockCount q)) :=
  allocatedWords_disjoint_prefixPath _ _ _ _

noncomputable def pool (p q : ℕ) (hpq : p ≤ q) (l : Label) : Finset (Word (blockCount q)) :=
  if l = neutralLabel then prefixPath (blockCount q) ∪ extra p q hpq (labelEquiv.symm l)
  else extra p q hpq (labelEquiv.symm l)

theorem mem_pool (p q : ℕ) (hpq : p ≤ q) (l : Label) (w : Word (blockCount q)) :
    w ∈ pool p q hpq l ↔ (l = neutralLabel ∧ w ∈ prefixPath (blockCount q)) ∨
      w ∈ extra p q hpq (labelEquiv.symm l) := by
  by_cases h : l = neutralLabel <;> simp [pool, h]

theorem pool_card (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (l : Label) :
    (pool p q hpq l).card = poolSize p q l := by
  by_cases hl : l = neutralLabel
  · subst l
    rw [pool, if_pos rfl, labelEquiv_symm_neutral,
      Finset.card_union_of_disjoint (extra_disjoint_prefixPath p q hpq 0).symm,
      prefixPath_card, extra_card]
    simp only [demand, ite_true, poolSize_neutral]
    have hpath := blockCount_path_fits q hq
    omega
  · have hi : labelEquiv.symm l ≠ 0 := by
      intro h
      have he := congrArg labelEquiv h
      exact hl (by simpa using he)
    rw [pool, if_neg hl, extra_card, demand, if_neg hi, Equiv.apply_symm_apply]

theorem pool_card_cast (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (l : Label) :
    ((pool p q hpq l).card : ℝ) = Label.payoff (p : ℝ) (q : ℝ) l := by
  rw [pool_card p q hpq hq, poolSize_cast p q hpq]

theorem pools_disjoint (p q : ℕ) (hpq : p ≤ q) {l k : Label} (hlk : l ≠ k) :
    Disjoint (pool p q hpq l) (pool p q hpq k) := by
  apply Finset.disjoint_left.mpr
  intro w hwl hwk
  have hij : labelEquiv.symm l ≠ labelEquiv.symm k := fun h => hlk (labelEquiv.symm.injective h)
  rcases (mem_pool p q hpq l w).mp hwl with ⟨hl, hwP⟩ | hwE
  · rcases (mem_pool p q hpq k w).mp hwk with ⟨hk, _⟩ | hwE
    · exact hlk (hl.trans hk.symm)
    · exact (Finset.disjoint_left.mp (extra_disjoint_prefixPath p q hpq _)) hwE hwP
  · rcases (mem_pool p q hpq k w).mp hwk with ⟨_, hwP⟩ | hwE'
    · exact (Finset.disjoint_left.mp (extra_disjoint_prefixPath p q hpq _)) hwE hwP
    · exact (Finset.disjoint_left.mp (extra_disjoint p q hpq hij)) hwE hwE'

theorem neutral_pool (p q : ℕ) (hpq : p ≤ q) :
    pool p q hpq neutralLabel = prefixPath (blockCount q) ∪ extra p q hpq 0 := by
  simp [pool]

theorem prefixPath_subset_neutral (p q : ℕ) (hpq : p ≤ q) :
    prefixPath (blockCount q) ⊆ pool p q hpq neutralLabel := by
  rw [neutral_pool]
  exact Finset.subset_union_left

theorem nonneutral_subset_fixedStartWords (p q : ℕ) (hpq : p ≤ q)
    {l : Label} (hl : l ≠ neutralLabel) :
    pool p q hpq l ⊆ fixedStartWords (exponent q) := by
  rw [pool, if_neg hl]
  exact extra_subset p q hpq _

theorem neutral_extras_isolated (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) :
    IsolatedExtras (blockCount q) (extra p q hpq 0) :=
  isolatedExtras_of_subset_fixedStartWords (exponent q) (exponent_pos q hq) _
    (extra_subset p q hpq 0)

theorem reverseComplement_mem_pool (p q : ℕ) (hpq : p ≤ q) (l : Label)
    {w : Word (blockCount q)} (hw : w ∈ pool p q hpq l) :
    reverseComplement w ∈ pool p q hpq l := by
  rcases (mem_pool p q hpq l w).mp hw with ⟨hl, hwP⟩ | hwE
  · exact (mem_pool p q hpq l _).mpr (Or.inl ⟨hl, reverseComplement_mem_prefixPath hwP⟩)
  · have hfix := (mem_fixedStartWords _ _).mp (extra_subset p q hpq _ hwE) |>.1
    exact (congrArg (fun v : Word (blockCount q) => v ∈ pool p q hpq l) hfix).mpr
      ((mem_pool p q hpq l w).mpr (Or.inr hwE))

theorem blockCount_ge_four (q : ℕ) (hq : 0 < q) : 4 ≤ blockCount q := by
  have h := exponent_pos q hq
  dsimp [blockCount]
  omega

theorem pool_nonempty (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (l : Label) :
    (pool p q hpq l).Nonempty := by
  apply Finset.card_pos.mp
  rw [pool_card p q hpq hq]
  have h := (poolSize_bounds p q hpq l).1
  omega

theorem nonneutral_word_fixed (p q : ℕ) (hpq : p ≤ q) {l : Label}
    (hl : l ≠ neutralLabel) {w : Word (blockCount q)} (hw : w ∈ pool p q hpq l) :
    reverseComplement w = w ∧ firstIndex (exponent q) ∉ w :=
  (mem_fixedStartWords _ _).mp (nonneutral_subset_fixedStartWords p q hpq hl hw)

theorem reverseComplement_pool (p q : ℕ) (hpq : p ≤ q) (l : Label) :
    (pool p q hpq l).image reverseComplement = pool p q hpq l := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact reverseComplement_mem_pool p q hpq l hv
  · intro hw
    exact Finset.mem_image.mpr ⟨reverseComplement w,
      reverseComplement_mem_pool p q hpq l hw, reverseComplement_reverseComplement w⟩

end TuranUniversality.Structural.CodePools
