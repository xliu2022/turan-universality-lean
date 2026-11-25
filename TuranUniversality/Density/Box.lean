module

public import TuranUniversality.Density.Averages
public import TuranUniversality.Selector.CrossIntersecting

@[expose] public section

/-!
# Finite cloning by Jensen's inequality

For any relation on d coordinates, the probability that an independent array
of s samples in each coordinate forms a complete box is at least the original
relation density raised to s^d. This is the quantitative finite cloning lemma
used to pass from ordinary forbidden copies to forbidden homomorphic images.
-/

open scoped BigOperators

namespace TuranUniversality.Density

open Selector

noncomputable def truth (p : Prop) : ℝ := by classical exact if p then 1 else 0

@[simp] theorem truth_true : truth True = 1 := by simp [truth]
@[simp] theorem truth_false : truth False = 0 := by simp [truth]
theorem truth_nonneg (p : Prop) : 0 ≤ truth p := by unfold truth; split <;> norm_num

theorem truth_forall_fin (s : ℕ) (p : Fin s → Prop) :
    truth (∀ j, p j) = ∏ j, truth (p j) := by
  classical
  by_cases h : ∀ j, p j
  · simp [truth, h]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    have hn : ¬ ∀ j, p j := fun h => hj (h j)
    rw [show truth (∀ j, p j) = 0 by simp [truth, hn]]
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [truth, hj])).symm

theorem mean_all_samples [Fintype A] (s : ℕ) (p : A → Prop) :
    mean (fun f : Fin s → A => truth (∀ j, p (f j))) =
      mean (fun a => truth (p a)) ^ s := by
  classical
  simp_rw [truth_forall_fin]
  symm
  simpa [mean] using Finset.expect_pow Finset.univ (fun a => truth (p a)) s

/-- Choose one of s entries in each of d independent coordinate lists. -/
def chooseWord {A : Type*} {s : ℕ} :
    (d : ℕ) → Words (Fin s → A) d → Words (Fin s) d → Words A d
  | 0, _, _ => PUnit.unit
  | d + 1, x, j => (x.1 j.1, chooseWord d x.2 j.2)

def IsBox {A : Type*} {s d : ℕ} (R : Words A d → Prop)
    (x : Words (Fin s → A) d) : Prop :=
  ∀ j, R (chooseWord d x j)

noncomputable def relationDensity {A : Type*} [Fintype A] {d : ℕ}
    (R : Words A d → Prop) : ℝ := mean (fun x => truth (R x))

noncomputable def boxDensity {A : Type*} [Fintype A] (s : ℕ) {d : ℕ}
    (R : Words A d → Prop) : ℝ := mean (fun x : Words (Fin s → A) d => truth (IsBox R x))

theorem relationDensity_nonneg {A : Type*} [Fintype A] {d : ℕ}
    (R : Words A d → Prop) : 0 ≤ relationDensity R :=
  mean_nonneg fun _ => truth_nonneg _

theorem boxDensity_succ {A : Type*} [Fintype A] (s d : ℕ)
    (R : Words A (d + 1) → Prop) :
    boxDensity s R = mean (fun f : Fin s → A =>
      boxDensity s (fun x : Words A d => ∀ j, R (f j, x))) := by
  unfold boxDensity
  rw [mean_prod]
  apply mean_congr
  intro f
  apply mean_congr
  intro x
  congr 1
  apply propext
  simp only [IsBox, chooseWord, Prod.forall]
  exact forall_comm

theorem mean_section_intersection {A : Type*} [Fintype A] (s d : ℕ)
    (R : Words A (d + 1) → Prop) :
    mean (fun f : Fin s → A => relationDensity (fun x : Words A d => ∀ j, R (f j, x))) =
      mean (fun x : Words A d => mean (fun a : A => truth (R (a, x))) ^ s) := by
  unfold relationDensity
  rw [mean_comm]
  apply mean_congr
  intro x
  exact mean_all_samples s (fun a => R (a, x))

/-- The complete-box density bound, proved by finite induction and Jensen. -/
theorem boxDensity_ge_power {A : Type*} [Fintype A] [Nonempty A]
    (s : ℕ) (d : ℕ) (R : Words A d → Prop) :
    relationDensity R ^ (s ^ d) ≤ boxDensity s R := by
  classical
  induction d with
  | zero =>
      have hR : R = fun _ => R PUnit.unit := by funext x; cases x; rfl
      rw [hR]
      simp [relationDensity, boxDensity, IsBox, mean_const]
  | succ d ih =>
      have hr : relationDensity R =
          mean (fun x : Words A d => mean (fun a : A => truth (R (a, x)))) := by
        unfold relationDensity
        rw [mean_prod, mean_comm]
      have hj : relationDensity R ^ s ≤
          mean (fun f : Fin s → A => relationDensity
            (fun x : Words A d => ∀ j, R (f j, x))) := by
        rw [hr, mean_section_intersection]
        exact mean_pow_le _ (fun x => mean_nonneg fun a => truth_nonneg _) s
      calc
        relationDensity R ^ (s ^ (d + 1)) = (relationDensity R ^ s) ^ (s ^ d) := by
          rw [pow_succ, Nat.mul_comm (s ^ d) s, pow_mul]
        _ ≤ (mean (fun f : Fin s → A => relationDensity
            (fun x : Words A d => ∀ j, R (f j, x)))) ^ (s ^ d) :=
          pow_le_pow_left₀ (pow_nonneg (relationDensity_nonneg R) _) hj _
        _ ≤ mean (fun f : Fin s → A => relationDensity
            (fun x : Words A d => ∀ j, R (f j, x)) ^ (s ^ d)) :=
          mean_pow_le _ (fun f => relationDensity_nonneg _) _
        _ ≤ mean (fun f : Fin s → A =>
            boxDensity s (fun x : Words A d => ∀ j, R (f j, x))) :=
          mean_mono fun f => ih (fun x => ∀ j, R (f j, x))
        _ = boxDensity s R := (boxDensity_succ s d R).symm

theorem chooseWord_function {A : Type*} {s d : ℕ}
    (x : Words (Fin s → A) d) (j : Words (Fin s) d) :
    wordsEquivFunction A d (chooseWord d x j) =
      fun i => wordsEquivFunction (Fin s → A) d x i
        (wordsEquivFunction (Fin s) d j i) := by
  induction d with
  | zero => funext i; exact Fin.elim0 i
  | succ d ih =>
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · rfl
      · exact congrFun (ih x.2 j.2) k

/-- The cloning bound in the conventional function representation of finite
words, ready to use with hypergraph vertex sets `Fin d`. -/
theorem box_power_function {A : Type*} [Fintype A] [Nonempty A]
    (s d : ℕ) (R : (Fin d → A) → Prop) :
    mean (fun f : Fin d → A => truth (R f)) ^ (s ^ d) ≤
      mean (fun x : Fin d → Fin s → A => truth
        (∀ c : Fin d → Fin s, R (fun i => x i (c i)))) := by
  classical
  let Rw : Words A d → Prop := fun w => R (wordsEquivFunction A d w)
  have hrel : relationDensity Rw = mean (fun f : Fin d → A => truth (R f)) := by
    exact Fintype.expect_equiv (wordsEquivFunction A d) _ _ (fun _ => rfl)
  have hbox : boxDensity s Rw =
      mean (fun x : Fin d → Fin s → A => truth
        (∀ c : Fin d → Fin s, R (fun i => x i (c i)))) := by
    apply Fintype.expect_equiv (wordsEquivFunction (Fin s → A) d)
    intro x
    congr 1
    apply propext
    unfold IsBox Rw
    simp_rw [chooseWord_function]
    constructor
    · intro h c
      simpa only [Equiv.apply_symm_apply] using
        h ((wordsEquivFunction (Fin s) d).symm c)
    · intro h j
      exact h (wordsEquivFunction (Fin s) d j)
  simpa only [hrel, hbox] using boxDensity_ge_power s d Rw

end TuranUniversality.Density
