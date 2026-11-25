module

public import TuranUniversality.Density.GeneralSampling
public import TuranUniversality.Density.SetFamilyBasic

@[expose] public section

/-! # Finite sampling events for free realization

The union bound and a second-moment bound control forbidden embedded copies
and finitely many homomorphism-density coordinates in one common sample.
-/

open scoped BigOperators

namespace TuranUniversality.Density

open Selector

variable {A I : Type*} [Fintype A]

theorem mean_truth_exists_finset_le (s : Finset I) (P : I → A → Prop) :
    mean (fun a => truth (∃ i ∈ s, P i a)) ≤ ∑ i ∈ s, mean (fun a => truth (P i a)) := by
  classical
  calc
    _ ≤ mean (fun a => ∑ i ∈ s, truth (P i a)) := by
      apply mean_mono
      intro a
      by_cases h : ∃ i ∈ s, P i a
      · obtain ⟨i, hi, hPi⟩ := h
        have hleft : truth (∃ i ∈ s, P i a) = truth (P i a) := by
          simp [truth, hPi, show ∃ i ∈ s, P i a from ⟨i, hi, hPi⟩]
        rw [hleft]
        exact Finset.single_le_sum (fun j _ => truth_nonneg (P j a)) hi
      · simp only [truth, h, ite_false]
        exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    _ = _ := Finset.expect_sum_comm _ _ _

theorem mean_truth_or_le (P Q : A → Prop) :
    mean (fun a => truth (P a ∨ Q a)) ≤
      mean (fun a => truth (P a)) + mean (fun a => truth (Q a)) := by
  rw [← mean_add]
  apply mean_mono
  intro a
  classical
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [truth, hP, hQ]

theorem exists_not_of_mean_truth_lt_one [Nonempty A] (P : A → Prop)
    (h : mean (fun a => truth (P a)) < 1) : ∃ a, ¬ P a := by
  classical
  by_contra hn
  push Not at hn
  have heq : mean (fun a => truth (P a)) = 1 := by simp [truth, hn]
  linarith

theorem mean_truth_abs_ge_le (f : A → ℝ) (ε : ℝ) (hε : 0 < ε) :
    mean (fun a => truth (ε ≤ |f a|)) ≤ mean (fun a => f a ^ 2) / ε ^ 2 := by
  have hpoint (a : A) : ε ^ 2 * truth (ε ≤ |f a|) ≤ f a ^ 2 := by
    classical
    by_cases h : ε ≤ |f a|
    · simp only [truth, h, ite_true, mul_one]
      simpa only [sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg _)).mpr h
    · simp only [truth, h, ite_false, mul_zero]
      exact sq_nonneg _
  have h := mean_mono hpoint
  rw [mean_const_mul] at h
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [mul_comm] using h

end TuranUniversality.Density

namespace TuranUniversality.RGraph

open Selector Density
universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

theorem sample_density_deviation_probability [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) :
    mean (fun f : Fin m → W => truth
        (ε ≤ |F.homDensity (G.sample m f) - F.homDensity G|)) ≤
      6 * (Fintype.card V : ℝ) ^ 2 / (m * ε ^ 2) := by
  calc
    _ ≤ mean (fun f : Fin m → W =>
        (F.homDensity (G.sample m f) - F.homDensity G) ^ 2) / ε ^ 2 :=
      mean_truth_abs_ge_le _ ε hε
    _ ≤ (6 * (Fintype.card V : ℝ) ^ 2 / m) / ε ^ 2 :=
      div_le_div_of_nonneg_right (F.mean_sample_homDensity_square_error G m hm)
        (sq_nonneg ε)
    _ = _ := by ring

theorem sample_embedding_probability_le [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) (m : ℕ) :
    mean (fun f : Fin m → W => truth (∃ g, F.IsEmbedding (G.sample m f) g)) ≤
      (m : ℝ) ^ Fintype.card V * F.homDensity G := by
  classical
  have hpoint (g : V → Fin m) :
      mean (fun f : Fin m → W => truth (F.IsEmbedding (G.sample m f) g)) ≤
        F.homDensity G := by
    by_cases hg : Function.Injective g
    · have heq : (fun f : Fin m → W => truth (F.IsEmbedding (G.sample m f) g)) =
          (fun f => F.homIndicator (G.sample m f) g) := by
        funext f
        by_cases hF : F.IsHom (G.sample m f) g
        · have hE : F.IsEmbedding (G.sample m f) g := ⟨hg, hF⟩
          simp only [truth, hE, ite_true, F.homIndicator_of_hom _ hF]
        · have hE : ¬ F.IsEmbedding (G.sample m f) g := fun h => hF h.2
          simp only [truth, hE, ite_false, F.homIndicator_of_not_hom _ hF]
      rw [heq, F.mean_homIndicator_sample_of_injective G g hg]
    · have heq : (fun f : Fin m → W => truth (F.IsEmbedding (G.sample m f) g)) =
          (fun _ => (0 : ℝ)) := by
        funext f
        simp [truth, IsEmbedding, hg]
      rw [heq, mean_zero]
      exact F.homDensity_nonneg G
  calc
    _ ≤ ∑ g : V → Fin m,
        mean (fun f : Fin m → W => truth (F.IsEmbedding (G.sample m f) g)) := by
      simpa using mean_truth_exists_finset_le (Finset.univ : Finset (V → Fin m))
        (fun g f => F.IsEmbedding (G.sample m f) g)
    _ ≤ ∑ _g : V → Fin m, F.homDensity G := Finset.sum_le_sum (fun g _ => hpoint g)
    _ = _ := by simp [Nat.cast_pow]

end TuranUniversality.RGraph

namespace TuranUniversality.SetFamily

open Selector Density
universe u
variable {r : ℕ} {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]

theorem sample_notFree_probability_le (F : Set (FiniteGraph r)) (G : RGraph W r) (m : ℕ) :
    mean (fun f : Fin m → W => truth (¬ Free F (G.sample m f))) ≤
      ∑ A ∈ truncate F m, (m : ℝ) ^ A.1 * A.2.homDensity G := by
  classical
  have heq (f : Fin m → W) : (¬ Free F (G.sample m f)) ↔
      ∃ A ∈ truncate F m, ∃ g, A.2.IsEmbedding (G.sample m f) g := by
    rw [← free_truncate_iff F m]
    simp only [familyFree, not_forall, not_not]
    simp
  calc
    _ = mean (fun f : Fin m → W => truth
        (∃ A ∈ truncate F m, ∃ g, A.2.IsEmbedding (G.sample m f) g)) := by
      apply mean_congr
      intro f
      simp only [truth, heq]
      split_ifs <;> rfl
    _ ≤ ∑ A ∈ truncate F m, mean (fun f : Fin m → W =>
        truth (∃ g, A.2.IsEmbedding (G.sample m f) g)) :=
      mean_truth_exists_finset_le (truncate F m) _
    _ ≤ _ := Finset.sum_le_sum (fun A _ => by
      simpa only [Fintype.card_fin] using A.2.sample_embedding_probability_le G m)

/-- A single sample is free and simultaneously approximates all prescribed
test densities whenever the explicit union-bound budget is less than one. -/
theorem exists_free_sample_close (F : Set (FiniteGraph r)) (tests : Finset (FiniteGraph r))
    (G : RGraph W r) (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hbudget : (∑ A ∈ truncate F m, (m : ℝ) ^ A.1 * A.2.homDensity G) +
      (∑ A ∈ tests, 6 * (A.1 : ℝ) ^ 2 / (m * ε ^ 2)) < 1) :
    ∃ f : Fin m → W, Free F (G.sample m f) ∧
      ∀ A ∈ tests, |A.2.homDensity (G.sample m f) - A.2.homDensity G| < ε := by
  classical
  let P (f : Fin m → W) : Prop := ¬ Free F (G.sample m f)
  let Q (f : Fin m → W) : Prop :=
    ∃ A ∈ tests, ε ≤ |A.2.homDensity (G.sample m f) - A.2.homDensity G|
  have hP : mean (fun f => truth (P f)) ≤
      ∑ A ∈ truncate F m, (m : ℝ) ^ A.1 * A.2.homDensity G :=
    sample_notFree_probability_le F G m
  have hQ : mean (fun f => truth (Q f)) ≤
      ∑ A ∈ tests, 6 * (A.1 : ℝ) ^ 2 / (m * ε ^ 2) := by
    apply (mean_truth_exists_finset_le tests _).trans
    exact Finset.sum_le_sum (fun A _ => by
      simpa only [Fintype.card_fin] using A.2.sample_density_deviation_probability G m hm ε hε)
  have hbad : mean (fun f => truth (P f ∨ Q f)) < 1 :=
    (mean_truth_or_le P Q).trans_lt ((add_le_add hP hQ).trans_lt hbudget)
  obtain ⟨f, hf⟩ := exists_not_of_mean_truth_lt_one (fun f => P f ∨ Q f) hbad
  have hfree : Free F (G.sample m f) := by
    by_contra hn
    exact hf (Or.inl hn)
  refine ⟨f, hfree, ?_⟩
  intro A hA
  exact lt_of_not_ge (fun h => hf (Or.inr ⟨A, hA, h⟩))

end TuranUniversality.SetFamily
