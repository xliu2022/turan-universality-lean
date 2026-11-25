module

public import TuranUniversality.Weighted.OneRoot

/-! # Summing the actual one-root link estimates -/

@[expose] public section

namespace TuranUniversality.Weighted

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Sum separate estimates on an embedded index set and its complement. No
sign condition on the exceptional corrections is needed. -/
theorem sum_bound_indexed {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A ↪ B) (g base : B → ℝ) (extra : A → ℝ)
    (hi : ∀ a, g (f a) ≤ base (f a) + extra a)
    (ho : ∀ b, (¬ ∃ a, f a = b) → g b ≤ base b) :
    (∑ b, g b) ≤ (∑ b, base b) + ∑ a, extra a := by
  let J := Finset.univ.image f
  have hJ : (∑ b ∈ J, g b) ≤ (∑ b ∈ J, base b) + ∑ a, extra a := by
    dsimp [J]
    rw [Finset.sum_image (fun _ _ _ _ he => f.injective he),
      Finset.sum_image (fun _ _ _ _ he => f.injective he), ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => hi a
  have hrest : (∑ b ∈ Finset.univ \ J, g b) ≤ ∑ b ∈ Finset.univ \ J, base b := by
    apply Finset.sum_le_sum
    intro b hb
    apply ho b
    rintro ⟨a, rfl⟩
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  have hg := Finset.sum_sdiff (Finset.subset_univ J) (f := g)
  have hb := Finset.sum_sdiff (Finset.subset_univ J) (f := base)
  linarith

namespace CompilerSignature

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

def copyMass (S : CompilerSignature Roots Code Kinds L) (z : Roots → ℝ) (e : Fin 3) : ℝ :=
  ∑ j, z (S.copyRoot (e, j))

def totalDefect (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (h : S.IncidenceLegal M) (x : Data → ℝ) : ℝ :=
  ∑ e, (S.unionMatching M e (h.matching e)).defect x x

omit [Fintype Kinds] in
theorem totalDefect_nonneg (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M) (x : Data → ℝ) :
    0 ≤ S.totalDefect M h x :=
  Finset.sum_nonneg fun _e _ => PartialMatching.defect_nonneg _ x x

omit [DecidableEq Code] [Fintype Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem copyMass_nonneg (S : CompilerSignature Roots Code Kinds L)
    (z : Roots → ℝ) (hz : ∀ r, 0 ≤ z r) (e : Fin 3) : 0 ≤ S.copyMass z e :=
  Finset.sum_nonneg fun _j _ => hz _

/-- The whole actual one-root edge contribution, with a separate coefficient
for each of the three extracted union-matching defects. -/
theorem one_root_sum_bound (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (z : Roots → ℝ) (x : Data → ℝ) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) :
    M.contribution 1 z x ≤
      (∑ r, z r) * elementary Finset.univ ((S.partition M h.candidates).mass x) 2 +
      (∑ r, z r) * ((∑ d, x d) * S.codes.ambiguousWeight M x -
        (S.codes.ambiguousWeight M x) ^ 2 / 2) +
      (∑ e, S.copyMass z e / 2 *
        ((S.partition M h.candidates).mass x (S.sourceKind e) -
          (S.partition M h.candidates).mass x (S.targetKind e)) ^ 2) -
      ∑ e, S.copyMass z e / 2 * (S.unionMatching M e (h.matching e)).defect x x := by
  let y := (S.partition M h.candidates).mass x
  let amb := (∑ d, x d) * S.codes.ambiguousWeight M x - (S.codes.ambiguousWeight M x) ^ 2 / 2
  let corr := fun e => (y (S.sourceKind e) - y (S.targetKind e)) ^ 2 / 2 -
    (S.unionMatching M e (h.matching e)).defect x x / 2
  have hi : ∀ p : Fin 3 × Fin L,
      z (S.copyRoot p) * (∑ a ∈ M.dataLink (S.copyRoot p), ∏ d ∈ a, x d) ≤
      z (S.copyRoot p) * (elementary Finset.univ y 2 + amb) + z (S.copyRoot p) * corr p.1 := by
    rintro ⟨e, j⟩
    have hlocal := S.indexed_dataLink_bound M h e j x hx
    have hdef := S.copy_defect_ge_union M e j (h.matching e) x hx
    have hlocal' : (∑ a ∈ M.dataLink (S.copyRoot (e, j)), ∏ d ∈ a, x d) ≤
        elementary Finset.univ y 2 + amb + corr e := by
      dsimp [y, amb, corr]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlocal' (hz (S.copyRoot (e, j)))
    simpa only [mul_add] using hmul
  have ho : ∀ r, (¬ ∃ p, S.copyRoot p = r) →
      z r * (∑ a ∈ M.dataLink r, ∏ d ∈ a, x d) ≤ z r * (elementary Finset.univ y 2 + amb) := by
    intro r hr
    have hnot : ¬ ∃ e j, S.copyRoot (e, j) = r := by
      rintro ⟨e, j, he⟩
      exact hr ⟨(e, j), he⟩
    have hlocal := S.additional_dataLink_bound M h r hnot x hx
    have hlocal' : (∑ a ∈ M.dataLink r, ∏ d ∈ a, x d) ≤ elementary Finset.univ y 2 + amb := by
      dsimp [y, amb]
      linarith
    exact mul_le_mul_of_nonneg_left hlocal' (hz r)
  have hsum := sum_bound_indexed S.copyRoot
    (fun r => z r * ∑ a ∈ M.dataLink r, ∏ d ∈ a, x d)
    (fun r => z r * (elementary Finset.univ y 2 + amb))
    (fun p => z (S.copyRoot p) * corr p.1) hi ho
  rw [← M.contribution_one_eq, ← Finset.sum_mul, Fintype.sum_prod_type] at hsum
  have hcopies : (∑ e, ∑ j, z (S.copyRoot (e, j)) * corr e) =
      ∑ e, S.copyMass z e * corr e := by
    apply Finset.sum_congr rfl
    intro e he
    exact (Finset.sum_mul _ _ _).symm
  rw [hcopies] at hsum
  dsimp [corr] at hsum
  simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib] at hsum
  dsimp [y, amb] at hsum
  have hnorm : (∑ e, S.copyMass z e *
        ((S.partition M h.candidates).mass x (S.sourceKind e) -
          (S.partition M h.candidates).mass x (S.targetKind e)) ^ 2 / 2) =
      ∑ e, S.copyMass z e / 2 *
        ((S.partition M h.candidates).mass x (S.sourceKind e) -
          (S.partition M h.candidates).mass x (S.targetKind e)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro e he
    ring
  have hdefnorm : (∑ e, S.copyMass z e * (S.unionMatching M e (h.matching e)).defect x x / 2) =
      ∑ e, S.copyMass z e / 2 * (S.unionMatching M e (h.matching e)).defect x x := by
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hnorm, hdefnorm] at hsum
  simpa only [mul_add, add_sub_assoc] using hsum

/-- If the indexed roots have small type incidence, the declared type
variance pays for all within-type corrections. -/
theorem one_root_variance_bound (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (z : Roots → ℝ) (x : Data → ℝ) (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d)
    (hm : 0 < Fintype.card Kinds) (Δ α : ℝ)
    (hΔ : ∀ k, incidenceWeight S.sourceKind S.targetKind (S.copyMass z) k ≤ Δ)
    (hα : ∀ e, 2 * α ≤ S.copyMass z e) :
    M.contribution 1 z x ≤
      coeffC (Fintype.card Kinds) * (∑ r, z r) *
        ((∑ d, x d) - S.codes.ambiguousWeight M x) ^ 2 +
      (∑ r, z r) * ((∑ d, x d) * S.codes.ambiguousWeight M x -
        (S.codes.ambiguousWeight M x) ^ 2 / 2) -
      ((∑ r, z r) / 2 - Δ) * rootVariance Finset.univ ((S.partition M h.candidates).mass x) -
      α * S.totalDefect M h x := by
  have hsum := S.one_root_sum_bound M h z x hz hx
  have htype := type_polynomial_variance ((S.partition M h.candidates).mass x) hm
  have hmass := S.codes.total_type_mass M S.physical h.candidates x
  rw [hmass] at htype
  rw [htype] at hsum
  have hc := type_correction_bound S.sourceKind S.targetKind (S.copyMass z)
    ((S.partition M h.candidates).mass x)
    ((∑ k, (S.partition M h.candidates).mass x k) / (Fintype.card Kinds : ℝ)) Δ
    (fun e => S.copyMass_nonneg z hz e) hΔ
  change (∑ e, S.copyMass z e / 2 *
      ((S.partition M h.candidates).mass x (S.sourceKind e) -
        (S.partition M h.candidates).mass x (S.targetKind e)) ^ 2) ≤
    Δ * rootVariance Finset.univ ((S.partition M h.candidates).mass x) at hc
  have hd : α * S.totalDefect M h x ≤
      ∑ e, S.copyMass z e / 2 * (S.unionMatching M e (h.matching e)).defect x x := by
    rw [totalDefect, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    apply mul_le_mul_of_nonneg_right (by linarith [hα e])
    exact PartialMatching.defect_nonneg _ x x
  nlinarith

end CompilerSignature

end TuranUniversality.Weighted
