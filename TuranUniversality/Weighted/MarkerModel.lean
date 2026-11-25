module

public import TuranUniversality.Weighted.Fine
public import TuranUniversality.Weighted.MatchingGrounded
public import TuranUniversality.Computation.RootedRealization

/-! # The actual data edge is absorbed when all marked components are open -/

@[expose] public section

namespace TuranUniversality.Weighted.CompilerSignature

open scoped BigOperators
open TuranUniversality.Computation.MatchingSystem

set_option backward.isDefEq.respectTransparency false

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

omit [DecidableEq Code] [DecidableEq Kinds] [Fintype Kinds] in
theorem ambiguous_subset_sum_le (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d)
    (I : Finset Data) (hI : ∀ d ∈ I, S.codes.Ambiguous M d) :
    (∑ d ∈ I, x d) ≤ S.codes.ambiguousWeight M x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI d hd⟩
  · exact fun d hd hnot => hx d

omit [Fintype Kinds] in
theorem marker_declared_mem_marks (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (p : Finset Data) (hp : p ∈ M.dataTriples) (a : Data) (ha : a ∈ p)
    (hnot : ¬ S.codes.Ambiguous M a) : a ∈ S.marks M := by
  obtain ⟨c, hc⟩ := S.declared_code_exists M h.candidates a
    ((S.codes.mem_declaredVertices M a).mpr hnot)
  have hkind := h.markerTypes p hp a ha c hc
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (S.codes.mem_typeVertices M S.physical S.cellKind a).mpr
    ⟨c, hc, hkind⟩, p, hp, ha⟩

omit [Fintype Kinds] in
/-- The four endpoint cases apply to the actual marker triple; declaration
and ambiguity are read from its actual root links. -/
theorem marker_triple_reward (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) (η : ℝ) (hη : 0 ≤ η)
    (hmarks : ∀ a ∈ S.marks M, x a ≤ η) (p : Finset Data) (hp : p ∈ M.dataTriples) :
    (∏ d ∈ p, x d) ≤ (S.codes.ambiguousWeight M x) ^ 3 / 27 + 2 * η ^ 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (M.dataTriples_uniform p hp)
  have hdecl : ∀ d ∈ ({a, b, c} : Finset Data), ¬ S.codes.Ambiguous M d → x d ≤ η := by
    intro d hd hnot
    exact hmarks d (S.marker_declared_mem_marks M h _ hp d hd hnot)
  have hsum1 : ∀ d, S.codes.Ambiguous M d → x d ≤ S.codes.ambiguousWeight M x := by
    intro d hd
    have hs := S.ambiguous_subset_sum_le M x hx {d} (by simpa using hd)
    simpa using hs
  have hsum2 : ∀ d e, d ≠ e → S.codes.Ambiguous M d → S.codes.Ambiguous M e →
      x d + x e ≤ S.codes.ambiguousWeight M x := by
    intro d e hde hd he
    have hs := S.ambiguous_subset_sum_le M x hx {d, e} (by
      intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl <;> assumption)
    simpa [hde] using hs
  have hsum3 : S.codes.Ambiguous M a → S.codes.Ambiguous M b → S.codes.Ambiguous M c →
      x a + x b + x c ≤ S.codes.ambiguousWeight M x := by
    intro ha hb hc
    have hs := S.ambiguous_subset_sum_le M x hx {a, b, c} (by
      intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl <;> assumption)
    simpa [hab, hac, hbc, add_assoc] using hs
  rw [Finset.prod_insert (by simp [hab, hac] : a ∉ ({b, c} : Finset Data)), Finset.prod_pair hbc]
  have ha0 := hx a
  have hb0 := hx b
  have hc0 := hx c
  by_cases ha : S.codes.Ambiguous M a
  · by_cases hb : S.codes.Ambiguous M b
    · by_cases hc : S.codes.Ambiguous M c
      · have hh := all_ambiguous_reward (x a) (x b) (x c) _ η ha0 hb0 hc0 hη (hsum3 ha hb hc)
        nlinarith
      · have hh := one_declared_reward (x a) (x b) (x c) _ η ha0 hb0 hc0 hη
          (hsum2 a b hab ha hb) (hdecl c (by simp) hc)
        nlinarith
    · by_cases hc : S.codes.Ambiguous M c
      · have hh := one_declared_reward (x a) (x c) (x b) _ η ha0 hc0 hb0 hη
          (hsum2 a c hac ha hc) (hdecl b (by simp) hb)
        nlinarith
      · have hh := two_declared_reward (x a) (x b) (x c) _ η ha0 hb0 hc0 hη
          (hsum1 a ha) (hdecl b (by simp) hb) (hdecl c (by simp) hc)
        nlinarith
  · by_cases hb : S.codes.Ambiguous M b
    · by_cases hc : S.codes.Ambiguous M c
      · have hh := one_declared_reward (x b) (x c) (x a) _ η hb0 hc0 ha0 hη
          (hsum2 b c hbc hb hc) (hdecl a (by simp) ha)
        nlinarith
      · have hh := two_declared_reward (x b) (x a) (x c) _ η hb0 ha0 hc0 hη
          (hsum1 b hb) (hdecl a (by simp) ha) (hdecl c (by simp) hc)
        nlinarith
    · by_cases hc : S.codes.Ambiguous M c
      · have hh := two_declared_reward (x c) (x a) (x b) _ η hc0 ha0 hb0 hη
          (hsum1 c hc) (hdecl a (by simp) ha) (hdecl b (by simp) hb)
        nlinarith
      · have hh := all_declared_reward (x a) (x b) (x c) _ η ha0 hb0 hc0
          (S.ambiguousWeight_nonneg M x hx) hη
          (hdecl a (by simp) ha) (hdecl b (by simp) hb) (hdecl c (by simp) hc)
        nlinarith

theorem marker_contribution_reward (S : CompilerSignature Roots Code Kinds L)
    (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (z : Roots → ℝ) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d) (η : ℝ) (hη : 0 ≤ η)
    (hmarks : ∀ a ∈ S.marks M, x a ≤ η) :
    M.contribution 0 z x ≤ (S.codes.ambiguousWeight M x) ^ 3 / 27 + 2 * η ^ 3 := by
  rw [M.contribution_zero_eq]
  by_cases hE : M.dataTriples = ∅
  · rw [hE, Finset.sum_empty]
    have hw := S.ambiguousWeight_nonneg M x hx
    positivity
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    have hsingle : M.dataTriples = {p} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hp, fun q hq => Finset.card_le_one.mp h.oneMarker q hq p hp⟩
    rw [hsingle, Finset.sum_singleton]
    exact S.marker_triple_reward M h x hx η hη hmarks p hp

theorem rootedRealization_totalDefect {Alphabet : Type*} [Inhabited Alphabet]
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (h : S.IncidenceLegal M) (color : Code → Alphabet) (x : Data → ℝ) :
    (rootedRealization S M color h.matching).totalDefect x = S.totalDefect M h x := by
  unfold totalDefect Realization.totalDefect
  rw [Fin.sum_univ_three]
  simp [rootedRealization, PartialMatching.defect, PartialMatching.leftMatched,
    PartialMatching.rightMatched, unionMatching, sourceKind, targetKind]

/-- Choosing an actual maximum among the marked vertices produces the
grounded endpoint bound required by all four reward cases. -/
theorem exists_grounded_marker_bound {Alphabet : Type*} [Inhabited Alphabet]
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data)
    (h : S.IncidenceLegal M) (color : Code → Alphabet) (x : Data → ℝ) (hx : ∀ d, 0 ≤ x d)
    (hopen : ∀ a ∈ S.marks M, ¬ (rootedRealization S M color h.matching).ClosedAt a) :
    ∃ η : ℝ, 0 ≤ η ∧ (∀ a ∈ S.marks M, x a ≤ η) ∧
      η ^ 3 ≤ 4 * (∑ d, x d) * S.totalDefect M h x := by
  classical
  by_cases hE : (S.marks M).Nonempty
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (S.marks M) x hE
    refine ⟨x a, hx a, hmax, ?_⟩
    have hh := (rootedRealization S M color h.matching).open_grounded_bound x hx a (hopen a ha)
    rw [S.rootedRealization_totalDefect M h color x] at hh
    exact hh
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · intro a ha
      exact False.elim (hE ⟨a, ha⟩)
    · simp only [zero_pow (by omega : 3 ≠ 0)]
      exact mul_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => hx d))
        (S.totalDefect_nonneg M h x)

/-- The complete weighted upper bound for actual rooted models with open
marked components. Nonhalting enters only through the separate computational
theorem proving these actual components are open. -/
theorem open_marked_edgePolynomial_le_baseline {Alphabet : Type*} [Inhabited Alphabet]
    (S : CompilerSignature Roots Code Kinds L) (M : RootedModel Roots Data) (h : S.IncidenceLegal M)
    (color : Code → Alphabet) (z : Roots → ℝ) (x : Data → ℝ) (u : ℝ)
    (hm : 30 ≤ Fintype.card Kinds) (hu : 100000 ≤ u)
    (hq : (Fintype.card Roots : ℝ) = rootCount (Fintype.card Kinds : ℝ))
    (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1)
    (hopen : ∀ a ∈ S.marks M, ¬ (rootedRealization S M color h.matching).ClosedAt a) :
    M.toRGraph.edgePolynomial (Sum.elim z x) ≤
      baselineMax (Fintype.card Kinds) (Fintype.card Roots) := by
  have hmr : (30 : ℝ) ≤ Fintype.card Kinds := by exact_mod_cast hm
  by_cases hP : coeffA (Fintype.card Roots) ≤ M.toRGraph.edgePolynomial (Sum.elim z x)
  · obtain ⟨η, hη, hmarks, hground⟩ := S.exists_grounded_marker_bound M h color x hx hopen
    have hreward := S.marker_contribution_reward M h z x hx η hη hmarks
    have hreg := S.codes.fine_regime M z x u (by linarith) hqu hz hx hnorm h.candidates h.oneMarker hP
    have hα : 8 * (∑ d, x d) ≤ 256 / u := by
      have hu0 : 0 < u := by linarith
      have ht := (lt_div_iff₀ hu0).mp hreg.1
      apply (le_div_iff₀ hu0).mpr
      nlinarith
    have habsorb := marker_defect_absorption (M.contribution 0 z x) (S.codes.ambiguousWeight M x)
      η (∑ d, x d) (S.totalDefect M h x) (256 / u)
      (S.totalDefect_nonneg M h x) hreward hground hα
    exact S.edgePolynomial_le_baseline_of_marker_absorbed M h z x u hm hu hq hqu hLlo hLhi
      hz hx hnorm habsorb
  · have hb := (baselineMax_strict_bounds (Fintype.card Kinds : ℝ) hmr).1
    rw [← hq] at hb
    exact (le_of_not_ge hP).trans hb.le

end TuranUniversality.Weighted.CompilerSignature
