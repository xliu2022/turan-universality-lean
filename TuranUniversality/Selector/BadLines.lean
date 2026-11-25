/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.CylinderSelector

/-! # Repeated root images on product lines -/

@[expose] public section

namespace TuranUniversality.Selector

variable {I V R T : Type*} {X : I → Type*}

/-- A map separates vertices differing in every coordinate. -/
def CoordinateProper (φ : ((i : I) → X i) → T) : Prop :=
  ∀ x y, (∀ i, x i ≠ y i) → φ x ≠ φ y

/-- Vary one coordinate and fix all other coordinates at guard vertices. -/
def coreLine [DecidableEq I] (guard : (i : I) → V → X i)
    (j : I) (x : X j) (w : I → V) : (i : I) → X i :=
  Function.update (fun i => guard i (w i)) j x

@[simp] theorem coreLine_same [DecidableEq I] (guard : (i : I) → V → X i)
    (j : I) (x : X j) (w : I → V) : coreLine guard j x w j = x := by
  simp [coreLine]

theorem coreLine_other [DecidableEq I] (guard : (i : I) → V → X i)
    (j : I) (x : X j) (w : I → V) {i : I} (hij : i ≠ j) :
    coreLine guard j x w i = guard i (w i) := Function.update_of_ne hij x _

/-- Full guard cylinders whose direction-`j` line repeats root `r`. -/
noncomputable def badLines [Fintype I] [DecidableEq I] [Fintype V]
    (φ : ((i : I) → X i) → T) (guard : (i : I) → V → X i)
    (root : R → T) (j : I) (r : R) : Finset (I → V) := by
  classical
  exact Finset.univ.filter fun w => ∃ x y : X j, x ≠ y ∧
    φ (coreLine guard j x w) = root r ∧ φ (coreLine guard j y w) = root r

@[simp] theorem mem_badLines [Fintype I] [DecidableEq I] [Fintype V]
    (φ : ((i : I) → X i) → T) (guard : (i : I) → V → X i)
    (root : R → T) (j : I) (r : R) (w : I → V) :
    w ∈ badLines φ guard root j r ↔ ∃ x y : X j, x ≠ y ∧
      φ (coreLine guard j x w) = root r ∧ φ (coreLine guard j y w) = root r := by
  classical
  simp [badLines]

theorem two_occurrences_avoid {X T : Type*} (f : X → T) (r : T)
    {x y : X} (hxy : x ≠ y) (hx : f x = r) (hy : f y = r) (z : X) :
    ∃ u, u ≠ z ∧ f u = r := by
  by_cases hxz : x = z
  · exact ⟨y, by simpa [← hxz] using Ne.symm hxy, hy⟩
  · exact ⟨x, hxz, hx⟩

theorem badLines_self [Fintype I] [DecidableEq I] [Fintype V]
    (φ : ((i : I) → X i) → T) (hφ : CoordinateProper φ)
    (guard : (i : I) → V → X i) (hguard : ∀ i, Function.Injective (guard i))
    (root : R → T) (j : I) (r : R) :
    ∀ w ∈ badLines φ guard root j r, ∀ v ∈ badLines φ guard root j r,
      ∃ i, i ≠ j ∧ w i = v i := by
  classical
  intro w hw v hv
  obtain ⟨x, y, hxy, hx, hy⟩ := (mem_badLines φ guard root j r w).mp hw
  obtain ⟨z, _, _, hz, _⟩ := (mem_badLines φ guard root j r v).mp hv
  obtain ⟨u, huz, hu⟩ := two_occurrences_avoid (fun x => φ (coreLine guard j x w))
    (root r) hxy hx hy z
  by_contra hn
  push Not at hn
  apply hφ (coreLine guard j u w) (coreLine guard j z v) _ (hu.trans hz.symm)
  intro i
  by_cases hij : i = j
  · subst i
    simpa using huz
  · rw [coreLine_other guard j u w hij, coreLine_other guard j z v hij]
    intro heq
    exact hn i hij (hguard i heq)

theorem badLines_cross [Fintype I] [DecidableEq I] [Fintype V]
    (φ : ((i : I) → X i) → T) (hφ : CoordinateProper φ)
    (guard : (i : I) → V → X i) (hguard : ∀ i, Function.Injective (guard i))
    (root : R → T) (j k : I) (hjk : j ≠ k) (r : R) :
    ∀ w ∈ badLines φ guard root j r, ∀ v ∈ badLines φ guard root k r,
      ∃ i, i ≠ j ∧ i ≠ k ∧ w i = v i := by
  classical
  intro w hw v hv
  obtain ⟨x, y, hxy, hx, hy⟩ := (mem_badLines φ guard root j r w).mp hw
  obtain ⟨z, z', hzz', hz, hz'⟩ := (mem_badLines φ guard root k r v).mp hv
  obtain ⟨u, huv, hu⟩ := two_occurrences_avoid (fun x => φ (coreLine guard j x w))
    (root r) hxy hx hy (guard j (v j))
  obtain ⟨u', hu'w, hu'⟩ := two_occurrences_avoid (fun x => φ (coreLine guard k x v))
    (root r) hzz' hz hz' (guard k (w k))
  by_contra hn
  push Not at hn
  apply hφ (coreLine guard j u w) (coreLine guard k u' v) _ (hu.trans hu'.symm)
  intro i
  by_cases hij : i = j
  · subst i
    rw [coreLine_same, coreLine_other guard k u' v hjk]
    exact huv
  · by_cases hik : i = k
    · subst i
      rw [coreLine_other guard j u w (Ne.symm hjk), coreLine_same]
      exact Ne.symm hu'w
    · rw [coreLine_other guard j u w hij, coreLine_other guard k u' v hik]
      intro heq
      exact hn i hij hik (hguard i heq)

/-- A coordinate-proper map has a direction with `h` compatible guard
profiles, none of whose core lines repeats a designated root. -/
theorem select_good_lines {B : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    (q : ℝ) (hq : 0 < q) (hroots : (Fintype.card R : ℝ) ≤ q)
    (hn : 1048576 ≤ Fintype.card V) (hnq : 19 * q / 20 < Fintype.card V)
    (h t : ℕ) (hh : 0 < h) (ht : 8 * h ≤ t)
    (block : V → B) (hblock : ∀ b, (blockFiber block b).card = t)
    (φ : ((i : I) → X i) → T) (hφ : CoordinateProper φ)
    (guard : (i : I) → V → X i) (hguard : ∀ i, Function.Injective (guard i))
    (root : R → T) :
    ∃ j : I, ∃ w : Fin h → I → V,
      (∀ a r x y, φ (coreLine guard j x (w a)) = root r →
        φ (coreLine guard j y (w a)) = root r → x = y) ∧
        (∀ i, Function.Injective (fun a => w a i)) ∧
          ∀ i a b, block (w a i) = block (w b i) := by
  classical
  obtain ⟨j, w, hw, hinj, hsame⟩ := select_good_cylinder_rows q hq hroots hn hnq h t hh ht
    block hblock (badLines φ guard root) (badLines_self φ hφ guard hguard root)
    (badLines_cross φ hφ guard hguard root)
  refine ⟨j, w, ?_, hinj, hsame⟩
  intro a r x y hx hy
  by_contra hxy
  exact hw a r ((mem_badLines φ guard root j r (w a)).mpr ⟨x, y, hxy, hx, hy⟩)

end TuranUniversality.Selector
