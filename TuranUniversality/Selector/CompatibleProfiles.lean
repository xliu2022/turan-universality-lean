/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.BadLines
public import TuranUniversality.Hypergraph.Product
public import TuranUniversality.Hypergraph.Extension

/-! # Compatible profiles from a genuine product homomorphism -/

@[expose] public section

namespace TuranUniversality.Selector

open RGraph

variable {I V R B T : Type*} {X : I → Type*}

theorem triple_product_mem [Fintype I] [Nonempty I]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (G : (i : I) → RGraph (X i) 3) (x y z : (i : I) → X i)
    (h : ∀ i, {x i, y i, z i} ∈ (G i).edges) :
    {x, y, z} ∈ (RGraph.product G).edges := by
  classical
  apply (RGraph.product_mem G _).mpr
  refine ⟨?_, ?_⟩
  · apply Nat.le_antisymm Finset.card_le_three
    let i : I := Classical.choice inferInstance
    calc
      3 = ({x i, y i, z i} : Finset (X i)).card := ((G i).uniform _ (h i)).symm
      _ = (({x, y, z} : Finset ((i : I) → X i)).image fun f => f i).card := by simp
      _ ≤ _ := Finset.card_image_le
  · intro i
    simpa using h i

/-- Pair extensions force a product homomorphism to separate any two
core tuples differing in every coordinate. -/
theorem product_core_coordinateProper [Fintype I] [Nonempty I]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [DecidableEq T]
    (A : (i : I) → RGraph (X i) 3) (target : RGraph T 3)
    (φ : ((i : I) → ExtensionVertex (X i)) → T)
    (hφ : (RGraph.product fun i => (A i).pairExtension).IsHom target φ) :
    CoordinateProper (fun x : (i : I) → X i => φ (fun i => Sum.inl (x i))) := by
  classical
  intro x y hxy heq
  let p : (i : I) → VertexPair (X i) := fun i => ⟨{x i, y i}, by simp [hxy i]⟩
  let z : (i : I) → ExtensionVertex (X i) := fun i => Sum.inr (p i)
  have hpoint (i : I) : {Sum.inl (x i), Sum.inl (y i), z i} ∈ (A i).pairExtension.edges := by
    have h := privateEdge_mem (A i) (p i)
    have heq : privateEdge (p i) = {Sum.inl (x i), Sum.inl (y i), z i} := by
      ext v
      simp [privateEdge, p, z, or_comm, or_assoc]
    exact heq ▸ h
  have hedge := triple_product_mem (fun i => (A i).pairExtension)
    (fun i => Sum.inl (x i)) (fun i => Sum.inl (y i)) z hpoint
  have he := hφ.injOn_edge hedge (by simp) (by simp) heq
  let i : I := Classical.choice inferInstance
  exact hxy i (Sum.inl.inj (congrFun he i))

theorem coreLine_map [DecidableEq I] {Y : I → Type*}
    (f : (i : I) → X i → Y i) (guard : (i : I) → V → X i)
    (j : I) (x : X j) (w : I → V) :
    (fun i => f i (coreLine guard j x w i)) =
      coreLine (fun i v => f i (guard i v)) j (f j x) w := by
  funext i
  by_cases hij : i = j
  · subst i
    simp
  · simp only [coreLine_other _ _ _ _ hij]

/-- The complete compatible-profile selector. Every hypothesis concerns
the actual finite guards and the actual product homomorphism. -/
theorem compatible_profiles
    [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [DecidableEq T]
    (q : ℝ) (hq : 0 < q) (hroots : (Fintype.card R : ℝ) ≤ q)
    (hn : 1048576 ≤ Fintype.card V) (hnq : 19 * q / 20 < Fintype.card V)
    (h t : ℕ) (hh : 0 < h) (ht : 8 * h ≤ t)
    (block : V → B) (hblock : ∀ b, (blockFiber block b).card = t)
    (A : (i : I) → RGraph (X i) 3) (target : RGraph T 3)
    (guard : (i : I) → V → X i) (hguard : ∀ i, Function.Injective (guard i))
    (hedges : ∀ i x y z, x ≠ y → x ≠ z → y ≠ z →
      block x = block y → block x = block z →
        {guard i x, guard i y, guard i z} ∈ (A i).edges)
    (φ : ((i : I) → ExtensionVertex (X i)) → T)
    (hφ : (RGraph.product fun i => (A i).pairExtension).IsHom target φ)
    (root : R → T) :
    ∃ j : I, ∃ f : Fin h → ExtensionVertex (X j) → T,
      (∀ a r x y, f a (Sum.inl x) = root r → f a (Sum.inl y) = root r → x = y) ∧
        ∀ x y z, {x, y, z} ∈ (A j).pairExtension.edges →
          ∀ a b c, a ≠ b → a ≠ c → b ≠ c → {f a x, f b y, f c z} ∈ target.edges := by
  classical
  let ψ : ((i : I) → X i) → T := fun x => φ (fun i => Sum.inl (x i))
  have hψ : CoordinateProper ψ := product_core_coordinateProper A target φ hφ
  obtain ⟨j, w, hw, hinj, hsame⟩ := select_good_lines q hq hroots hn hnq h t hh ht
    block hblock ψ hψ guard hguard root
  let extendedGuard : (i : I) → V → ExtensionVertex (X i) := fun i v => Sum.inl (guard i v)
  let f : Fin h → ExtensionVertex (X j) → T := fun a x => φ (coreLine extendedGuard j x (w a))
  have hcore (a : Fin h) (x : X j) : f a (Sum.inl x) = ψ (coreLine guard j x (w a)) := by
    unfold f ψ
    rw [coreLine_map]
  refine ⟨j, f, ?_, ?_⟩
  · intro a r x y hx hy
    apply hw a r x y
    · rw [← hcore]; exact hx
    · rw [← hcore]; exact hy
  · intro x y z he a b c hab hac hbc
    let X₁ := coreLine extendedGuard j x (w a)
    let X₂ := coreLine extendedGuard j y (w b)
    let X₃ := coreLine extendedGuard j z (w c)
    have hpoint (i : I) : {X₁ i, X₂ i, X₃ i} ∈ (A i).pairExtension.edges := by
      by_cases hij : i = j
      · subst i
        simpa [X₁, X₂, X₃] using he
      · simp only [X₁, X₂, X₃, coreLine_other _ _ _ _ hij]
        have hguardedge := hedges i (w a i) (w b i) (w c i)
          (fun he => hab (hinj i he)) (fun he => hac (hinj i he)) (fun he => hbc (hinj i he))
          (hsame i a b) (hsame i a c)
        simpa [extendedGuard] using (core_isHom (A i)) _ hguardedge
    have hproduct := triple_product_mem (fun i => (A i).pairExtension) X₁ X₂ X₃ hpoint
    simpa [X₁, X₂, X₃, f] using hφ _ hproduct

end TuranUniversality.Selector
