/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.ComputationalRecovery

/-! # Complete profile reconstruction and exclusion of legal targets -/

@[expose] public section

namespace TuranUniversality.Selector

open RGraph Weighted Computation.MatchingSystem

variable {Roots Code Kinds Alphabet Data RootBlocks : Type*} {L : ℕ}
    [Fintype Roots] [DecidableEq Roots] [Fintype Code] [DecidableEq Code] [Nonempty Code]
    [Fintype Kinds] [DecidableEq Kinds] [Fintype Data] [DecidableEq Data]
    [DecidableEq RootBlocks] [Inhabited Alphabet] [DecidableEq Alphabet]

/-- A complete legal partial rooting is reconstructed from the genuine
compatible profiles. The internal constants are parameterized by the
maximum root block size. -/
theorem profile_reconstruction {X I : Type*} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I]
    (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (spec : Specification Alphabet) (A : RGraph X 3) (target : RootedModel Roots Data)
    (hlegal : RootedLegal S target color spec)
    (hdeclared : ∀ d, ∃ c, S.codes.Declared target d c)
    (block : Roots → RootBlocks) (bound : ℕ) (hbound : 0 < bound)
    (hblocks : ∀ b, (Finset.univ.filter fun r => block r = b).card ≤ bound)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → block r = block s)
    (hI : 3 * Fintype.card Code + bound ≤ Fintype.card I)
    (f : I → ExtensionVertex X → Roots ⊕ Data)
    (hroots : ∀ i r x y, f i (Sum.inl x) = Sum.inl r → f i (Sum.inl y) = Sum.inl r → x = y)
    (hcross : ∀ x y z, {x, y, z} ∈ A.pairExtension.edges →
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k → {f i x, f j y, f k z} ∈ target.toRGraph.edges) :
    Admissible S color spec A := by
  classical
  choose code hcode using hdeclared
  let row : X → I → Roots ⊕ Data := fun x i => f i (Sum.inl x)
  have hcard : 3 ≤ Fintype.card I := by
    have hC : 0 < Fintype.card Code := Fintype.card_pos
    omega
  have hprivacy : ∀ x y, x ≠ y → ∀ i j, i ≠ j → row x i ≠ row y j :=
    profile_cross_privacy hcard A target.toRGraph f hcross
  have hrowcross : CrossEdges A target row := by
    intro x y z he i j k hij hik hjk
    have hext : {Sum.inl x, Sum.inl y, Sum.inl z} ∈ A.pairExtension.edges := by
      simpa using (core_isHom A) _ he
    exact hcross (Sum.inl x) (Sum.inl y) (Sum.inl z) hext i j k hij hik hjk
  obtain ⟨P⟩ := exists_row_rooting row code block bound hbound hblocks hI hprivacy hroots
  exact P.admissible S A target hcode hrowcross hinside hprivacy color spec hlegal

/-- A product of forbidden guarded core extensions has no homomorphism
to any fully declared legal target. This includes a one-factor product. -/
theorem product_target_exclusion {F V GuardBlocks : Type*} {X : F → Type*}
    [Fintype F] [Nonempty F] [DecidableEq F]
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype GuardBlocks] [DecidableEq GuardBlocks]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (spec : Specification Alphabet) (A : (i : F) → RGraph (X i) 3)
    (hforbidden : ∀ i, ¬ Admissible S color spec (A i))
    (target : RootedModel Roots Data) (hlegal : RootedLegal S target color spec)
    (hdeclared : ∀ d, ∃ c, S.codes.Declared target d c)
    (rootBlock : Roots → RootBlocks) (bound : ℕ) (hbound : 0 < bound)
    (hrootBlocks : ∀ b, (Finset.univ.filter fun r => rootBlock r = b).card ≤ bound)
    (hinside : ∀ c r s, {r, s} ∈ (S.codes.missing c).pairs → rootBlock r = rootBlock s)
    (q : ℝ) (hq : 0 < q) (hroots : (Fintype.card Roots : ℝ) ≤ q)
    (hn : 1048576 ≤ Fintype.card V) (hnq : 19 * q / 20 < Fintype.card V)
    (h t : ℕ) (hh : 0 < h) (ht : 8 * h ≤ t) (hprofile : 3 * Fintype.card Code + bound ≤ h)
    (guardBlock : V → GuardBlocks) (hguardBlocks : ∀ b, (blockFiber guardBlock b).card = t)
    (guard : (i : F) → V → X i) (hguard : ∀ i, Function.Injective (guard i))
    (hedges : ∀ i x y z, x ≠ y → x ≠ z → y ≠ z →
      guardBlock x = guardBlock y → guardBlock x = guardBlock z →
        {guard i x, guard i y, guard i z} ∈ (A i).edges) :
    (RGraph.product fun i => (A i).pairExtension).HomFree target.toRGraph := by
  rintro ⟨φ, hφ⟩
  obtain ⟨j, f, hfroots, hfcross⟩ := compatible_profiles q hq hroots hn hnq h t hh ht
    guardBlock hguardBlocks A target.toRGraph guard hguard hedges φ hφ Sum.inl
  apply hforbidden j
  exact profile_reconstruction S color spec (A j) target hlegal hdeclared rootBlock bound hbound
    hrootBlocks hinside (by simpa using hprofile) f hfroots hfcross

end TuranUniversality.Selector
