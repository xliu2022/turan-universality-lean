module

public import TuranUniversality.Weighted.MarkerModel
public import TuranUniversality.Computation.ClosedRecovery

/-! # Nonhalting implies the actual rooted weighted bound -/

@[expose] public section

namespace TuranUniversality.Weighted.CompilerSignature

open scoped BigOperators
open TuranUniversality.Computation
open TuranUniversality.Computation.MatchingSystem
open Turing

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Data : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Data] [Fintype Data]

theorem nonhalting_edgePolynomial_le_baseline
    {Γ Λ : Type*} [DecidableEq Γ] [Fintype Γ] [Inhabited Γ]
    [DecidableEq Λ] [Fintype Λ] [Inhabited Λ]
    (S : CompilerSignature Roots Code Kinds L) (G : RootedModel Roots Data)
    (color : Code → LocalSystem.Label Γ Λ) (M : TM0.Machine Γ Λ) (input : List Γ)
    (hlegal : RootedLegal S G color (LocalSystem.specification M input))
    (hn : ¬ (TM0.eval M input).Dom)
    (z : Roots → ℝ) (x : Data → ℝ) (u : ℝ)
    (hm : 30 ≤ Fintype.card Kinds) (hu : 100000 ≤ u)
    (hq : (Fintype.card Roots : ℝ) = rootCount (Fintype.card Kinds : ℝ))
    (hqu : (Fintype.card Roots : ℝ) = u ^ 2)
    (hLlo : 2048 * u ≤ (L : ℝ)) (hLhi : (L : ℝ) ≤ 2049 * u)
    (hz : ∀ r, 0 ≤ z r) (hx : ∀ d, 0 ≤ x d) (hnorm : (∑ r, z r) + (∑ d, x d) = 1) :
    G.toRGraph.edgePolynomial (Sum.elim z x) ≤
      baselineMax (Fintype.card Kinds) (Fintype.card Roots) := by
  obtain ⟨h, hcomp⟩ := hlegal
  apply S.open_marked_edgePolynomial_le_baseline G h color z x u hm hu hq hqu hLlo hLhi hz hx hnorm
  intro a ha
  exact (rootedRealization S G color h.matching).nonhalting_not_closed M input hcomp hn a ha

end TuranUniversality.Weighted.CompilerSignature
