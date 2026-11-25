/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootedImage
public import TuranUniversality.Computation.RootedRealization

/-! # Admissibility means existence of a legal partial rooting -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted Computation.MatchingSystem

/-- The vertex-to-label form of a partial injective root assignment. -/
abbrev VertexRooting (Roots X : Type*) :=
  {ρ : X → Option Roots // ∀ x y r, ρ x = some r → ρ y = some r → x = y}

variable {X Roots Code Kinds Alphabet : Type*} {L : ℕ}
    [Fintype X] [DecidableEq X] [Fintype Roots] [DecidableEq Roots]
    [Fintype Code] [DecidableEq Code] [Fintype Kinds] [DecidableEq Kinds]
    [Inhabited Alphabet] [DecidableEq Alphabet]

/-- This is the actual hereditary class used in the singleton reduction:
some partial assignment of the fixed root labels makes the source graph
legal under the incidence and computational rules. -/
def Admissible (S : CompilerSignature Roots Code Kinds L) (color : Code → Alphabet)
    (spec : Specification Alphabet) (A : RGraph X 3) : Prop :=
  ∃ ρ : VertexRooting Roots X,
    RootedLegal S (rootedImage A ρ.val ρ.property) color spec

end TuranUniversality.Selector
