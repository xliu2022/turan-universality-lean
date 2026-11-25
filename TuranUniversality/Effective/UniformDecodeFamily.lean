module

public import TuranUniversality.Effective.UniformEncoding
public import TuranUniversality.Density.FamilyBasic

@[expose] public section

/-! # The public decoding of a finite list of uniform hypergraph codes -/

namespace TuranUniversality.Effective.Uniform

noncomputable def decodeFamily (r : ℕ) (gs : List Code) : Finset (FiniteGraph r) := by
  classical
  exact (gs.map (decodeFinite r)).toFinset

@[simp] theorem mem_decodeFamily (r : ℕ) (gs : List Code) (A : FiniteGraph r) :
    A ∈ decodeFamily r gs ↔ ∃ g ∈ gs, decodeFinite r g = A := by
  classical
  simp [decodeFamily]

@[simp] theorem decodeFamily_singleton (r : ℕ) (g : Code) :
    decodeFamily r [g] = {decodeFinite r g} := by simp [decodeFamily]

end TuranUniversality.Effective.Uniform
