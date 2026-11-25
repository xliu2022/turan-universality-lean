module

public import TuranUniversality.Structural.NumberedProfile

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

/-! # The ordinary structural universality theorem

This proof closes every clause of the independent statement, including the
fixed finite multiset profile, floor/ceiling rounding, actual edge edits,
the whole inner extremal space, and one jointly primitive-recursive compiler.
-/

namespace TuranUniversality.Structural

open Fixed

/-- V4 Theorem 1.3 for the literal binary halting semantics of the project. -/
theorem registry_main : Registry.structuralStatement := by
  refine ⟨tau3, tau3_bounds.1, tau3_bounds.2, forbiddenCompiler,
    forbiddenCompiler_primrec, ?_, uniformityThreshold, uniformityThreshold_ge_four,
    compiler, compiler_primrec, ?_⟩
  · intro β
    exact ⟨forbiddenCompiler_has_edges β, forbiddenCompiler_density_eq_iff β,
      forbiddenCompiler_density_strict_iff β⟩
  · intro r hr
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hr
    have htr : r = t + uniformityThreshold := ht.trans (Nat.add_comm _ _)
    clear ht
    subst r
    refine ⟨roleCount t, numberedPattern t, numberedWeight t, numberedCounts t,
      test t false, test t true, roleCount_pos t, numberedWeight_probability t,
      numberedCounts_balanced t, ?_⟩
    intro β
    dsimp only
    rw [compiler_decode_offset]
    constructor
    · intro hβ
      rw [numbered_profile]
      exact ⟨nonhalting_profiles t β hβ, neutral_separator t, numbered_stable t β hβ⟩
    · exact halting_twoPhases t β

end TuranUniversality.Structural
