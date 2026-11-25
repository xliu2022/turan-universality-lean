module

public import TuranUniversality.Effective.UniformChecksPrimrec
public import TuranUniversality.Reduction.Universality

@[expose] public section

/-! # One primitive-recursive compiler for all ranks and inputs

The three-uniform branch is literally the previously proved singleton
compiler. Higher ranks enumerate the actual suspension obstructions and all
their pair-covering extensions. Ranks below three have the fixed empty-list
default. Both arguments vary in the single primitive-recursion theorem.
-/

namespace TuranUniversality.Effective.Uniform

open TuranUniversality.Computation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000

noncomputable def compiler (r : ℕ) (β : BinaryWord) : List Code :=
  if r = 3 then [liftThree (forbiddenCompiler β)]
  else if r < 3 then []
  else familyCodes r (liftThree (forbiddenCompiler β))

theorem compiler_primrec : Primrec₂ compiler := by
  have hp : Primrec (fun p : ℕ × BinaryWord => liftThree (forbiddenCompiler p.2)) :=
    liftThree_primrec.comp (forbiddenCompiler_primrec.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
    (Primrec.list_cons.comp hp (Primrec.const []))
    (Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.const 3)) (Primrec.const [])
      (familyCodes_primrec.comp Primrec.fst hp))

/-- Uniform computability follows from the joint proof, rather than from a
nonuniform choice of separately primitive-recursive rank sections. -/
theorem compiler_computable : Computable₂ compiler := compiler_primrec.to_comp

theorem compiler_fixed_primrec (r : ℕ) : Primrec (compiler r) :=
  compiler_primrec.comp (Primrec.const r) Primrec.id

@[simp] theorem compiler_three (β : BinaryWord) :
    compiler 3 β = [liftThree (forbiddenCompiler β)] := by simp [compiler]

theorem compiler_default (r : ℕ) (hr : r < 3) (β : BinaryWord) :
    compiler r β = [] := by simp [compiler, hr, show r ≠ 3 by omega]

theorem compiler_decode_three (β : BinaryWord) :
    ((compiler 3 β).map (decodeFinite 3)).toFinset =
      {Effective.decodeGraphCode (forbiddenCompiler β)} := by
  simp

theorem compiler_decode_other (r : ℕ) (hr : 3 ≤ r) (hne : r ≠ 3) (β : BinaryWord) :
    ((compiler r β).map (decodeFinite r)).toFinset =
      Uniformity.family (Effective.decodeGraphCode (forbiddenCompiler β)) r := by
  rw [compiler, ite_eq_right hne, ite_eq_right (by omega), familyCodes_decode, decodeFinite_liftThree]

end TuranUniversality.Effective.Uniform
