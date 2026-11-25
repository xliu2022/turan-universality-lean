module

public import TuranUniversality.Weighted.BalancedCompletion
public import TuranUniversality.Computation.PermutationTableau
public import TuranUniversality.Computation.RootedRealization

/-! # Turning total finite local permutations into actual rooted models -/

@[expose] public section

namespace TuranUniversality.Weighted

open TuranUniversality.Computation
open TuranUniversality.Computation.MatchingSystem
open scoped BigOperators

universe u v w t
variable {Roots : Type u} {Code : Type v} {Kinds : Type w} {Index : Type t} {L : ℕ}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Code] [Fintype Code]
  [DecidableEq Kinds] [Fintype Kinds] [DecidableEq Index] [Fintype Index]

structure PermutationSeed (S : CompilerSignature Roots Code Kinds L) (Index : Type t)
    [DecidableEq Index] [Fintype Index] where
  code : Kinds × Index → Code
  physical_code : ∀ d, S.physical (code d) = d.1
  H : Equiv.Perm Index
  V : Equiv.Perm Index
  markers : Finset (Finset (Kinds × Index))
  marker_uniform : ∀ p ∈ markers, p.card = 3
  one_marker : markers.card ≤ 1
  marker_cell : ∀ p ∈ markers, ∀ d ∈ p, d.1 = S.cellKind

namespace PermutationSeed

variable {S : CompilerSignature Roots Code Kinds L}

def relationPerms (P : PermutationSeed S Index) (e : Fin 3) : Equiv.Perm Index :=
  if e = 0 then Equiv.refl Index else if e = 1 then P.H else P.V

def completion (P : PermutationSeed S Index) : Completion S (Kinds × Index) :=
  balancedCompletion S P.code P.physical_code P.relationPerms P.markers
    P.marker_uniform P.one_marker P.marker_cell

theorem completion_balanced (P : PermutationSeed S Index) (k : Kinds) :
    (P.completion.partition.block k).card = Fintype.card Index :=
  assignment_fiber_card S.physical P.code P.physical_code k

theorem completion_full (P : PermutationSeed S Index) (e : Fin 3) :
    (P.completion.matching e).Full := fiberMatching_full S.physical P.code P.physical_code _ _ _

noncomputable def realization {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots) :
    Realization (Kinds × Index) Alphabet :=
  rootedRealization S P.completion.model color (P.completion.model_incidenceLegal hq).matching

theorem J_iff {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (a b : Kinds × Index) :
    (a, b) ∈ (P.realization color hq).J.pairs ↔
      a.1 = S.cellKind ∧ b.1 = S.colorKind ∧ b.2 = a.2 := by
  change (a, b) ∈ S.unionRelation P.completion.model 0 ↔ _
  rw [P.completion.model_unionRelation hq hL]
  simpa [completion, balancedCompletion, relationPerms,
    CompilerSignature.sourceKind, CompilerSignature.targetKind] using
      (mem_fiberMatching S.physical P.code P.physical_code S.cellKind S.colorKind (Equiv.refl Index) a b)

theorem R_iff {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (a b : Kinds × Index) :
    (a, b) ∈ (P.realization color hq).R.pairs ↔
      a.1 = S.colorKind ∧ b.1 = S.cellKind ∧ b.2 = P.H a.2 := by
  change (a, b) ∈ S.unionRelation P.completion.model 1 ↔ _
  rw [P.completion.model_unionRelation hq hL]
  simpa [completion, balancedCompletion, relationPerms,
    CompilerSignature.sourceKind, CompilerSignature.targetKind] using
      (mem_fiberMatching S.physical P.code P.physical_code S.colorKind S.cellKind P.H a b)

theorem S_iff {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (a b : Kinds × Index) :
    (a, b) ∈ (P.realization color hq).S.pairs ↔
      a.1 = S.colorKind ∧ b.1 = S.cellKind ∧ b.2 = P.V a.2 := by
  change (a, b) ∈ S.unionRelation P.completion.model 2 ↔ _
  rw [P.completion.model_unionRelation hq hL]
  simpa [completion, balancedCompletion, relationPerms,
    CompilerSignature.sourceKind, CompilerSignature.targetKind] using
      (mem_fiberMatching S.physical P.code P.physical_code S.colorKind S.cellKind P.V a b)

theorem H_iff {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (a b : Kinds × Index) :
    (P.realization color hq).H a b ↔
      a.1 = S.cellKind ∧ b.1 = S.cellKind ∧ b.2 = P.H a.2 := by
  constructor
  · rintro ⟨c, hj, hr⟩
    obtain ⟨ha, hc, hci⟩ := (P.J_iff color hq hL a c).mp hj
    obtain ⟨hc', hb, hbi⟩ := (P.R_iff color hq hL c b).mp hr
    exact ⟨ha, hb, by simpa only [hci] using hbi⟩
  · rintro ⟨ha, hb, hbi⟩
    refine ⟨(S.colorKind, a.2), (P.J_iff color hq hL a _).mpr ⟨ha, rfl, rfl⟩, ?_⟩
    exact (P.R_iff color hq hL _ b).mpr ⟨rfl, hb, hbi⟩

theorem V_iff {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (a b : Kinds × Index) :
    (P.realization color hq).V a b ↔
      a.1 = S.cellKind ∧ b.1 = S.cellKind ∧ b.2 = P.V a.2 := by
  constructor
  · rintro ⟨c, hj, hs⟩
    obtain ⟨ha, hc, hci⟩ := (P.J_iff color hq hL a c).mp hj
    obtain ⟨hc', hb, hbi⟩ := (P.S_iff color hq hL c b).mp hs
    exact ⟨ha, hb, by simpa only [hci] using hbi⟩
  · rintro ⟨ha, hb, hbi⟩
    refine ⟨(S.colorKind, a.2), (P.J_iff color hq hL a _).mpr ⟨ha, rfl, rfl⟩, ?_⟩
    exact (P.S_iff color hq hL _ b).mpr ⟨rfl, hb, hbi⟩

theorem Lab_iff {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (label : Index → Alphabet)
    (hcolor : ∀ i, color (P.code (S.colorKind, i)) = label i) (a : Kinds × Index) (b : Alphabet) :
    (P.realization color hq).Lab a b ↔ a.1 = S.cellKind ∧ b = label a.2 := by
  have hlabel : ∀ i, (P.realization color hq).label (S.colorKind, i) = label i := by
    intro i
    change decodedLabel S P.completion.model color (S.colorKind, i) = _
    rw [decodedLabel_of_declared S P.completion.model color _ _
      (P.completion.model_declared hq (S.colorKind, i))]
    exact hcolor i
  constructor
  · rintro ⟨c, hj, hb⟩
    obtain ⟨ha, hc, hci⟩ := (P.J_iff color hq hL a c).mp hj
    have hceq : c = (S.colorKind, a.2) := Prod.ext hc hci
    exact ⟨ha, hb.symm.trans (hceq ▸ hlabel a.2)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(S.colorKind, a.2), (P.J_iff color hq hL a _).mpr ⟨ha, rfl, rfl⟩,
      (hlabel a.2).trans hb.symm⟩

theorem path_index {Alphabet : Type*} [Inhabited Alphabet]
    (P : PermutationSeed S Index) (color : Code → Alphabet) (hq : 0 < Fintype.card Roots)
    (hL : 0 < L) (n : ℕ) (a b : Kinds × Index)
    (hp : Path (P.realization color hq).H n a b) : b.2 = (P.H : Index → Index)^[n] a.2 := by
  induction n generalizing a with
  | zero => exact congrArg Prod.snd hp.symm
  | succ n ih =>
    obtain ⟨c, hac, hcb⟩ := hp
    have hc := (P.H_iff color hq hL a c).mp hac
    have hb := ih c hcb
    rw [hc.2.2] at hb
    simpa only [Function.iterate_succ_apply] using hb

/-- Every concrete positive computation clause pulls through the explicit
fiber matchings; no legality of the completed graph is assumed. -/
theorem rootedLegal_of_permutationModel
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ]
    [DecidableEq Γ] [DecidableEq Λ]
    (P : PermutationSeed S Index) (color : Code → LocalSystem.Label Γ Λ)
    (hq : 0 < Fintype.card Roots) (hL : 0 < L)
    (M : Turing.TM0.Machine Γ Λ) (input : List Γ)
    (T : LocalSystem.PermutationModel M input Index) (hH : P.H = T.H) (hV : P.V = T.V)
    (hcolor : ∀ i, color (P.code (S.colorKind, i)) = T.label i)
    (hmarked : ∀ p ∈ P.markers, ∀ d ∈ p, T.MarkedAt d.2) :
    RootedLegal S P.completion.model color (LocalSystem.specification M input) := by
  refine ⟨P.completion.model_incidenceLegal hq, ?_⟩
  change (P.realization color hq).Legal (LocalSystem.specification M input)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x e n y z hxe hxn hey hnz
    obtain ⟨hx, he, hei⟩ := (P.H_iff color hq hL x e).mp hxe
    obtain ⟨hx', hn, hni⟩ := (P.V_iff color hq hL x n).mp hxn
    obtain ⟨he', hy, hyi⟩ := (P.V_iff color hq hL e y).mp hey
    obtain ⟨hn', hz, hzi⟩ := (P.H_iff color hq hL n z).mp hnz
    apply Prod.ext (hy.trans hz.symm)
    rw [hyi, hzi, hei, hni, hH, hV]
    exact (T.commute x.2).symm
  · intro l x r x' al ax ar b hlx hxr hxx' hl hx hr hb
    obtain ⟨hlc, hxc, hxi⟩ := (P.H_iff color hq hL l x).mp hlx
    obtain ⟨hxc', hrc, hri⟩ := (P.H_iff color hq hL x r).mp hxr
    obtain ⟨hxc'', hx'c, hx'i⟩ := (P.V_iff color hq hL x x').mp hxx'
    have hal := ((P.Lab_iff color hq hL T.label hcolor l al).mp hl).2
    have hax := ((P.Lab_iff color hq hL T.label hcolor x ax).mp hx).2
    have har := ((P.Lab_iff color hq hL T.label hcolor r ar).mp hr).2
    have hbb := ((P.Lab_iff color hq hL T.label hcolor x' b).mp hb).2
    have hli : l.2 = P.H.symm x.2 := by
      have hh := congrArg P.H.symm hxi
      simpa only [Equiv.symm_apply_apply] using hh.symm
    apply (LocalSystem.mem_evolution M input al ax ar b).mpr
    rw [hal, hax, har, hbb, hli, hri, hx'i, hH, hV]
    exact T.evolution x.2
  · intro x y a b hxy hx hy
    have hhi := ((P.H_iff color hq hL x y).mp hxy).2.2
    have ha := ((P.Lab_iff color hq hL T.label hcolor x a).mp hx).2
    have hb := ((P.Lab_iff color hq hL T.label hcolor y b).mp hy).2
    apply (LocalSystem.mem_horizontal M input a b).mpr
    rw [ha, hb, hhi, hH]
    exact T.horizontal x.2
  · intro a ha y sy sa hya hy ha'
    have hamark : a ∈ P.markers.biUnion id := by
      change a ∈ S.marks P.completion.model at ha
      rw [P.completion.model_marks hq] at ha
      exact ha
    obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp hamark
    have hm := hmarked p hp a hap
    have hhi := ((P.H_iff color hq hL y a).mp hya).2.2
    have hsy := ((P.Lab_iff color hq hL T.label hcolor y sy).mp hy).2
    have hsa := ((P.Lab_iff color hq hL T.label hcolor a sa).mp ha').2
    have hyi : y.2 = T.H.symm a.2 := by
      have hh := congrArg P.H.symm hhi
      simpa only [Equiv.symm_apply_apply, hH] using hh.symm
    constructor
    · change sy = LocalSystem.Label.leftWall
      rw [hsy, hyi]
      exact hm.1
    · apply (LocalSystem.mem_initial M input sa).mpr
      rw [hsa]
      exact hm.2
  · intro x sx hlab hstart j hj z sz hpath hsz
    have hsx := ((P.Lab_iff color hq hL T.label hcolor x sx).mp hlab).2
    have hsz' := ((P.Lab_iff color hq hL T.label hcolor z sz).mp hsz).2
    have hstart' : LocalSystem.IsStart (T.label x.2) := by
      have hh := (LocalSystem.mem_prefixTrigger M input sx).mp hstart
      simpa only [hsx] using hh
    have hzi := P.path_index color hq hL j x z hpath
    apply (LocalSystem.mem_inputPrefix M input j hj sz).mpr
    rw [hsz', hzi, hH]
    apply T.input_rule x.2 hstart' j
    simpa [LocalSystem.specification] using hj

end PermutationSeed

end TuranUniversality.Weighted
