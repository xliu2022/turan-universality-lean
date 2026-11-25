module

public import TuranUniversality.Reduction.TargetExclusion
public import TuranUniversality.Selector.BasisNonempty
public import TuranUniversality.Weighted.ConcreteWitness
public import TuranUniversality.Density.ProductUpper
public import TuranUniversality.Density.LowerBridge

/-! # The ordinary Turán-density dichotomy for the actual singleton graph

The forbidden cores are the bounded, guarded obstructions to the concrete
partial-rooting class.  Their private-pair product is one finite three-graph.
The upper bound uses the proved finite-support compression and ordinary
sampling bridge.  Both lower bounds use actual legal completed templates with
explicit natural clone counts.
-/

@[expose] public section

namespace TuranUniversality.Reduction

open Construction Weighted Selector TuranUniversality.Computation
  TuranUniversality.Computation.MatchingSystem Turing
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {Γ Λ : Type*} [DecidableEq Γ] [Fintype Γ] [Inhabited Γ]
  [DecidableEq Λ] [Fintype Λ] [Inhabited Λ]

noncomputable def guardGraph (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] : FiniteGraph 3 :=
  FiniteGraph.ofRGraph (fixedGuard (alphabetSize Γ Λ))

noncomputable def forbiddenCores (M : TM0.Machine Γ Λ) (input : List Γ) :
    Finset (FiniteGraph 3) :=
  guardedAdmissibleBasis (compilerSignature (LocalSystem.Label Γ Λ))
    (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ)))
    (LocalSystem.specification M input) (guardGraph Γ Λ)

noncomputable def forbiddenGraph (M : TM0.Machine Γ Λ) (input : List Γ) : FiniteGraph 3 :=
  FiniteGraph.singletonProduct (forbiddenCores M input)

theorem fixedGuard_has_edges (A : ℕ) : (fixedGuard A).edges.Nonempty := by
  have ht := guardCliqueSize_ge A
  have hs := (guard_sizes (rootNumber (chosenParameter A)) (guardCliqueSize A)
    ht (rootNumber_guard_large A)).1
  let i : Fin (guardCopies (rootNumber (chosenParameter A)) (guardCliqueSize A)) := ⟨0, by omega⟩
  let a : Fin (guardCliqueSize A) := ⟨0, by omega⟩
  let b : Fin (guardCliqueSize A) := ⟨1, by omega⟩
  let c : Fin (guardCliqueSize A) := ⟨2, by omega⟩
  exact ⟨_, RGraph.cliquePacking_triple i a b c
    (by simp [a, b, Fin.ext_iff]) (by simp [a, c, Fin.ext_iff])
    (by simp [b, c, Fin.ext_iff])⟩

omit [DecidableEq Γ] [DecidableEq Λ] [Inhabited Γ] [Inhabited Λ] in
theorem guardGraph_has_edges : (guardGraph Γ Λ).2.edges.Nonempty :=
  FiniteGraph.ofRGraph_edges_nonempty _ (fixedGuard_has_edges _)

theorem forbiddenCores_illegal (M : TM0.Machine Γ Λ) (input : List Γ)
    {A : FiniteGraph 3} (hA : A ∈ forbiddenCores M input) : ¬ Legal M input A.2 :=
  (guardedAdmissibleBasis_contains_guard _ _ _ _ hA).1

theorem forbiddenCores_contain_guard (M : TM0.Machine Γ Λ) (input : List Γ)
    {A : FiniteGraph 3} (hA : A ∈ forbiddenCores M input) :
    ∃ f, (fixedGuard (alphabetSize Γ Λ)).IsEmbedding A.2 f := by
  obtain ⟨f, hf⟩ := (guardedAdmissibleBasis_contains_guard _ _ _ _ hA).2
  exact ⟨_, hf.comp (FiniteGraph.embedding_ofRGraph _)⟩

theorem forbiddenCores_has_edges (M : TM0.Machine Γ Λ) (input : List Γ)
    {A : FiniteGraph 3} (hA : A ∈ forbiddenCores M input) : A.2.edges.Nonempty :=
  guardedAdmissibleBasis_has_edges _ _ _ _ guardGraph_has_edges hA

theorem forbiddenCores_nonempty (M : TM0.Machine Γ Λ) (input : List Γ) :
    (forbiddenCores M input).Nonempty := guardedAdmissibleBasis_nonempty _ _ _ _

theorem forbiddenGraph_has_edges (M : TM0.Machine Γ Λ) (input : List Γ) :
    (forbiddenGraph M input).2.edges.Nonempty :=
  FiniteGraph.singletonProduct_edges_nonempty _ (forbiddenCores_nonempty M input)
    (fun _ hA => forbiddenCores_has_edges M input hA)

theorem forbiddenCores_free_legal (M : TM0.Machine Γ Λ) (input : List Γ)
    (n : ℕ) (G : RGraph (Fin n) 3)
    (hfree : ∀ A ∈ forbiddenCores M input, ¬ A.Contains ⟨n, G⟩) :
    GuardedLegal M input G := by
  have h := (guardedAdmissibleBasis_spec (compilerSignature (LocalSystem.Label Γ Λ))
    (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ)))
    (LocalSystem.specification M input) (guardGraph Γ Λ) ⟨n, G⟩).mpr hfree
  rcases h with h | h
  · exact Or.inl h
  · right
    rintro ⟨f, hf⟩
    exact h ⟨_, hf.comp (FiniteGraph.ofRGraph_embedding _)⟩

/-- The unmarked completed template gives the exact rational lower bound
for every input, independently of its execution. -/
theorem forbiddenGraph_density_lower (M : TM0.Machine Γ Λ) (input : List Γ) :
    (threshold (alphabetSize Γ Λ) : ℝ) ≤ turanDensity (forbiddenGraph M input).2 := by
  have hfree := singletonProduct_target_exclusion M input (forbiddenCores M input)
    (forbiddenCores_nonempty M input) (fun _ hA => forbiddenCores_illegal M input hA)
    (fun _ hA => forbiddenCores_contain_guard M input hA)
    (ConcreteWitness.baselineCompletion (Γ := Γ) (Λ := Λ)).model
    (ConcreteWitness.baselineCompletion_legal M input)
    ConcreteWitness.baselineCompletion_declared
  have h := turanDensity_lower_integer_weights (forbiddenGraph M input).2
    (Finset.card_pos.mpr (forbiddenGraph_has_edges M input))
    ConcreteWitness.baselineCompletion.model.toRGraph hfree ConcreteWitness.baselineSizes
    ConcreteWitness.baselineSizes_pos
  rw [ConcreteWitness.baselineCompletion_value] at h
  exact h

/-- Every compressed core-free support belongs to the proved guarded legal
class, which supplies the upper bound when the computation does not halt. -/
theorem forbiddenGraph_density_upper (M : TM0.Machine Γ Λ) (input : List Γ)
    (hn : ¬ (TM0.eval M input).Dom) :
    turanDensity (forbiddenGraph M input).2 ≤ (threshold (alphabetSize Γ Λ) : ℝ) := by
  classical
  let F := forbiddenCores M input
  let : Nonempty F := ⟨⟨(forbiddenCores_nonempty M input).choose,
    (forbiddenCores_nonempty M input).choose_spec⟩⟩
  apply product_turanDensity_upper (fun A : F => A.val.2)
    (fun A => forbiddenCores_has_edges M input A.property) _
    (by exact_mod_cast (threshold_bounds (alphabetSize Γ Λ)).1.le)
  intro n G x hx hcores
  apply GuardedLegal.nonhalting_bound G ?_ hn x hx
  apply forbiddenCores_free_legal M input n G
  intro A hA
  exact hcores ⟨A, hA⟩

theorem forbiddenGraph_density_eq_of_nonhalting (M : TM0.Machine Γ Λ) (input : List Γ)
    (hn : ¬ (TM0.eval M input).Dom) :
    turanDensity (forbiddenGraph M input).2 = (threshold (alphabetSize Γ Λ) : ℝ) :=
  le_antisymm (forbiddenGraph_density_upper M input hn) (forbiddenGraph_density_lower M input)

/-- A finite halting tableau yields three identical components and one
marker edge. Its explicit natural clone sizes strictly beat the baseline. -/
theorem forbiddenGraph_density_strict_of_halting (M : TM0.Machine Γ Λ) (input : List Γ)
    (hi : input ≠ []) (hh : (TM0.eval M input).Dom) :
    (threshold (alphabetSize Γ Λ) : ℝ) < turanDensity (forbiddenGraph M input).2 := by
  obtain ⟨p, m, G, sizes, hdeclared, hlegal, hsizes, hvalue⟩ :=
    ConcreteWitness.halting_witness M input hi hh
  have hfree := singletonProduct_target_exclusion M input (forbiddenCores M input)
    (forbiddenCores_nonempty M input) (fun _ hA => forbiddenCores_illegal M input hA)
    (fun _ hA => forbiddenCores_contain_guard M input hA) G hlegal hdeclared
  exact hvalue.trans_le (turanDensity_lower_integer_weights (forbiddenGraph M input).2
    (Finset.card_pos.mpr (forbiddenGraph_has_edges M input)) G.toRGraph hfree sizes hsizes)

/-- The equality side of the ordinary Turán-density universality statement. -/
theorem forbiddenGraph_density_eq_iff (M : TM0.Machine Γ Λ) (input : List Γ) (hi : input ≠ []) :
    turanDensity (forbiddenGraph M input).2 = (threshold (alphabetSize Γ Λ) : ℝ) ↔
      ¬ (TM0.eval M input).Dom := by
  constructor
  · intro heq hh
    have hlt := forbiddenGraph_density_strict_of_halting M input hi hh
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · exact forbiddenGraph_density_eq_of_nonhalting M input

/-- The strict side of the ordinary Turán-density universality statement. -/
theorem forbiddenGraph_density_strict_iff (M : TM0.Machine Γ Λ) (input : List Γ) (hi : input ≠ []) :
    (threshold (alphabetSize Γ Λ) : ℝ) < turanDensity (forbiddenGraph M input).2 ↔
      (TM0.eval M input).Dom := by
  constructor
  · intro hlt
    by_contra hn
    rw [forbiddenGraph_density_eq_of_nonhalting M input hn] at hlt
    exact lt_irrefl _ hlt
  · exact forbiddenGraph_density_strict_of_halting M input hi

end TuranUniversality.Reduction
