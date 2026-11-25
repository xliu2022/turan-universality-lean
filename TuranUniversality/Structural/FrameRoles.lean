module

public import TuranUniversality.Structural.FrameBalance

@[expose] public section

/-! # Recovering roles from an ordinary frame homomorphism -/

open scoped BigOperators

namespace TuranUniversality.Structural.Frame

open Cube Support

variable {V : Type*} [DecidableEq V] {b t : ℕ}
  {Ω : Finset (Word b)} {pools : Label → Finset (Word b)} {R : RecordSystem V}
  {f : Compiled.Vertex b t (Fin 5) → Compiled.Vertex b t V}

theorem target_susp_member (e : Finset (Compiled.Vertex b t V))
    (he : e ∈ (Compiled.graph t pools R).edges) (j : Fin t) : Sum.inl j ∈ e := by
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (Compiled.mem_graph pools R e).mp he
  simp

/-- Every target suspension has a preimage in the common intersection. -/
theorem suspension_preimage (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) (j : Fin t) :
    ∃ i : Fin t, f (.inl i) = .inl j := by
  have hinj := hom_injective hzero hf
  obtain ⟨e, he⟩ := edges_nonempty (t := t) hzero
  obtain ⟨u, hu, huj⟩ := Finset.mem_image.mp (target_susp_member (e.image f) (hf e he) j)
  have huall : ∀ d ∈ (graph b t Ω).edges, u ∈ d := by
    intro d hd
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp (target_susp_member (d.image f) (hf d hd) j)
    have huv : u = v := hinj (huj.trans hvj.symm)
    exact huv ▸ hv
  obtain ⟨i, rfl⟩ := (common_intersection hzero u).mp huall
  exact ⟨i, huj⟩

/-- The entire suspension set is permuted, including the case `t = 0`. -/
theorem suspension_roles (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) :
    ∃ σ : Equiv.Perm (Fin t), ∀ i, f (.inl i) = .inl (σ i) := by
  classical
  choose pre hpre using suspension_preimage hzero hf
  have hp : Function.Injective pre := by
    intro i j hij
    have h := (hpre i).symm.trans ((congrArg (fun k => f (.inl k)) hij).trans (hpre j))
    exact Sum.inl.inj h
  let e : Equiv.Perm (Fin t) := Equiv.ofBijective pre ⟨hp, Finite.surjective_of_injective hp⟩
  refine ⟨e.symm, ?_⟩
  intro i
  have hi : pre (e.symm i) = i := e.apply_symm_apply i
  simpa only [hi] using hpre (e.symm i)

theorem image_susp_iff (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f)
    (v : Compiled.Vertex b t (Fin 5)) :
    (∃ j : Fin t, f v = .inl j) ↔ ∃ i : Fin t, v = .inl i := by
  obtain ⟨σ, hσ⟩ := suspension_roles hzero hf
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨σ.symm j, hom_injective hzero hf ?_⟩
    rw [hj, hσ, Equiv.apply_symm_apply]
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, hσ i⟩

def blockIndicator (i : Fin b) : Compiled.Vertex b t V → ℕ
  | .inr (.inl v) => if v.1 = i then 1 else 0
  | _ => 0

theorem blockIndicator_eq_one (i : Fin b) (v : Compiled.Vertex b t V) :
    blockIndicator i v = 1 ↔ ∃ a : Fin 5, v = .inr (.inl ⟨i, a⟩) := by
  cases v with
  | inl j => simp [blockIndicator]
  | inr v =>
    cases v with
    | inr a => simp [blockIndicator]
    | inl v =>
      rcases v with ⟨j, a⟩
      by_cases h : j = i
      · subst j; simp [blockIndicator]
      · simp [blockIndicator, h]

theorem blockIndicator_values (i : Fin b) (v : Compiled.Vertex b t V) :
    blockIndicator i v = 0 ∨ blockIndicator i v = 1 := by
  cases v with
  | inl j => exact Or.inl rfl
  | inr v =>
    cases v with
    | inr a => exact Or.inl rfl
    | inl v => by_cases h : v.1 = i <;> simp [blockIndicator, h]

theorem target_block_sum (i : Fin b) (e : Finset (Compiled.Vertex b t V))
    (he : e ∈ (Compiled.graph t pools R).edges) :
    (∑ v ∈ e, blockIndicator i v) = 3 := by
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (Compiled.mem_graph pools R e).mp he
  obtain ⟨w, hw, hZw⟩ := Finset.mem_biUnion.mp hZ
  obtain ⟨a, rfl⟩ := (mem_wordGraph w Z).mp hZw
  rw [Compiled.edge_sum, choiceEdge, joinRows, Finset.sum_sigma]
  have hrow (j : Fin b) : (∑ v ∈ (a j).val,
      blockIndicator i (.inr (.inl ⟨j, v⟩) : Compiled.Vertex b t V)) =
        if j = i then 3 else 0 := by
    by_cases h : j = i
    · simp [blockIndicator, h, (blockGraph w j).uniform _ (a j).property]
    · simp [blockIndicator, h]
  change (∑ _i : Fin t, 0) +
    (∑ j : Fin b, ∑ v ∈ (a j).val,
      blockIndicator i (.inr (.inl ⟨j, v⟩) : Compiled.Vertex b t V)) + (∑ _v ∈ X, 0) = 3
  simp only [hrow, Finset.sum_const_zero, zero_add, add_zero]
  simp

theorem pullback_block_sum (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) (i : Fin b)
    (e : Finset (Compiled.Vertex b t (Fin 5))) (he : e ∈ (graph b t Ω).edges) :
    (∑ v ∈ e, blockIndicator i (f v)) = 3 := by
  have h := target_block_sum i (e.image f) (hf e he)
  rw [Finset.sum_image (fun _ _ _ _ hv => hom_injective hzero hf hv)] at h
  exact h

theorem block_membership_constant (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) (j : Fin b) :
    ∀ (i : Fin b) (a : Fin 5),
      blockIndicator j (f (.inr (.inl ⟨i, a⟩))) = blockIndicator j (f (.inr (.inl ⟨i, 0⟩))) :=
  block_constant hzero _ 3 (pullback_block_sum hzero hf j)

theorem data_membership_constant (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) (j : Fin b) :
    ∀ a : Fin 5,
      blockIndicator j (f (.inr (.inr a))) = blockIndicator j (f (.inr (.inr 0))) :=
  data_constant hzero _ 3 (pullback_block_sum hzero hf j)

/-- The five source data points cannot all enter a block with only three edge positions. -/
theorem data_outside_blocks (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) (j : Fin b) (a : Fin 5) :
    blockIndicator j (f (.inr (.inr a))) = 0 := by
  have hc := data_membership_constant hzero hf j
  have h := pullback_block_sum hzero hf j _
    (edge_mem (t := t) hzero (baseChoice b) (X := {0, 1, 2, 3}) (by decide))
  rw [Compiled.edge_sum] at h
  have hdata : (∑ v ∈ ({0, 1, 2, 3} : Finset (Fin 5)),
      blockIndicator j (f (.inr (.inr v)))) = 4 * blockIndicator j (f (.inr (.inr 0))) := by
    simp only [hc, Finset.sum_const, nsmul_eq_mul]
    norm_num
  rw [hdata] at h
  rw [hc a]
  omega

theorem data_roles (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) :
    ∃ d : Fin 5 → V, Function.Injective d ∧ ∀ a, f (.inr (.inr a)) = .inr (.inr (d a)) := by
  classical
  have hd (a : Fin 5) : ∃ v : V, f (.inr (.inr a)) = .inr (.inr v) := by
    cases he : f (.inr (.inr a)) with
    | inl j =>
      have h := (image_susp_iff hzero hf (.inr (.inr a))).mp ⟨j, he⟩
      simp at h
    | inr v =>
      cases v with
      | inr v => exact ⟨v, rfl⟩
      | inl v =>
        have h := data_outside_blocks hzero hf v.1 a
        simp [he, blockIndicator] at h
  choose d hd using hd
  refine ⟨d, ?_, hd⟩
  intro a c hac
  have h := hom_injective hzero hf ((hd a).trans ((congrArg (fun v =>
    (Sum.inr (Sum.inr v) : Compiled.Vertex b t V)) hac).trans (hd c).symm))
  exact Sum.inr.inj (Sum.inr.inj h)

/-- Each target block receives one entire source block. -/
theorem source_block_for_target (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) (j : Fin b) :
    ∃ i : Fin b, ∀ a : Fin 5, ∃ c : Fin 5,
      f (.inr (.inl ⟨i, a⟩)) = .inr (.inl ⟨j, c⟩) := by
  obtain ⟨σ, hσ⟩ := suspension_roles hzero hf
  have hc := block_membership_constant hzero hf j
  have hex : ∃ i : Fin b, blockIndicator j (f (.inr (.inl ⟨i, 0⟩))) = 1 := by
    by_contra! hn
    have hz (i : Fin b) : blockIndicator j (f (.inr (.inl ⟨i, 0⟩))) = 0 :=
      (blockIndicator_values j _).resolve_right (hn i)
    have h := pullback_block_sum hzero hf j _
      (edge_mem (t := t) hzero (baseChoice b) (X := {0, 1, 2, 3}) (by decide))
    rw [Compiled.edge_sum, choiceEdge, joinRows, Finset.sum_sigma] at h
    have hs (i : Fin t) : blockIndicator j (f (.inl i)) = 0 := by
      rw [hσ]; rfl
    have hb (i : Fin b) (a : Fin 5) : blockIndicator j (f (.inr (.inl ⟨i, a⟩))) = 0 :=
      (hc i a).trans (hz i)
    have hd (a : Fin 5) : blockIndicator j (f (.inr (.inr a))) = 0 :=
      data_outside_blocks hzero hf j a
    simp only [hs, hb, hd, Finset.sum_const_zero, zero_add] at h
    contradiction
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  intro a
  exact (blockIndicator_eq_one j _).mp ((hc i a).trans hi)

/-- All source blocks are carried bijectively to all target blocks, with genuine
five-point bijections in each block. -/
theorem block_roles (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) :
    ∃ π : Equiv.Perm (Fin b), ∃ τ : Fin b → Equiv.Perm (Fin 5),
      ∀ (i : Fin b) (a : Fin 5),
        f (.inr (.inl ⟨i, a⟩)) = .inr (.inl ⟨π i, τ i a⟩) := by
  classical
  choose pre hpre using source_block_for_target hzero hf
  have hpre_inj : Function.Injective pre := by
    intro j k hjk
    obtain ⟨a, ha⟩ := hpre j 0
    obtain ⟨c, hc⟩ := hpre k 0
    have he : (Sum.inr (Sum.inl ⟨j, a⟩) : Compiled.Vertex b t V) = .inr (.inl ⟨k, c⟩) := by
      rw [← ha, ← hc, hjk]
    exact congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj he))
  let e : Equiv.Perm (Fin b) :=
    Equiv.ofBijective pre ⟨hpre_inj, Finite.surjective_of_injective hpre_inj⟩
  have hm (i : Fin b) (a : Fin 5) : ∃ c : Fin 5,
      f (.inr (.inl ⟨i, a⟩)) = .inr (.inl ⟨e.symm i, c⟩) := by
    have hi : pre (e.symm i) = i := e.apply_symm_apply i
    simpa only [hi] using hpre (e.symm i) a
  choose row hrow using hm
  have hrow_inj (i : Fin b) : Function.Injective (row i) := by
    intro a c hac
    have hf' : f (.inr (.inl ⟨i, a⟩)) = f (.inr (.inl ⟨i, c⟩)) := by
      rw [hrow, hrow, hac]
    have he := Sum.inl.inj (Sum.inr.inj (hom_injective hzero hf hf'))
    exact eq_of_heq (Sigma.mk.inj he).2
  let τ (i : Fin b) : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective (row i) ⟨hrow_inj i, Finite.surjective_of_injective (hrow_inj i)⟩
  exact ⟨e.symm, τ, hrow⟩

/-- Complete role recovery for every ordinary homomorphism of the actual frame. -/
theorem roles (hzero : ∅ ∈ Ω)
    (hf : (graph b t Ω).IsHom (Compiled.graph t pools R) f) :
    ∃ σ : Equiv.Perm (Fin t), ∃ π : Equiv.Perm (Fin b),
      ∃ τ : Fin b → Equiv.Perm (Fin 5), ∃ d : Fin 5 → V,
        Function.Injective d ∧
        (∀ i, f (.inl i) = .inl (σ i)) ∧
        (∀ (i : Fin b) (a : Fin 5), f (.inr (.inl ⟨i, a⟩)) = .inr (.inl ⟨π i, τ i a⟩)) ∧
        (∀ a, f (.inr (.inr a)) = .inr (.inr (d a))) := by
  obtain ⟨σ, hσ⟩ := suspension_roles hzero hf
  obtain ⟨π, τ, hτ⟩ := block_roles hzero hf
  obtain ⟨d, hd, hdf⟩ := data_roles hzero hf
  exact ⟨σ, π, τ, d, hd, hσ, hτ, hdf⟩

end TuranUniversality.Structural.Frame
