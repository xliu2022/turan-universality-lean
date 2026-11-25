module

public import TuranUniversality.Reduction.LegalClass
public import TuranUniversality.Selector.Reconstruction
public import TuranUniversality.Hypergraph.Labeled

@[expose] public section

/-! # Concrete forbidden products exclude the completed legal templates -/

namespace TuranUniversality.Reduction

open Construction Weighted Selector Computation Computation.MatchingSystem Turing

set_option backward.isDefEq.respectTransparency false

theorem cliquePacking_block_card (s t : ℕ) (b : Fin s) :
    (blockFiber (Prod.fst : Fin s × Fin t → Fin s) b).card = t := by
  classical
  let e : (blockFiber (Prod.fst : Fin s × Fin t → Fin s) b) ≃ Fin t :=
    { toFun := fun x => x.val.2
      invFun := fun j => ⟨(b, j), by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hx : x.val.1 = b := (mem_blockFiber Prod.fst b x.val).mp x.property
        exact Prod.ext hx.symm rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e

theorem cliquePacking_same_block {s t : ℕ} (x y z : Fin s × Fin t)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyB : x.1 = y.1) (hxzB : x.1 = z.1) :
    {x, y, z} ∈ (RGraph.cliquePacking s t).edges := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  rcases z with ⟨k, c⟩
  dsimp at hxyB hxzB
  subst j
  subst k
  exact RGraph.cliquePacking_triple i a b c
    (fun h => hxy (Prod.ext rfl h)) (fun h => hxz (Prod.ext rfl h))
    (fun h => hyz (Prod.ext rfl h))

variable {Γ Λ : Type*} [DecidableEq Γ] [Fintype Γ] [Inhabited Γ]
  [DecidableEq Λ] [Fintype Λ] [Inhabited Λ]

/-- All constants in the abstract selector theorem are instantiated by the
fixed signature and guard. The only input-dependent hypotheses say that the
cores are forbidden and contain the guard. -/
theorem concrete_product_target_exclusion {F Data : Type*} {X : F → Type*}
    [Fintype F] [Nonempty F] [DecidableEq F]
    [Fintype Data] [DecidableEq Data]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (M : TM0.Machine Γ Λ) (input : List Γ)
    (A : (i : F) → RGraph (X i) 3)
    (hforbidden : ∀ i, ¬ Legal M input (A i))
    (hguard : ∀ i, ∃ f, (fixedGuard (alphabetSize Γ Λ)).IsEmbedding (A i) f)
    (target : RootedModel (RootLabels (alphabetSize Γ Λ)) Data)
    (hlegal : RootedLegal (compilerSignature (LocalSystem.Label Γ Λ)) target
      (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ)))
      (LocalSystem.specification M input))
    (hdeclared : ∀ d, ∃ c, (compilerSignature (LocalSystem.Label Γ Λ)).codes.Declared target d c) :
    (RGraph.product fun i => (A i).pairExtension).HomFree target.toRGraph := by
  classical
  let a := alphabetSize Γ Λ
  let q := rootNumber (chosenParameter a)
  let t := guardCliqueSize a
  let s := guardCopies q t
  have hsizes := guard_sizes q t (guardCliqueSize_ge a) (rootNumber_guard_large a)
  letI : Nonempty (Fin s) := ⟨⟨0, by dsimp [s]; omega⟩⟩
  letI : Nonempty (Fin t) := ⟨⟨0, by have := guardCliqueSize_ge a; dsimp [t]; omega⟩⟩
  letI : Nonempty (LabelCodes (LocalSystem.Label Γ Λ)) := ⟨Sum.inr (Sum.inl ())⟩
  have hq : (0 : ℝ) < q := by
    have h := rootNumber_large (chosenParameter a)
    have hm := physicalCount_ge (chosenParameter a)
    exact_mod_cast (show 0 < q by dsimp [q]; omega)
  have hn : 1048576 ≤ Fintype.card (Fin s × Fin t) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, s] using hsizes.2.2.2.2.2
  have hnq : 19 * (q : ℝ) / 20 < Fintype.card (Fin s × Fin t) := by
    have hlt : ((t * (s - 1) : ℕ) : ℝ) < (t * s : ℕ) := by
      exact_mod_cast hsizes.2.2.2.1
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
      hsizes.2.2.1.trans hlt
  choose guard hguard' using hguard
  apply Selector.product_target_exclusion
    (compilerSignature (LocalSystem.Label Γ Λ))
    (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ)))
    (LocalSystem.specification M input) A hforbidden target hlegal hdeclared
    (blockLabel (chosenBlocks a).half) (4 * codeCount a) (by have := codeCount_pos a; omega)
    (fun b => ((chosenBlocks a).block_size b).le) ?_ (q : ℝ) hq ?_ hn hnq
    (guardProfiles a) t (by have := codeCount_pos a; unfold guardProfiles; omega)
    (by rfl) ?_ Prod.fst (cliquePacking_block_card s t) guard (fun i => (hguard' i).1) ?_
  · intro c r u hpair
    exact compilerSignature_pair_inside (LocalSystem.Label Γ Λ) c {r, u} hpair
      (by simp) (by simp)
  · rw [rootLabels_card]
    exact le_rfl
  · rw [labelCodes_card]
    change 3 * codeCount a + 4 * codeCount a ≤ guardProfiles a
    unfold guardProfiles
    omega
  · intro i x y z hxy hxz hyz hxyB hxzB
    have he := (hguard' i).2 _ (cliquePacking_same_block x y z hxy hxz hyz hxyB hxzB)
    simpa using he

theorem singletonProduct_target_exclusion {Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (M : TM0.Machine Γ Λ) (input : List Γ)
    (F : Finset (FiniteGraph 3)) (hF : F.Nonempty)
    (hforbidden : ∀ A ∈ F, ¬ Legal M input A.2)
    (hguard : ∀ A ∈ F, ∃ f, (fixedGuard (alphabetSize Γ Λ)).IsEmbedding A.2 f)
    (target : RootedModel (RootLabels (alphabetSize Γ Λ)) Data)
    (hlegal : RootedLegal (compilerSignature (LocalSystem.Label Γ Λ)) target
      (colorLabel (LocalSystem.background (Γ := Γ) (Λ := Λ)))
      (LocalSystem.specification M input))
    (hdeclared : ∀ d, ∃ c, (compilerSignature (LocalSystem.Label Γ Λ)).codes.Declared target d c) :
    (FiniteGraph.singletonProduct F).2.HomFree target.toRGraph := by
  classical
  letI : Nonempty F := ⟨⟨hF.choose, hF.choose_spec⟩⟩
  apply (FiniteGraph.ofRGraph_homFree _ _).mpr
  exact concrete_product_target_exclusion M input (fun A : F => A.val.2)
    (fun A => hforbidden A.val A.property) (fun A => hguard A.val A.property)
    target hlegal hdeclared

end TuranUniversality.Reduction
