module

public import TuranUniversality.Density.FiniteSubfamilyInf
public import TuranUniversality.Density.HomomorphicClosure

@[expose] public section

/-! # Homomorphic closure of an arbitrary forbidden family

Images retain all image vertices, including isolated vertices. Every finite
part of the closure is covered by the closure of a finite part of the original
family. This cofinality and the finite-subfamily infimum prove preservation
of the ordinary Turán density, without a finiteness assumption on the family.
-/

namespace TuranUniversality.SetFamily

universe u
variable {r : ℕ}

def homomorphicClosure (F : Set (FiniteGraph r)) : Set (FiniteGraph r) :=
  {Q | ∃ A ∈ F, IsHomomorphicImage A Q}

@[simp] theorem mem_homomorphicClosure (F : Set (FiniteGraph r)) (Q : FiniteGraph r) :
    Q ∈ homomorphicClosure F ↔ ∃ A ∈ F, IsHomomorphicImage A Q := Iff.rfl

theorem subset_homomorphicClosure (F : Set (FiniteGraph r)) : F ⊆ homomorphicClosure F :=
  fun A hA => ⟨A, hA, IsHomomorphicImage.refl A⟩

theorem homomorphicClosure_mono {F H : Set (FiniteGraph r)} (h : F ⊆ H) :
    homomorphicClosure F ⊆ homomorphicClosure H := by
  rintro Q ⟨A, hA, hi⟩
  exact ⟨A, h hA, hi⟩

theorem homomorphicImage_order_le {A Q : FiniteGraph r} (h : IsHomomorphicImage A Q) :
    Q.1 ≤ A.1 := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_surjective f hf

theorem homomorphicClosure_finset (F : Finset (FiniteGraph r)) :
    (TuranUniversality.homomorphicClosure F : Set (FiniteGraph r)) =
      homomorphicClosure (F : Set (FiniteGraph r)) := by
  classical
  ext Q
  constructor
  · intro hQ
    exact (TuranUniversality.mem_homomorphicClosure F Q).mp hQ |>.2
  · rintro ⟨A, hA, hi⟩
    exact (TuranUniversality.mem_homomorphicClosure F Q).mpr
      ⟨(homomorphicImage_order_le hi).trans (Finset.le_sup (f := fun A => A.1) hA),
        A, hA, hi⟩

theorem free_homomorphicClosure_iff {W : Type u} [DecidableEq W]
    (F : Set (FiniteGraph r)) (G : RGraph W r) :
    Free (homomorphicClosure F) G ↔ HomFree F G := by
  constructor
  · intro h A hA
    rintro ⟨f, hf⟩
    obtain ⟨Q, _, hQ, hemb⟩ := exists_homomorphicImage_embedding A G hf
    exact h Q ⟨A, hA, hQ⟩ hemb
  · intro h Q hQ
    rintro ⟨g, hg⟩
    obtain ⟨A, hA, hi⟩ := hQ
    obtain ⟨f, hf⟩ := hi.exists_hom
    exact h A hA ⟨g ∘ f, hg.isHom.comp hf⟩

theorem homFree_homomorphicClosure_iff {W : Type u} [DecidableEq W]
    (F : Set (FiniteGraph r)) (G : RGraph W r) :
    HomFree (homomorphicClosure F) G ↔ HomFree F G := by
  constructor
  · intro h
    exact h.mono (subset_homomorphicClosure F)
  · intro h Q hQ
    rintro ⟨g, hg⟩
    obtain ⟨A, hA, hi⟩ := hQ
    obtain ⟨f, hf⟩ := hi.exists_hom
    exact h A hA ⟨g ∘ f, hg.comp hf⟩

theorem homomorphicClosure_has_edges (F : Set (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    ∀ Q ∈ homomorphicClosure F, Q.2.edges.Nonempty := by
  rintro Q ⟨A, hA, f, _, heq⟩
  rw [heq]
  exact (hedges A hA).image _

/-- A finite collection of image obstructions uses only finitely many sources. -/
theorem finite_subset_homomorphicClosure (F : Set (FiniteGraph r))
    (E : Finset (FiniteGraph r)) (hE : (E : Set (FiniteGraph r)) ⊆ homomorphicClosure F) :
    ∃ H : Finset (FiniteGraph r), (H : Set (FiniteGraph r)) ⊆ F ∧
      E ⊆ TuranUniversality.homomorphicClosure H := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨∅, by simp, Finset.empty_subset _⟩
  | @insert Q E hnot ih =>
    obtain ⟨A, hA, hi⟩ := hE (Finset.mem_insert_self Q E)
    obtain ⟨H, hH, hEH⟩ := ih (fun B hB => hE (Finset.mem_insert_of_mem hB))
    refine ⟨insert A H, ?_, ?_⟩
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hA
      · exact hH hB
    · intro B hB
      have hmem : B ∈ homomorphicClosure (insert A H : Set (FiniteGraph r)) := by
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact ⟨A, Set.mem_insert A H, hi⟩
        · apply homomorphicClosure_mono (F := (H : Set (FiniteGraph r)))
            (fun _ h => Set.mem_insert_of_mem _ h)
          rw [← homomorphicClosure_finset]
          exact hEH hB
      have hmem' : B ∈ homomorphicClosure ((insert A H : Finset (FiniteGraph r)) :
          Set (FiniteGraph r)) := by simpa only [Finset.coe_insert] using hmem
      rw [← homomorphicClosure_finset (insert A H)] at hmem'
      exact hmem'

noncomputable section

/-- Homomorphic closure preserves the actual ordinary density for every
positive uniformity, including edgeless forbidden members. -/
theorem turanDensity_homomorphicClosure (F : Set (FiniteGraph r)) (hr : 0 < r) :
    turanDensity (homomorphicClosure F) = turanDensity F := by
  apply le_antisymm (turanDensity_antitone (subset_homomorphicClosure F))
  rw [turanDensity_eq_sInf_finite (homomorphicClosure F)]
  apply le_csInf (finiteDensityValues_nonempty _)
  rintro z ⟨E, hE, rfl⟩
  obtain ⟨H, hH, hEH⟩ := finite_subset_homomorphicClosure F E hE
  calc
    turanDensity F ≤ familyTuranDensity H := turanDensity_le_finite F H hH
    _ = familyTuranDensity (TuranUniversality.homomorphicClosure H) :=
      (familyTuranDensity_homomorphicClosure H hr).symm
    _ ≤ familyTuranDensity E := by
      simpa only [turanDensity_finset] using
        turanDensity_antitone
          (show (E : Set (FiniteGraph r)) ⊆ TuranUniversality.homomorphicClosure H from hEH)

end
end TuranUniversality.SetFamily
