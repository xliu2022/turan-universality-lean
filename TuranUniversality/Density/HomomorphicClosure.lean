module

public import TuranUniversality.Density.FiniteApproximation
public import TuranUniversality.Density.FamilyVariational
public import TuranUniversality.Density.DegenerateFamily

@[expose] public section

/-! # The finite family of homomorphic images

Every homomorphism from a finite graph factors through its finite vertex
image, with an exact image edge set, followed by an embedding. This yields
an explicit finite homomorphic closure, the equality of its ordinary free
class with the original hom-free class, and equality of ordinary densities.
-/

namespace TuranUniversality

universe u

variable {r : ℕ}

/-- A homomorphic image includes all vertices and exactly the edge images.
In particular, it does not silently remove isolated vertices. -/
def IsHomomorphicImage (A Q : FiniteGraph r) : Prop :=
  ∃ f : Fin A.1 → Fin Q.1, Function.Surjective f ∧
    Q.2.edges = A.2.edges.image (fun e => e.image f)

instance (A Q : FiniteGraph r) : Decidable (IsHomomorphicImage A Q) :=
  inferInstanceAs (Decidable (∃ f : Fin A.1 → Fin Q.1, Function.Surjective f ∧
    Q.2.edges = A.2.edges.image (fun e => e.image f)))

theorem IsHomomorphicImage.exists_hom {A Q : FiniteGraph r}
    (h : IsHomomorphicImage A Q) : ∃ f, A.2.IsHom Q.2 f := by
  obtain ⟨f, _, heq⟩ := h
  refine ⟨f, ?_⟩
  intro e he
  rw [heq]
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem IsHomomorphicImage.refl (A : FiniteGraph r) : IsHomomorphicImage A A := by
  refine ⟨id, Function.surjective_id, ?_⟩
  simp

/-- All labelled homomorphic images of members of `F`. Their vertex orders
are bounded by the maximum source order, so this is a genuine finite set. -/
def homomorphicClosure (F : Finset (FiniteGraph r)) : Finset (FiniteGraph r) :=
  (FiniteGraph.bounded r (F.sup (fun A => A.1))).filter
    (fun Q => ∃ A ∈ F, IsHomomorphicImage A Q)

@[simp] theorem mem_homomorphicClosure (F : Finset (FiniteGraph r))
    (Q : FiniteGraph r) :
    Q ∈ homomorphicClosure F ↔
      Q.1 ≤ F.sup (fun A => A.1) ∧ ∃ A ∈ F, IsHomomorphicImage A Q := by
  simp [homomorphicClosure]

theorem mem_homomorphicClosure_of_mem (F : Finset (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) : A ∈ homomorphicClosure F := by
  apply (mem_homomorphicClosure F A).mpr
  exact ⟨Finset.le_sup (f := fun B : FiniteGraph r => B.1) hA,
    A, hA, IsHomomorphicImage.refl A⟩

/-- Factor an arbitrary homomorphism through a labelled finite image. -/
theorem exists_homomorphicImage_embedding {W : Type u} [DecidableEq W]
    (A : FiniteGraph r) (G : RGraph W r) {f : Fin A.1 → W}
    (hf : A.2.IsHom G f) :
    ∃ Q : FiniteGraph r, Q.1 ≤ A.1 ∧ IsHomomorphicImage A Q ∧
      ∃ j, Q.2.IsEmbedding G j := by
  classical
  let S : Finset W := Finset.univ.image f
  let f₀ : Fin A.1 → S := fun a =>
    ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨w, hw⟩
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hw
    exact ⟨a, Subtype.ext ha⟩
  let e : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let q : Fin A.1 → Fin S.card := e.symm ∘ f₀
  let j : Fin S.card → W := Subtype.val ∘ e
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  have hcomp : j ∘ q = f := by
    funext a
    simp [j, q, f₀]
  have hmap (a : Finset (Fin A.1)) : (a.image q).image j = a.image f := by
    rw [Finset.image_image, hcomp]
  let H : RGraph (Fin S.card) r :=
    { edges := A.2.edges.image (fun a => a.image q)
      uniform := by
        intro d hd
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
        have hcard : (a.image q).card = (a.image f).card := by
          rw [← hmap a, Finset.card_image_of_injective _ hj]
        exact hcard.trans (G.uniform _ (hf a ha)) }
  have hsize : S.card ≤ A.1 := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin A.1)).card := Finset.card_image_le
      _ = A.1 := by simp
  refine ⟨⟨S.card, H⟩, hsize, ⟨q, e.symm.surjective.comp hf₀, rfl⟩,
    j, hj, ?_⟩
  intro d hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  rw [hmap]
  exact hf a ha

/-- Ordinary avoidance of the finite homomorphic closure is exactly
homomorphism avoidance of the original family. -/
theorem familyFree_homomorphicClosure_iff {W : Type u} [DecidableEq W]
    (F : Finset (FiniteGraph r)) (G : RGraph W r) :
    familyFree (homomorphicClosure F) G ↔ familyHomFree F G := by
  constructor
  · intro hfree A hA
    rintro ⟨f, hf⟩
    obtain ⟨Q, hsize, hQ, hemb⟩ := exists_homomorphicImage_embedding A G hf
    have hmem : Q ∈ homomorphicClosure F :=
      (mem_homomorphicClosure F Q).mpr
        ⟨hsize.trans (Finset.le_sup (f := fun B : FiniteGraph r => B.1) hA), A, hA, hQ⟩
    exact hfree Q hmem hemb
  · intro hfree Q hQ
    rintro ⟨g, hg⟩
    obtain ⟨_, A, hA, himage⟩ := (mem_homomorphicClosure F Q).mp hQ
    obtain ⟨f, hf⟩ := himage.exists_hom
    exact hfree A hA ⟨g ∘ f, hg.isHom.comp hf⟩

theorem familyHomFree_homomorphicClosure_iff {W : Type u} [DecidableEq W]
    (F : Finset (FiniteGraph r)) (G : RGraph W r) :
    familyHomFree (homomorphicClosure F) G ↔ familyHomFree F G := by
  constructor
  · intro hfree A hA
    exact hfree A (mem_homomorphicClosure_of_mem F hA)
  · intro hfree Q hQ
    rintro ⟨g, hg⟩
    obtain ⟨_, A, hA, himage⟩ := (mem_homomorphicClosure F Q).mp hQ
    obtain ⟨f, hf⟩ := himage.exists_hom
    exact hfree A hA ⟨g ∘ f, hg.comp hf⟩

theorem homomorphicClosure_has_edges (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    ∀ Q ∈ homomorphicClosure F, Q.2.edges.Nonempty := by
  intro Q hQ
  obtain ⟨_, A, hA, f, _, heq⟩ := (mem_homomorphicClosure F Q).mp hQ
  rw [heq]
  exact (hedges A hA).image _

/-- The integer used by the effective approximation is exactly the ordinary
extremal number for the finite family of all homomorphic images. -/
theorem familyExtremalNumber_homomorphicClosure (F : Finset (FiniteGraph r)) (m : ℕ) :
    familyExtremalNumber (homomorphicClosure F) m = homFreeMax F m := by
  classical
  apply le_antisymm
  · by_cases hz : familyExtremalNumber (homomorphicClosure F) m = 0
    · simp [hz]
    have hspec := Nat.findGreatest_of_ne_zero
      (P := fun k => ∃ G : RGraph (Fin m) r,
        familyFree (homomorphicClosure F) G ∧ G.edges.card = k)
      (n := m.choose r) (m := familyExtremalNumber (homomorphicClosure F) m) rfl hz
    obtain ⟨G, hG, hcard⟩ := hspec
    rw [← hcard]
    exact edge_card_le_homFreeMax F G ((familyFree_homomorphicClosure_iff F G).mp hG)
  · apply (homFreeMax_le_iff F m _).mpr
    intro G hG
    exact edge_card_le_familyExtremalNumber (homomorphicClosure F) G
      ((familyFree_homomorphicClosure_iff F G).mpr hG)

theorem familyWeightedValues_homomorphicClosure (F : Finset (FiniteGraph r)) :
    familyWeightedValues (homomorphicClosure F) = familyWeightedValues F := by
  ext z
  simp only [familyWeightedValues, Set.mem_ofPred_eq, familyHomFree_homomorphicClosure_iff]

/-- The homomorphic closure preserves the actual ordinary Turán density,
including families containing an edgeless forbidden graph. -/
theorem familyTuranDensity_homomorphicClosure (F : Finset (FiniteGraph r)) (hr : 0 < r) :
    familyTuranDensity (homomorphicClosure F) = familyTuranDensity F := by
  classical
  by_cases hedges : ∀ A ∈ F, A.2.edges.Nonempty
  · rw [familyTuranDensity_eq_sSup_weighted (homomorphicClosure F) hr
      (homomorphicClosure_has_edges F hedges),
      familyTuranDensity_eq_sSup_weighted F hr hedges,
      familyWeightedValues_homomorphicClosure]
  · have hQ : ¬ ∀ Q ∈ homomorphicClosure F, Q.2.edges.Nonempty := by
      intro h
      exact hedges (fun A hA => h A (mem_homomorphicClosure_of_mem F hA))
    rw [familyTuranDensity_eq_zero_of_not_nonempty _ hQ,
      familyTuranDensity_eq_zero_of_not_nonempty _ hedges]

theorem homFreeMax_eq_zero_of_edgeless (F : Finset (FiniteGraph r))
    {A : FiniteGraph r} (hA : A ∈ F) (hempty : A.2.edges = ∅)
    (m : ℕ) (hm : 0 < m) : homFreeMax F m = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (homFreeMax_le_iff F m 0).mpr
  intro G hG
  exfalso
  apply hG A hA
  refine ⟨fun _ => ⟨0, hm⟩, ?_⟩
  intro e he
  simp [hempty] at he

/-- The numerical sandwich also includes the degenerate edgeless-forbidden
case. For a nonempty target vertex set that case has hom-free maximum zero. -/
theorem homFreeMax_bounds_unconditional (F : Finset (FiniteGraph r))
    (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    homFreeLower F m ≤ familyTuranDensity F ∧
      familyTuranDensity F ≤ homFreeUpper F m := by
  classical
  by_cases hedges : ∀ A ∈ F, A.2.edges.Nonempty
  · exact homFreeMax_bounds F hedges m hm hr
  · have hpi := familyTuranDensity_eq_zero_of_not_nonempty F hedges
    push Not at hedges
    obtain ⟨A, hA, hempty⟩ := hedges
    have hmax := homFreeMax_eq_zero_of_edgeless F hA hempty m hm
    simp [homFreeLower, homFreeUpper, hmax, hpi]

/-- The finite-family approximation statement written with the original
ordinary extremal number of the homomorphic closure. -/
theorem familyTuranDensity_finite_approximation (F : Finset (FiniteGraph r))
    (m : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    (r.factorial : ℝ) * familyExtremalNumber (homomorphicClosure F) m / (m : ℝ) ^ r ≤
        familyTuranDensity F ∧
      familyTuranDensity F ≤
        (familyExtremalNumber (homomorphicClosure F) m : ℝ) / (m.choose r : ℝ) ∧
      0 ≤ (familyExtremalNumber (homomorphicClosure F) m : ℝ) / (m.choose r : ℝ) -
        familyTuranDensity F ∧
      (familyExtremalNumber (homomorphicClosure F) m : ℝ) / (m.choose r : ℝ) -
          familyTuranDensity F ≤ (r : ℝ) * ((r : ℝ) - 1) / (2 * (m : ℝ)) := by
  obtain ⟨hl, hu⟩ := homFreeMax_bounds_unconditional F m hm hr
  have herr : homFreeUpper F m - familyTuranDensity F ≤
      (r : ℝ) * ((r : ℝ) - 1) / (2 * (m : ℝ)) :=
    (sub_le_sub_left hl _).trans (homFreeMax_interval_width F m hm hr)
  simpa only [homFreeLower, homFreeUpper, familyExtremalNumber_homomorphicClosure]
    using And.intro hl (And.intro hu (And.intro (sub_nonneg.mpr hu) herr))

end TuranUniversality
