module

public import TuranUniversality.Structural.CanonicalWeights
public import TuranUniversality.Density.SetFamilyExtremal

@[expose] public section

/-! # The actual finite noncanonical forbidden family

The order cutoff is the one in Section 9: all pair-covering extensions of
the rooted forbidden basis, together with the vertex-role witness bound.
The finite set is proved homomorphism closed and has the exact ordinary
Turán density. Effective code enumeration is a separate, additional layer.
-/

namespace TuranUniversality.Structural.Ordinary

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def roleWitnessEdges (B : Finset (FiniteGraph 3)) : ℕ :=
  max 2 (7 * (RecordSystem.cutoff B).choose 4)

noncomputable def orderCutoff (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (t : ℕ) : ℕ :=
  max ((Rooted.basis (homomorphicClosure F) Ω t).sup
    (fun A => Uniformity.extensionBound (t + (3 * b + 4)) A.1))
    ((t + (3 * b + 4)) ^ 2 * (t + 5 * b + 1) * roleWitnessEdges (homomorphicClosure F) + 2)

noncomputable def forbidden (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (t : ℕ) : Finset (FiniteGraph (t + (3 * b + 4))) := by
  classical
  exact FiniteGraph.forbiddenBasis
    (fun G : FiniteGraph (t + (3 * b + 4)) => Canonical (homomorphicClosure F) Ω G.2)
    (orderCutoff F Ω t)

@[simp] theorem mem_forbidden (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (t : ℕ) (G : FiniteGraph (t + (3 * b + 4))) :
    G ∈ forbidden F Ω t ↔ G.1 ≤ orderCutoff F Ω t ∧ ¬ Canonical (homomorphicClosure F) Ω G.2 := by
  classical
  simp [forbidden]

attribute [local irreducible] forbidden

theorem canonical_free (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) (hG : Canonical (homomorphicClosure F) Ω G) :
    familyFree (forbidden F Ω t) G := by
  intro A hA
  rintro ⟨f, hf⟩
  exact ((mem_forbidden F Ω t A).mp hA).2 (Canonical.of_hom F Ω hf.2 hG)

theorem forbidden_has_edges (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    {A : FiniteGraph (t + (3 * b + 4))} (hA : A ∈ forbidden F Ω t) : A.2.edges.Nonempty := by
  by_contra h
  exact ((mem_forbidden F Ω t A).mp hA).2
    (Canonical.of_admits (homomorphicClosure F) Ω hdis
      (Rooted.edgeless_admits (homomorphicClosure F) (homomorphicClosure_has_edges F hedges)
        Ω A.2 (Finset.not_nonempty_iff_eq_empty.mp h)))

theorem homomorphicClosure_forbidden (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (t : ℕ) :
    homomorphicClosure (forbidden F Ω t) = forbidden F Ω t := by
  classical
  apply Finset.ext
  intro Q
  constructor
  · intro hQ
    obtain ⟨_, A, hA, him⟩ := (mem_homomorphicClosure (forbidden F Ω t) Q).mp hQ
    have hhom := him.exists_hom
    obtain ⟨f, hf, he⟩ := him
    have hcard : Q.1 ≤ A.1 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f hf
    obtain ⟨hsize, hbad⟩ := (mem_forbidden F Ω t A).mp hA
    apply (mem_forbidden F Ω t Q).mpr
    refine ⟨hcard.trans hsize, ?_⟩
    intro hcan
    obtain ⟨g, hg⟩ := hhom
    exact hbad (Canonical.of_hom F Ω hg hcan)
  · exact mem_homomorphicClosure_of_mem _

theorem free_iff_homFree (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) :
    familyFree (forbidden F Ω t) G ↔ familyHomFree (forbidden F Ω t) G := by
  have h := familyFree_homomorphicClosure_iff (forbidden F Ω t) G
  rwa [homomorphicClosure_forbidden] at h

theorem canonical_homFree (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) (hG : Canonical (homomorphicClosure F) Ω G) :
    familyHomFree (forbidden F Ω t) G :=
  (free_iff_homFree F Ω G).mp (canonical_free F Ω G hG)

theorem extension_noncanonical (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    {A E : FiniteGraph (t + (3 * b + 4))}
    (hA : A ∈ Rooted.basis (homomorphicClosure F) Ω t)
    (hE : Uniformity.IsExtension A.2 E.2) : ¬ Canonical (homomorphicClosure F) Ω E.2 := by
  rintro ⟨ρ, R, hR, hh⟩
  obtain ⟨g, hg⟩ := hE.core_embedding_of_hom hh
  exact ((Rooted.mem_basis (homomorphicClosure F) Ω t A).mp hA).2
    (Rooted.Admits.of_embedding (homomorphicClosure F) Ω hdis hg
      (Compiled.admits (homomorphicClosure F) Ω R hR))

theorem extensionFamily_subset (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (t : ℕ) : PairTransfer.extensionFamily (Rooted.basis (homomorphicClosure F) Ω t) ⊆
      forbidden F Ω t := by
  intro E hE
  obtain ⟨A, hA, hE⟩ := (PairTransfer.mem_extensionFamily _ E).mp hE
  obtain ⟨hsize, hext⟩ := (Uniformity.mem_extensions A E).mp hE
  apply (mem_forbidden F Ω t E).mpr
  refine ⟨?_, extension_noncanonical F Ω hdis hA hext⟩
  exact hsize.trans ((Finset.le_sup (f := fun A : FiniteGraph (t + (3 * b + 4)) =>
    Uniformity.extensionBound (t + (3 * b + 4)) A.1) hA).trans (le_max_left _ _))

/-- The ordinary density identity from Section 9, for the actual finite
family and actual seven support pools. -/
theorem density_eq (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    familyTuranDensity (forbidden F Ω t) = ((t + (3 * b + 4)).factorial : ℝ) *
      (OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)) := by
  have hr : 2 ≤ t + (3 * b + 4) := by omega
  have hfac : (0 : ℝ) < (t + (3 * b + 4)).factorial := by
    exact_mod_cast Nat.factorial_pos _
  apply le_antisymm
  · have hmono : familyTuranDensity (forbidden F Ω t) ≤
        familyTuranDensity (PairTransfer.extensionFamily (Rooted.basis (homomorphicClosure F) Ω t)) := by
      have hs : (PairTransfer.extensionFamily (Rooted.basis (homomorphicClosure F) Ω t) :
          Set (FiniteGraph (t + (3 * b + 4)))) ⊆ (forbidden F Ω t : Set _) := by
        intro A hA
        exact extensionFamily_subset F Ω hdis t hA
      have h := SetFamily.turanDensity_antitone hs
      simpa only [SetFamily.turanDensity_finset] using h
    rw [PairTransfer.density_eq _ hr
      (fun A hA => Rooted.basis_has_edges (homomorphicClosure F)
        (homomorphicClosure_has_edges F hedges) Ω t hA),
      admissible_classLagrangian F hedges Ω hdis t p q hp hpq hq hz hΩ] at hmono
    exact hmono
  · have hb : OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F) ≤
        familyTuranDensity (forbidden F Ω t) / ((t + (3 * b + 4)).factorial : ℝ) := by
      apply (Compiled.weightedValues_isLUB F hedges Ω p q hp hpq hq hz hΩ).2
      rintro z ⟨V, d, f, R, x, hR, hx, rfl⟩
      letI : DecidableEq V := d
      letI : Fintype V := f
      apply (le_div_iff₀ hfac).mpr
      simpa only [mul_comm] using familyTuranDensity_lower_of_homFree (forbidden F Ω t)
        (Compiled.graph t Ω R)
        (canonical_homFree F Ω _ (Compiled.canonical (homomorphicClosure F) Ω R hR)) x hx
    simpa only [mul_comm] using (le_div_iff₀ hfac).mp hb

end TuranUniversality.Structural.Ordinary
