module

public import TuranUniversality.Structural.Symmetrized
public import TuranUniversality.Stability.NearExtremal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Instantiating the finite Ψ theorem for the actual ordinary family

The forbidden family, canonical class, exact weighted upper bound, and
symmetrized conclusion are the concrete constructions of Sections 8--9.
The remaining input in the degree-stability wrapper is explicitly the
one-vertex extension theorem, rather than a stability conclusion.
-/

open Filter Topology

namespace TuranUniversality.Structural.Ordinary

open Stability

universe u v
variable {b t : ℕ}

def freeClass (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) : GraphClass.{u} (t + (3 * b + 4)) :=
  fun {_} _ _ G => familyFree (forbidden F Ω t) G

def canonicalClass (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) : GraphClass.{u} (t + (3 * b + 4)) :=
  fun {_} _ _ G => Canonical (homomorphicClosure F) Ω G

noncomputable def optimum (F : Finset (FiniteGraph 3)) (b t : ℕ) (p q : ℝ) : ℝ :=
  OuterWeights.chi b t * SwitchScalar.phaseScore p q (familyTuranDensity F)

theorem optimum_pos (F : Finset (FiniteGraph 3)) (b t : ℕ) (p q : ℝ)
    (hq : 0 < q) (hz : p / q ≤ familyTuranDensity F) : 0 < optimum F b t p q :=
  mul_pos (OuterWeights.chi_pos b t) (SwitchScalar.phaseScore_pos p q _ hq hz)

theorem freeClass_homClosed (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (t : ℕ) : HomClosed (freeClass.{u} F Ω t) := by
  intro V W _ _ _ _ G H f hf hH
  exact (free_iff_homFree F Ω G).mpr
    (familyHomFree_of_hom (forbidden F Ω t) G H hf ((free_iff_homFree F Ω H).mp hH))

theorem canonicalClass_embeddingClosed (F : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (t : ℕ) :
    EmbeddingClosed (canonicalClass.{u} F Ω t) := by
  intro V W _ _ _ _ G H f hf hH
  exact Canonical.of_hom F Ω hf.2 hH

theorem freeClass_polynomialBound (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a) :
    PolynomialBound (freeClass.{u} F Ω t) (optimum F b t p q) := by
  intro V _ _ G hG x hx
  have h := familyTuranDensity_lower_of_homFree (forbidden F Ω t) G
    ((free_iff_homFree F Ω G).mp hG) x hx
  rw [density_eq F hedges Ω hdis t p q hp hpq hq hz hΩ] at h
  have hfac : (0 : ℝ) < (t + (3 * b + 4)).factorial := by
    exact_mod_cast Nat.factorial_pos _
  exact (mul_le_mul_iff_right₀ hfac).mp h

theorem symmetrized_stable (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ) (Λ ε : ℝ) (N : ℕ) :
    SymmetrizedStable (freeClass.{u} F Ω t) (canonicalClass F Ω t) Λ ε N := by
  intro V _ _ G hG _ _ hsym
  exact symmetrized_canonical F hedges Ω hdis G hG hsym

/-- All structural inputs except the actual one-vertex extension have
been discharged for the concrete finite forbidden family. -/
theorem degree_stable (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{u} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N) :
    DegreeStable (freeClass.{u} F Ω t) (canonicalClass F Ω t) (optimum F b t p q) := by
  apply degreeStable_of_symmetrized_vertexExtendable _ _ (by omega)
    (freeClass_homClosed F Ω t) (canonicalClass_embeddingClosed F Ω t)
    (optimum_pos F b t p q hq hz)
    (freeClass_polynomialBound F hedges Ω hdis t p q hp hpq hq hz hΩ)
    _ hext
  exact ⟨1, zero_lt_one, 0, symmetrized_stable F hedges Ω hdis t _ 1 0⟩

theorem eventually_canonical_induced (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : 0 < q)
    (hz : p / q ≤ familyTuranDensity F)
    (hΩ : ∀ a, ((Ω a).card : ℝ) = Label.payoff p q a)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ N : ℕ,
      VertexExtendable (freeClass.{u} F Ω t) (canonicalClass F Ω t)
        ((t + (3 * b + 4) : ℕ) * optimum F b t p q - ζ) N)
    {I : Type v} {V : I → Type u}
    [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (G : ∀ i, RGraph (V i) (t + (3 * b + 4)))
    (hG : ∀ i, familyFree (forbidden F Ω t) (G i))
    (hn : ∀ i, 0 < Fintype.card (V i)) (l : Filter I)
    (hsize : Tendsto (fun i => Fintype.card (V i)) l atTop)
    (hlim : Tendsto (fun i => ((G i).edges.card : ℝ) /
      (Fintype.card (V i) : ℝ) ^ (t + (3 * b + 4))) l (𝓝 (optimum F b t p q))) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun i => (((G i).lowDegreeSet (optimum F b t p q) δ).card : ℝ) /
        Fintype.card (V i)) l (𝓝 0) ∧
      ∀ᶠ i in l, 0 < (goodVertices (G i) (optimum F b t p q) δ).card ∧
        Canonical (homomorphicClosure F) Ω
          ((G i).induced (goodVertices (G i) (optimum F b t p q) δ)) := by
  exact eventually_good_induced_of_degreeStable (freeClass F Ω t) (canonicalClass F Ω t)
    (by omega) (freeClass_homClosed F Ω t) (optimum_pos F b t p q hq hz)
    (freeClass_polynomialBound F hedges Ω hdis t p q hp hpq hq hz hΩ)
    (degree_stable F hedges Ω hdis t p q hp hpq hq hz hΩ hext)
    G hG hn l hsize hlim

end TuranUniversality.Structural.Ordinary
