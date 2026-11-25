module

public import TuranUniversality.Uniformity.Extensions
public import TuranUniversality.Hypergraph.Relabel
public import TuranUniversality.Hypergraph.Lagrangian
public import TuranUniversality.Density.FamilyUpper
public import TuranUniversality.Density.FamilyLower

@[expose] public section

/-! # Pair-covering transfer for an arbitrary finite ordinary forbidden family

This is the general form of Lemma 2.4. The class Lagrangian is defined from
the edge polynomials of actual ordinary-free finite graphs. The density is
the ordinary extremal-density limit. No variational identity is an input.

The members of the input family have edges, as in the definition of Ext in
the paper. All three conclusions hold without the additional nontriviality
assumption that the free class contains an edge.
-/

namespace TuranUniversality.PairTransfer

universe u
variable {r : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- The actual finite union of all bounded pair-covering extensions. -/
def extensionFamily (A : Finset (FiniteGraph r)) : Finset (FiniteGraph r) :=
  A.biUnion Uniformity.extensions

@[simp] theorem mem_extensionFamily (A : Finset (FiniteGraph r)) (E : FiniteGraph r) :
    E ∈ extensionFamily A ↔ ∃ B ∈ A, E ∈ Uniformity.extensions B := by
  simp [extensionFamily]

theorem extensionFamily_has_edges (A : Finset (FiniteGraph r))
    (hedges : ∀ B ∈ A, B.2.edges.Nonempty) {E : FiniteGraph r}
    (hE : E ∈ extensionFamily A) : E.2.edges.Nonempty := by
  obtain ⟨B, hB, hE⟩ := (mem_extensionFamily A E).mp hE
  exact Uniformity.extensions_has_edges B (hedges B hB) hE

/-- An ordinary-free base avoids every extension as a homomorphic image. -/
theorem homFree_of_free (A : Finset (FiniteGraph r)) (G : RGraph V r)
    (hfree : familyFree A G) : familyHomFree (extensionFamily A) G := by
  intro E hE
  obtain ⟨B, hB, hE⟩ := (mem_extensionFamily A E).mp hE
  rintro ⟨f, hf⟩
  exact hfree B hB (((Uniformity.mem_extensions B E).mp hE).2.core_embedding_of_hom hf)

/-- Every blowup in conclusion (ii), with arbitrary nonnegative class sizes. -/
theorem blowup_free (A : Finset (FiniteGraph r)) (G : RGraph V r)
    (hfree : familyFree A G) (sizes : V → ℕ) :
    familyFree (extensionFamily A) (G.blowup sizes) :=
  familyFree_blowup _ G (homFree_of_free A G hfree) sizes

theorem free_of_pairCovered (A : Finset (FiniteGraph r)) (hr : 2 ≤ r)
    (hedges : ∀ B ∈ A, B.2.edges.Nonempty) (G : RGraph V r)
    (hfree : familyFree (extensionFamily A) G) (hcover : G.CoversPairs) :
    familyFree A G := by
  intro B hB hemb
  obtain ⟨f, hf⟩ := hemb
  obtain ⟨E, hE, g, hg⟩ := Uniformity.exists_embedded_extension B G hr
    (hedges B hB) hcover hf
  exact hfree E ((mem_extensionFamily A E).mpr ⟨B, hB, hE⟩) ⟨g, hg⟩

theorem compressed_support_free (A : Finset (FiniteGraph r)) (hr : 2 ≤ r)
    (hedges : ∀ B ∈ A, B.2.edges.Nonempty) (G : RGraph V r)
    (hfree : familyFree (extensionFamily A) G) (x : V → ℝ)
    (hcover : G.CoversWeightSupport x) : familyFree A (G.supportGraph x) := by
  classical
  exact free_of_pairCovered A hr hedges _
    (familyFree_pullback _ G _ hfree) (hcover.support_covers_pairs G x)

/-- Unnormalized ordinary-free polynomial values. Including zero also
specifies the value of a class with no probability-weighted member. -/
def ordinaryWeightedValues (A : Finset (FiniteGraph r)) : Set ℝ :=
  insert 0 {z | ∃ (n : ℕ) (G : RGraph (Fin n) r) (x : Fin n → ℝ),
    familyFree A G ∧ ProbabilityWeights x ∧ z = G.edgePolynomial x}

theorem ordinaryWeightedValues_nonempty (A : Finset (FiniteGraph r)) :
    (ordinaryWeightedValues A).Nonempty := ⟨0, Or.inl rfl⟩

theorem ordinaryWeightedValues_bddAbove (A : Finset (FiniteGraph r)) :
    BddAbove (ordinaryWeightedValues A) := by
  refine ⟨1, ?_⟩
  rintro z (rfl | ⟨n, G, x, _, hx, rfl⟩)
  · norm_num
  · have hn := G.edgePolynomial_nonneg hx.1
    have hf : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
    have hb := (familyTuranDensity_lower_of_homFree ∅ G
      (familyHomFree_empty_family G) x hx).trans (familyTuranDensity_le_one ∅)
    nlinarith

/-- The class Lagrangian Λ(Forb(A)), with no factor r!. -/
noncomputable def classLagrangian (A : Finset (FiniteGraph r)) : ℝ :=
  sSup (ordinaryWeightedValues A)

theorem classLagrangian_nonneg (A : Finset (FiniteGraph r)) :
    0 ≤ classLagrangian A :=
  le_csSup (ordinaryWeightedValues_bddAbove A) (Or.inl rfl)

theorem polynomial_le_classLagrangian (A : Finset (FiniteGraph r))
    (G : RGraph V r) (hfree : familyFree A G) (x : V → ℝ)
    (hx : ProbabilityWeights x) : G.edgePolynomial x ≤ classLagrangian A := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  apply le_csSup (ordinaryWeightedValues_bddAbove A)
  refine Or.inr ⟨Fintype.card V, G.pullback e.toEmbedding, x ∘ e,
    familyFree_pullback A G e.toEmbedding hfree, probabilityWeights_equiv e x hx, ?_⟩
  exact (G.pullback_equiv_polynomial e x).symm

theorem classLagrangian_le_of_bound (A : Finset (FiniteGraph r)) (b : ℝ)
    (hb : 0 ≤ b)
    (hbound : ∀ n (G : RGraph (Fin n) r) (x : Fin n → ℝ),
      familyFree A G → ProbabilityWeights x → G.edgePolynomial x ≤ b) :
    classLagrangian A ≤ b := by
  apply csSup_le (ordinaryWeightedValues_nonempty A)
  rintro z (rfl | ⟨n, G, x, hfree, hx, rfl⟩)
  · exact hb
  · exact hbound n G x hfree hx

/-- Conclusion (i): the density of the concrete extension family is exactly
r! times the ordinary-free class Lagrangian. -/
theorem density_eq (A : Finset (FiniteGraph r)) (hr : 2 ≤ r)
    (hedges : ∀ B ∈ A, B.2.edges.Nonempty) :
    familyTuranDensity (extensionFamily A) = (r.factorial : ℝ) * classLagrangian A := by
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  apply le_antisymm
  · apply familyTuranDensity_upper_of_weighted_free (extensionFamily A)
      (fun _ h => extensionFamily_has_edges A hedges h)
    intro n G x hfree hx
    obtain ⟨y, hy, hxy, hcover⟩ := G.exists_compressed_weights x hx
    have hb := polynomial_le_classLagrangian A (G.supportGraph y)
      (compressed_support_free A hr hedges G hfree y hcover)
      (fun v => y v.val) (support_probability y hy)
    rw [G.supportGraph_polynomial] at hb
    exact mul_le_mul_of_nonneg_left (hxy.trans hb) hf.le
  · have hl : classLagrangian A ≤
        familyTuranDensity (extensionFamily A) / (r.factorial : ℝ) := by
      apply classLagrangian_le_of_bound A _
        (div_nonneg (familyTuranDensity_nonneg _) hf.le)
      intro n G x hfree hx
      apply (le_div_iff₀ hf).mpr
      simpa [mul_comm] using familyTuranDensity_lower_of_homFree
        (extensionFamily A) G (homFree_of_free A G hfree) x hx
    simpa [mul_comm] using (le_div_iff₀ hf).mp hl

/-- The actual optimality and minimum-support conditions in conclusion (iii). -/
def MinimumSupportMaximizer (G : RGraph V r) (x : V → ℝ) : Prop :=
  ProbabilityWeights x ∧ (r.factorial : ℝ) * G.edgePolynomial x = G.lagrangian ∧
    ∀ y : V → ℝ, ProbabilityWeights y →
      (r.factorial : ℝ) * G.edgePolynomial y = G.lagrangian →
      (weightSupport x).card ≤ (weightSupport y).card

/-- Compactness supplies a maximum, and well-ordering of finite support
sizes supplies the minimum-support maximum used in the paper. -/
theorem exists_minimumSupportMaximizer [Nonempty V] (G : RGraph V r) :
    ∃ x : V → ℝ, MinimumSupportMaximizer G x := by
  classical
  obtain ⟨x₀, hx₀, heq₀⟩ := G.exists_lagrangian_maximizer
  have hex : ∃ n : ℕ, ∃ x : V → ℝ, ProbabilityWeights x ∧
      (r.factorial : ℝ) * G.edgePolynomial x = G.lagrangian ∧
      (weightSupport x).card = n := ⟨_, x₀, hx₀, heq₀, rfl⟩
  obtain ⟨x, hx, heq, hcard⟩ := Nat.find_spec hex
  refine ⟨x, hx, heq, ?_⟩
  intro y hy heqy
  rw [hcard]
  exact Nat.find_min' hex ⟨y, hy, heqy, rfl⟩

theorem minimumSupportMaximizer_covers (G : RGraph V r) (x : V → ℝ)
    (hx : MinimumSupportMaximizer G x) : G.CoversWeightSupport x := by
  classical
  by_contra hc
  obtain ⟨y, hy, hxy, hcard⟩ := G.compression_step x hx.1 hc
  have heq : (r.factorial : ℝ) * G.edgePolynomial y = G.lagrangian := by
    apply le_antisymm (G.normalizedPolynomial_le_lagrangian y hy)
    rw [← hx.2.1]
    exact mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg _)
  exact (Nat.not_lt_of_ge (hx.2.2 y hy heq)) hcard

/-- Conclusion (iii) for the subhypergraph induced by all positive weights.
For probability weights, nonzero and positive support coincide. -/
theorem minimumSupportMaximizer_support (A : Finset (FiniteGraph r)) (hr : 2 ≤ r)
    (hedges : ∀ B ∈ A, B.2.edges.Nonempty) (G : RGraph V r)
    (hfree : familyFree (extensionFamily A) G) (x : V → ℝ)
    (hx : MinimumSupportMaximizer G x) :
    familyFree A (G.supportGraph x) ∧ (G.supportGraph x).CoversPairs := by
  have hc := minimumSupportMaximizer_covers G x hx
  exact ⟨compressed_support_free A hr hedges G hfree x hc,
    hc.support_covers_pairs G x⟩

end TuranUniversality.PairTransfer
