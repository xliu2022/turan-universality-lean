module

public import TuranUniversality.Uniformity.Obstruction
public import TuranUniversality.Uniformity.Extensions
public import TuranUniversality.Uniformity.Suspension

@[expose] public section

/-! # Ordinary extensions and suspension-class templates

The upper direction uses ordinary embedded extensions in a pair-covered
support. The lower direction uses homomorphism avoidance, hence permits all
blowups of an admissible template.
-/

namespace TuranUniversality.Uniformity

universe u v
variable {V : Type u} {X : Type v} [DecidableEq V] [DecidableEq X]
  [Fintype V] [Fintype X] {r : ℕ}

def family (P : FiniteGraph 3) (r : ℕ) : Finset (FiniteGraph r) :=
  (basis P r).biUnion extensions

@[simp] theorem mem_family (P : FiniteGraph 3) (r : ℕ) (E : FiniteGraph r) :
    E ∈ family P r ↔ ∃ A ∈ basis P r, E ∈ extensions A := by
  simp [family]

theorem family_has_edges (P : FiniteGraph 3) (r : ℕ)
    {E : FiniteGraph r} (hE : E ∈ family P r) : E.2.edges.Nonempty := by
  obtain ⟨A, hA, hE⟩ := (mem_family P r E).mp hE
  exact extensions_has_edges A (basis_has_edges P r hA) hE

/-- Every admissible template avoids all of the forbidden extensions even
as homomorphic images. -/
theorem familyHomFree_of_admissible (P : FiniteGraph 3) (r : ℕ)
    (G : RGraph V r) (hG : Admissible P.2 G) : familyHomFree (family P r) G := by
  intro E hE
  obtain ⟨A, hA, hE⟩ := (mem_family P r E).mp hE
  rintro ⟨f, hf⟩
  obtain ⟨g, hg⟩ := ((mem_extensions A E).mp hE).2.core_embedding_of_hom hf
  exact ((mem_basis P r A).mp hA).2 (hG.of_embedding hg)

/-- Ordinary extension avoidance on a pair-covered host forces membership
in the suspension class. -/
theorem admissible_of_pairCovered_free (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r)
    (G : RGraph V r) (hfree : familyFree (family P r) G) (hcover : G.CoversPairs) :
    Admissible P.2 G := by
  apply (basis_spec_finite P r hr G).mpr
  intro A hA hemb
  obtain ⟨f, hf⟩ := hemb
  obtain ⟨E, hE, g, hg⟩ := exists_embedded_extension A G (by omega)
    (basis_has_edges P r hA) hcover hf
  exact hfree E ((mem_family P r E).mpr ⟨A, hA, hE⟩) ⟨g, hg⟩

/-- The actual finite support supplied by weight compression is admissible. -/
theorem compressed_support_admissible (P : FiniteGraph 3) (r : ℕ) (hr : 3 ≤ r)
    (G : RGraph V r) (hfree : familyFree (family P r) G)
    (x : V → ℝ) (hcover : G.CoversWeightSupport x) :
    Admissible P.2 (G.supportGraph x) := by
  classical
  exact admissible_of_pairCovered_free P r hr _
    (familyFree_pullback _ G _ hfree) (hcover.support_covers_pairs G x)

/-- Every blowup of an admissible template is ordinarily forbidden-free. -/
theorem familyFree_blowup_of_admissible (P : FiniteGraph 3) (r : ℕ)
    (G : RGraph V r) (hG : Admissible P.2 G) (sizes : V → ℕ) :
    familyFree (family P r) (G.blowup sizes) :=
  familyFree_blowup _ G (familyHomFree_of_admissible P r G hG) sizes

/-- The suspension of a homomorphism-free three-graph is an admissible
template, retaining every data vertex. -/
theorem Admissible.suspension (P : RGraph X 3) (G : RGraph V 3) (s : ℕ)
    (hfree : P.HomFree G) : Admissible P (G.suspension s) := by
  classical
  let S : Finset (Fin s ⊕ V) := Finset.univ.map Function.Embedding.inl
  have hS : (G.suspension s).IsCore S := by
    refine ⟨by simp [S], ?_⟩
    intro e he
    obtain ⟨d, hd, rfl⟩ := (G.mem_suspension s e).mp he
    exact Finset.subset_union_left
  have hright (v : {v : Fin s ⊕ V // v ∉ S}) : ∃ w : V, Sum.inr w = v.val := by
    cases hv : v.val with
    | inl i => exact False.elim (v.property (by simp [S, hv]))
    | inr w => exact ⟨w, rfl⟩
  choose g hg using hright
  have hhom : ((G.suspension s).coreLink S).IsHom G g := by
    intro e he
    have he' := ((G.suspension s).mem_coreLink S e).mp he
    obtain ⟨d, hd, hde⟩ := (G.mem_suspension s _).mp he'.2
    have himage : e.image g = d := by
      ext w
      constructor
      · intro hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have h : Sum.inr (g v) ∈ S ∪ e.image Subtype.val :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, (hg v).symm⟩)
        rw [← hde] at h
        exact (RGraph.mem_suspendEdge_right s d (g v)).mp h
      · intro hw
        have h : Sum.inr w ∈ S ∪ e.image Subtype.val := by
          rw [← hde]
          exact (RGraph.mem_suspendEdge_right s d w).mpr hw
        have hn : Sum.inr w ∉ S := by simp [S]
        obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp ((Finset.mem_union.mp h).resolve_left hn)
        exact Finset.mem_image.mpr ⟨v, hv, Sum.inr.inj ((hg v).trans hvw)⟩
    exact himage ▸ hd
  refine Or.inr ⟨S, hS, ?_⟩
  rintro ⟨f, hf⟩
  exact hfree ⟨g ∘ f, hhom.comp hf⟩

end TuranUniversality.Uniformity
