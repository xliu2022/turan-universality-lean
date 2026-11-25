module

public import TuranUniversality.Density.FamilyExtremal

@[expose] public section

/-! # Finite homomorphism-free extremal problems

The maximum is a finite supremum of natural edge counts. In particular it is
defined even when no graph avoids the forbidden family, in which case it is
zero. The hypotheses that each forbidden graph has an edge are needed only
to choose an actual maximizing graph.
-/

namespace TuranUniversality

variable {r : ℕ}

/-- All graphs on the labelled vertex set `Fin m` avoiding every member of
`F` as a homomorphic image. -/
def homFreeGraphs (F : Finset (FiniteGraph r)) (m : ℕ) :
    Finset (RGraph (Fin m) r) :=
  (RGraph.enumerate (Fin m) r).filter (familyHomFree F)

/-- The maximum edge count of an `m`-vertex `F`-hom-free graph. The maximum
of the empty feasible set is zero. -/
def homFreeMax (F : Finset (FiniteGraph r)) (m : ℕ) : ℕ :=
  (homFreeGraphs F m).sup (fun G => G.edges.card)

@[simp] theorem mem_homFreeGraphs (F : Finset (FiniteGraph r)) (m : ℕ)
    (G : RGraph (Fin m) r) :
    G ∈ homFreeGraphs F m ↔ familyHomFree F G := by
  simp [homFreeGraphs]

theorem edge_card_le_homFreeMax (F : Finset (FiniteGraph r)) {m : ℕ}
    (G : RGraph (Fin m) r) (hG : familyHomFree F G) :
    G.edges.card ≤ homFreeMax F m :=
  Finset.le_sup (f := fun H : RGraph (Fin m) r => H.edges.card)
    ((mem_homFreeGraphs F m G).mpr hG)

theorem homFreeMax_le_iff (F : Finset (FiniteGraph r)) (m c : ℕ) :
    homFreeMax F m ≤ c ↔
      ∀ G : RGraph (Fin m) r, familyHomFree F G → G.edges.card ≤ c := by
  simp only [homFreeMax, Finset.sup_le_iff, mem_homFreeGraphs]

theorem homFreeMax_le_choose (F : Finset (FiniteGraph r)) (m : ℕ) :
    homFreeMax F m ≤ m.choose r := by
  apply (homFreeMax_le_iff F m _).mpr
  intro G _
  exact G.edge_card_le_choose

theorem familyHomFree_empty (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) :
    familyHomFree F (RGraph.empty (Fin m) r) := by
  intro A hA
  rintro ⟨f, hf⟩
  obtain ⟨e, he⟩ := hedges A hA
  have h := hf e he
  simp [RGraph.empty] at h

theorem homFreeGraphs_nonempty (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) :
    (homFreeGraphs F m).Nonempty :=
  ⟨RGraph.empty (Fin m) r,
    (mem_homFreeGraphs F m _).mpr (familyHomFree_empty F hedges m)⟩

theorem exists_homFreeMax (F : Finset (FiniteGraph r))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (m : ℕ) :
    ∃ G : RGraph (Fin m) r,
      familyHomFree F G ∧ G.edges.card = homFreeMax F m := by
  obtain ⟨G, hG, hmax⟩ := Finset.exists_mem_eq_sup
    (homFreeGraphs F m) (homFreeGraphs_nonempty F hedges m) (fun G => G.edges.card)
  exact ⟨G, (mem_homFreeGraphs F m G).mp hG, hmax.symm⟩

end TuranUniversality
