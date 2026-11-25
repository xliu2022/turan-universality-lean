module

public import TuranUniversality.Hypergraph.FiniteBasis
public import TuranUniversality.Hypergraph.Relabel

@[expose] public section

/-!
# A finite forbidden basis whose every core contains the guard

Instead of canonicalizing overlap unions, we enumerate all labeled obstructions
up to the same order bound. This preserves effectiveness and ensures that every
listed core contains the guard as an ordinary embedded subgraph.
-/

namespace TuranUniversality.FiniteGraph

variable {r : ℕ}

def guardedClass (C : FiniteGraph r → Prop) (H : FiniteGraph r) (G : FiniteGraph r) : Prop :=
  C G ∨ ¬ H.Contains G

instance (C : FiniteGraph r → Prop) [DecidablePred C] (H : FiniteGraph r) :
    DecidablePred (guardedClass C H) := fun G =>
  inferInstanceAs (Decidable (C G ∨ ¬ H.Contains G))

theorem guardedClass_monotone (C : FiniteGraph r → Prop) (hC : ClassMonotone C)
    (H : FiniteGraph r) : ClassMonotone (guardedClass C H) := by
  intro A G hAG hG
  rcases hG with hG | hG
  · exact Or.inl (hC A G hAG hG)
  · right
    rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ := hAG
    exact hG ⟨_, hg.comp hf⟩

theorem guardedClass_bounded (C : FiniteGraph r → Prop) (hC : ClassMonotone C)
    (B : ℕ) (hB : ∀ G, ¬ C G → ∃ A, A.1 ≤ B ∧ ¬ C A ∧ A.Contains G)
    (H : FiniteGraph r) (G : FiniteGraph r) (hG : ¬ guardedClass C H G) :
    ∃ A, A.1 ≤ B + H.1 ∧ ¬ guardedClass C H A ∧ A.Contains G := by
  have hnC : ¬ C G := fun h => hG (Or.inl h)
  have hpair : ¬ C G ∧ H.Contains G := by
    simpa only [guardedClass, not_or, not_not] using hG
  have hH := hpair.2
  obtain ⟨A, hsize, hA, f, hf⟩ := hB G hnC
  obtain ⟨g, hg⟩ := hH
  obtain ⟨k, K, hk, ⟨a, ha⟩, ⟨b, hb⟩, ⟨t, ht⟩⟩ := RGraph.joint_embedded_subgraph A.2 H.2 G.2 hf hg
  refine ⟨⟨k, K⟩, ?_, ?_, ⟨t, ht⟩⟩
  · have hk' : k ≤ A.1 + H.1 := by simpa only [Fintype.card_fin] using hk
    exact hk'.trans (Nat.add_le_add_right hsize H.1)
  · rintro (hK | hK)
    · exact hA (hC A ⟨k, K⟩ ⟨a, ha⟩ hK)
    · exact hK ⟨b, hb⟩

def guardedBasis (C : FiniteGraph r → Prop) [DecidablePred C]
    (B : ℕ) (H : FiniteGraph r) : Finset (FiniteGraph r) :=
  forbiddenBasis (guardedClass C H) (B + H.1)

theorem guardedBasis_contains_guard (C : FiniteGraph r → Prop) [DecidablePred C]
    (B : ℕ) (H : FiniteGraph r) {A : FiniteGraph r} (hA : A ∈ guardedBasis C B H) :
    ¬ C A ∧ H.Contains A := by
  have h := ((mem_forbiddenBasis (guardedClass C H) (B + H.1) A).mp hA).2
  simpa only [guardedClass, not_or, not_not] using h

theorem guardedBasis_spec (C : FiniteGraph r → Prop) [DecidablePred C]
    (hC : ClassMonotone C) (B : ℕ)
    (hB : ∀ G, ¬ C G → ∃ A, A.1 ≤ B ∧ ¬ C A ∧ A.Contains G)
    (H G : FiniteGraph r) :
    guardedClass C H G ↔ ∀ A ∈ guardedBasis C B H, ¬ A.Contains G :=
  forbiddenBasis_spec (guardedClass C H) (B + H.1) (guardedClass_monotone C hC H)
    (guardedClass_bounded C hC B hB H) G

end TuranUniversality.FiniteGraph
