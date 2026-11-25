module

public import TuranUniversality.Density.UpperBridge
public import TuranUniversality.Density.LowerBridge

@[expose] public section

/-! # Ordinary Turán density respects homomorphisms of forbidden graphs -/

namespace TuranUniversality

theorem turanDensity_nonneg {r k : ℕ} (F : RGraph (Fin k) r) :
    0 ≤ turanDensity F :=
  le_ciInf fun n => extremalDensity_nonneg F (n + r)

/-- The two sampling bridges show that a homomorphism between forbidden
graphs gives the same direction of monotonicity for their ordinary densities.
The statement includes isolated vertices on either side. -/
theorem turanDensity_le_of_hom {k l : ℕ}
    (F : RGraph (Fin k) 3) (G : RGraph (Fin l) 3)
    (hF : F.edges.Nonempty) (hG : G.edges.Nonempty)
    {f : Fin k → Fin l} (hf : F.IsHom G f) :
    turanDensity F ≤ turanDensity G := by
  apply turanDensity_upper_of_homFree F (Finset.card_pos.mpr hF) _ (turanDensity_nonneg G)
  intro n H hfree
  by_cases hn : n = 0
  · subst n
    simpa [RGraph.oneEdge_homDensity] using turanDensity_nonneg G
  · letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    exact turanDensity_lower_of_homFree G (Finset.card_pos.mpr hG) H (hfree.of_hom hf)

theorem turanDensity_eq_of_mutualHom {k l : ℕ}
    (F : RGraph (Fin k) 3) (G : RGraph (Fin l) 3)
    (hF : F.edges.Nonempty) (hG : G.edges.Nonempty)
    (hFG : ∃ f, F.IsHom G f) (hGF : ∃ f, G.IsHom F f) :
    turanDensity F = turanDensity G := by
  obtain ⟨f, hf⟩ := hFG
  obtain ⟨g, hg⟩ := hGF
  exact le_antisymm (turanDensity_le_of_hom F G hF hG hf)
    (turanDensity_le_of_hom G F hG hF hg)

end TuranUniversality
