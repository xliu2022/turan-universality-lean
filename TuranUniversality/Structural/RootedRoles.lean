module

public import TuranUniversality.Structural.CanonicalLocal

@[expose] public section

/-! # Partial rootings and singleton root classes

Formalization author: Xizhi Liu.
Maintainer: Xizhi Liu.

The finite-basis predicate uses a partial injection of roots into vertices.
It is exactly the role-map predicate with at most one vertex in each root
class. Restricting a local test to its data vertices reconciles the two local
legality definitions. This identity permits a single finite role checker to
compute both the rooted basis and the canonical obstruction family.
-/

namespace TuranUniversality.Structural.Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem admissibleOn_univ_iff_roles (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (G : RGraph V (t + (3 * b + 4)))
    (μ : Rooting (Roots b t) V) :
    AdmissibleOn B Ω G Finset.univ μ ↔ Roles.Admissible B Ω G μ.inverse.val := by
  classical
  constructor
  · intro h
    refine ⟨fun e he => h.1 e he (Finset.subset_univ _), ?_⟩
    intro S hcard
    let U := S.filter fun v => μ.inverse.val v = none
    have hUS : U ⊆ S := Finset.filter_subset _ _
    obtain ⟨O, hO, hfits⟩ := h.2 U (Finset.subset_univ _)
      (fun v hv => (Finset.mem_filter.mp hv).2)
      ((Finset.card_le_card hUS).trans hcard)
    refine ⟨O, hO.trans hUS, fun e he heS => ?_⟩
    apply hfits e he (Finset.subset_univ _)
    intro v hv
    exact Finset.mem_filter.mpr ⟨heS hv, (mem_dataSet μ e v).mp hv |>.2⟩
  · intro h
    refine ⟨fun e he _ => h.1 e he, ?_⟩
    intro S _ _ hcard
    obtain ⟨O, hO, hfits⟩ := h.2 S hcard
    exact ⟨O, hO, fun e he _ heS => hfits e he heS⟩

theorem admits_iff_singleton_root_roles (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (G : RGraph V (t + (3 * b + 4))) :
    Admits B Ω G ↔ ∃ ρ : V → Option (Roots b t),
      Roles.Admissible B Ω G ρ ∧
        ∀ v w m, ρ v = some m → ρ w = some m → v = w := by
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨μ.inverse.val, (admissibleOn_univ_iff_roles B Ω G μ).mp hμ,
      μ.inverse.property⟩
  · rintro ⟨ρ, hρ, hinj⟩
    let μ : Rooting (Roots b t) V := Rooting.inverse ⟨ρ, hinj⟩
    refine ⟨μ, (admissibleOn_univ_iff_roles B Ω G μ).mpr ?_⟩
    simpa [μ] using hρ

end TuranUniversality.Structural.Rooted
