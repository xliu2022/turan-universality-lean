module

public import TuranUniversality.Structural.WeightedProfiles
public import TuranUniversality.Density.HomomorphicClosure
public import TuranUniversality.Density.Cloning
public import Mathlib.Topology.Sequences

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Ordinary and weighted extremal spaces

The underlying coordinates are the homomorphism densities of all labelled
finite graphs. The ordinary extremal space uses the ordinary Turán density
and the ordinary dense limit space. The equality with the weighted hom-free
closure is proved using finite free realization and homomorphic images.
-/

open scoped BigOperators
open Filter Topology

namespace TuranUniversality.SetFamily

variable {r : ℕ}

def edgeTest (r : ℕ) : FiniteGraph r := ⟨r, RGraph.oneEdge r⟩

noncomputable def weightedClassProfiles (C : FiniteGraph r → Prop) : Set (Profile r) :=
  {W | ∃ (G : FiniteGraph r) (x : Fin G.1 → ℝ),
    C G ∧ ProbabilityWeights x ∧ W = weightedProfile G.2 x}

theorem closure_weightedClassProfiles_subset (C : FiniteGraph r → Prop) :
    closure (weightedClassProfiles C) ⊆ {W | IsLimitProfile W} := by
  apply closure_minimal _ isClosed_closure
  rintro W ⟨G, x, _, hx, rfl⟩
  exact isLimitProfile_weighted G.2 x hx

theorem isCompact_closure_weightedClassProfiles (C : FiniteGraph r → Prop) :
    IsCompact (closure (weightedClassProfiles C)) :=
  (isCompact_limitProfiles r).of_isClosed_subset isClosed_closure
    (closure_weightedClassProfiles_subset C)

theorem exists_weighted_sequence (C : FiniteGraph r → Prop) (W : Profile r)
    (hW : W ∈ closure (weightedClassProfiles C)) :
    ∃ (G : ℕ → FiniteGraph r) (x : ∀ n, Fin (G n).1 → ℝ),
      (∀ n, C (G n)) ∧ (∀ n, ProbabilityWeights (x n)) ∧
      Tendsto (fun n => weightedProfile (G n).2 (x n)) atTop (𝓝 W) := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hW
  choose G x hC hx he using hu
  refine ⟨G, x, hC, hx, ?_⟩
  have heq : u = fun n => weightedProfile (G n).2 (x n) := funext he
  rwa [heq] at ht

def weightedExtremalProfiles (C : FiniteGraph r → Prop) (Λ : ℝ) : Set (Profile r) :=
  closure (weightedClassProfiles C) ∩ {W | W (edgeTest r) = (r.factorial : ℝ) * Λ}

theorem isCompact_weightedExtremalProfiles (C : FiniteGraph r → Prop) (Λ : ℝ) :
    IsCompact (weightedExtremalProfiles C Λ) :=
  (isCompact_closure_weightedClassProfiles C).inter_right
    (isClosed_eq (continuous_apply _) continuous_const)

def Vanishes (F : Set (FiniteGraph r)) (W : Profile r) : Prop := ∀ A ∈ F, W A = 0

theorem isClosed_vanishes (F : Set (FiniteGraph r)) : IsClosed {W | Vanishes F W} := by
  have h := isClosed_iInter (fun A : FiniteGraph r =>
    isClosed_iInter (fun _ : A ∈ F =>
      (isClosed_eq (continuous_apply A) continuous_const : IsClosed {W : Profile r | W A = 0})))
  simpa only [Vanishes, Set.setOf_forall] using h

def freeLimitProfiles (F : Set (FiniteGraph r)) : Set (Profile r) :=
  {W | IsLimitProfile W ∧ Vanishes F W}

theorem isCompact_freeLimitProfiles (F : Set (FiniteGraph r)) : IsCompact (freeLimitProfiles F) :=
  (isCompact_limitProfiles r).inter_right (isClosed_vanishes F)

/-- The ordinary extremal space, with no quotient or alternative density
definition: forbidden coordinates vanish and the edge coordinate is π(F). -/
def extremalProfiles (F : Finset (FiniteGraph r)) : Set (Profile r) :=
  freeLimitProfiles (F : Set (FiniteGraph r)) ∩ {W | W (edgeTest r) = familyTuranDensity F}

theorem isCompact_extremalProfiles (F : Finset (FiniteGraph r)) : IsCompact (extremalProfiles F) :=
  (isCompact_freeLimitProfiles (F : Set (FiniteGraph r))).inter_right
    (isClosed_eq (continuous_apply _) continuous_const)

theorem IsLimitProfile.power_le_of_hom (W : Profile r) (hW : IsLimitProfile W)
    (A Q : FiniteGraph r) {f : Fin A.1 → Fin Q.1} (hf : A.2.IsHom Q.2 f) :
    W Q ^ ((A.1 + 1) ^ Q.1) ≤ W A := by
  have hc : IsClosed {p : Profile r | p Q ^ ((A.1 + 1) ^ Q.1) ≤ p A} :=
    isClosed_le ((continuous_apply Q).pow _) (continuous_apply A)
  apply closure_minimal _ hc hW
  rintro p ⟨G, hG, rfl⟩
  letI : Nonempty (Fin G.1) := ⟨⟨0, hG⟩⟩
  exact A.2.homDensity_power_le_of_hom Q.2 G.2 hf (A.1 + 1)
    (by simp) (by omega)

theorem IsLimitProfile.vanishes_homomorphicClosure_iff (W : Profile r) (hW : IsLimitProfile W)
    (F : Finset (FiniteGraph r)) :
    Vanishes (TuranUniversality.homomorphicClosure F : Set (FiniteGraph r)) W ↔
      Vanishes (F : Set (FiniteGraph r)) W := by
  constructor
  · intro h A hA
    exact h A (mem_homomorphicClosure_of_mem F hA)
  · intro h Q hQ
    obtain ⟨_, A, hA, him⟩ := (TuranUniversality.mem_homomorphicClosure F Q).mp hQ
    obtain ⟨f, hf⟩ := him.exists_hom
    have hp := hW.power_le_of_hom W A Q hf
    rw [h A hA] at hp
    exact eq_zero_of_pow_eq_zero (le_antisymm hp (pow_nonneg (hW.bounds Q).1 _))

theorem freeLimitProfiles_homomorphicClosure (F : Finset (FiniteGraph r)) :
    freeLimitProfiles (TuranUniversality.homomorphicClosure F : Set (FiniteGraph r)) =
      freeLimitProfiles (F : Set (FiniteGraph r)) := by
  ext W
  constructor
  · intro h
    exact ⟨h.1, (h.1.vanishes_homomorphicClosure_iff W F).mp h.2⟩
  · intro h
    exact ⟨h.1, (h.1.vanishes_homomorphicClosure_iff W F).mpr h.2⟩

theorem extremalProfiles_homomorphicClosure (F : Finset (FiniteGraph r)) (hr : 0 < r) :
    extremalProfiles (TuranUniversality.homomorphicClosure F) = extremalProfiles F := by
  rw [extremalProfiles, extremalProfiles, freeLimitProfiles_homomorphicClosure,
    familyTuranDensity_homomorphicClosure F hr]

theorem closure_homFreeProfiles (F : Finset (FiniteGraph r)) :
    closure (weightedClassProfiles (fun G => familyHomFree F G.2)) =
      freeLimitProfiles (F : Set (FiniteGraph r)) := by
  apply le_antisymm
  · apply closure_minimal _ (isCompact_freeLimitProfiles _).isClosed
    rintro W ⟨G, x, hG, hx, rfl⟩
    refine ⟨isLimitProfile_weighted G.2 x hx, ?_⟩
    intro A hA
    exact A.2.weightedHomDensity_eq_zero_of_homFree G.2 (hG A hA) x
  · intro W hW
    have hB := (hW.1.vanishes_homomorphicClosure_iff W F).mpr hW.2
    obtain ⟨G, hG, hsize, hlim⟩ :=
      isFreeLimit_of_vanishing (TuranUniversality.homomorphicClosure F : Set (FiniteGraph r)) W hW.1 hB
    apply isClosed_closure.mem_of_tendsto hlim
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    apply subset_closure
    refine ⟨G n, fun _ => ((G n).1 : ℝ)⁻¹,
      (familyFree_homomorphicClosure_iff F (G n).2).mp (hG n), ?_, (weightedProfile_uniform _).symm⟩
    refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), ?_⟩
    simp [show (G n).1 ≠ 0 by omega]

theorem edge_le_density_of_freeLimit (F : Finset (FiniteGraph r)) (W : Profile r)
    (hW : W ∈ freeLimitProfiles (F : Set (FiniteGraph r))) :
    W (edgeTest r) ≤ familyTuranDensity F := by
  rw [← closure_homFreeProfiles F] at hW
  apply closure_minimal _ (isClosed_le (continuous_apply _) continuous_const) hW
  rintro W ⟨G, x, hG, hx, rfl⟩
  change (RGraph.oneEdge r).weightedHomDensity G.2 x ≤ _
  rw [RGraph.weightedHomDensity_oneEdge]
  exact familyTuranDensity_lower_of_homFree F G.2 hG x hx

theorem extremalProfiles_nonempty (F : Finset (FiniteGraph r)) (hr : 0 < r)
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) : (extremalProfiles F).Nonempty := by
  have hnon : (freeLimitProfiles (F : Set (FiniteGraph r))).Nonempty := by
    rw [← closure_homFreeProfiles F]
    obtain ⟨m, G, x, hG, hx, _⟩ := zero_mem_familyWeightedValues F hedges
    exact ⟨weightedProfile G x, subset_closure ⟨⟨m, G⟩, x, hG, hx, rfl⟩⟩
  obtain ⟨W, hW, hmax⟩ := (isCompact_freeLimitProfiles (F : Set (FiniteGraph r))).exists_isMaxOn
    hnon (continuous_apply (edgeTest r)).continuousOn
  refine ⟨W, hW, le_antisymm (edge_le_density_of_freeLimit F W hW) ?_⟩
  rw [familyTuranDensity_eq_sSup_weighted F hr hedges]
  apply csSup_le ⟨0, zero_mem_familyWeightedValues F hedges⟩
  rintro z ⟨m, G, x, hG, hx, rfl⟩
  have hm : weightedProfile G x ∈ freeLimitProfiles (F : Set (FiniteGraph r)) := by
    rw [← closure_homFreeProfiles F]
    exact subset_closure ⟨⟨m, G⟩, x, hG, hx, rfl⟩
  have h := hmax hm
  change (RGraph.oneEdge r).weightedHomDensity G x ≤ W (edgeTest r) at h
  rwa [RGraph.weightedHomDensity_oneEdge] at h

end TuranUniversality.SetFamily
