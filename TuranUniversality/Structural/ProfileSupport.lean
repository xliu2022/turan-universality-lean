module

public import TuranUniversality.Structural.ExtremalProfiles
public import TuranUniversality.Density.WeightedCollisions
public import TuranUniversality.Uniformity.Extensions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Source isolated vertices and determination of the full profile

Removing isolated vertices from a test graph preserves every probability
weighted homomorphism density. The identity extends to the actual ordinary
limit space by closure. Thus edged tests without isolated vertices determine
all coordinates; edgeless test coordinates are identically one.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Density

variable {U V W : Type*} [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable [Fintype U] [Fintype V] [Fintype W] {r : ℕ}

theorem sourcePullback_edges (F : RGraph U r) (i : W ↪ U)
    (hs : ∀ e ∈ F.edges, ∀ u ∈ e, u ∈ Set.range i) :
    (F.pullback i).edges.image (fun e => e.map i) = F.edges := by
  rw [F.pullback_edges_image]
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, hs e h⟩⟩

theorem sourcePullback_hom_iff (F : RGraph U r) (G : RGraph V r) (i : W ↪ U)
    (hs : ∀ e ∈ F.edges, ∀ u ∈ e, u ∈ Set.range i) (f : U → V) :
    (F.pullback i).IsHom G (f ∘ i) ↔ F.IsHom G f := by
  constructor
  · intro h e he
    rw [← F.sourcePullback_edges i hs] at he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    simpa only [Finset.map_eq_image, Finset.image_image] using h d hd
  · intro h
    exact h.comp (F.pullback_isHom i)

theorem weightedHomDensity_sourcePullback (F : RGraph U r) (G : RGraph V r) (i : W ↪ U)
    (hs : ∀ e ∈ F.edges, ∀ u ∈ e, u ∈ Set.range i)
    (x : V → ℝ) (hx : ∑ v, x v = 1) :
    F.weightedHomDensity G x = (F.pullback i).weightedHomDensity G x := by
  unfold weightedHomDensity
  calc
    weightedMean x (F.homIndicator G) =
        weightedMean x (fun f : U → V => (F.pullback i).homIndicator G (f ∘ i)) := by
      apply weightedMean_congr
      intro f
      simp only [homIndicator, sourcePullback_hom_iff F G i hs f]
    _ = _ := by
      rw [weightedMean_restrict_mass x i i.injective, hx, one_pow, mul_one]

theorem weightedHomDensity_source_ofRGraph (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (hx : ∑ v, x v = 1) :
    (FiniteGraph.ofRGraph F).2.weightedHomDensity G x = F.weightedHomDensity G x := by
  change (F.pullback (Fintype.equivFin U).symm.toEmbedding).weightedHomDensity G x = _
  exact (weightedHomDensity_sourcePullback F G (Fintype.equivFin U).symm.toEmbedding
    (fun _ _ u _ => (Fintype.equivFin U).symm.surjective u) x hx).symm

theorem weightedHomDensity_edgeless (F : RGraph U r) (hF : F.edges = ∅)
    (G : RGraph V r) (x : V → ℝ) (hx : ∑ v, x v = 1) : F.weightedHomDensity G x = 1 := by
  have hh (f : U → V) : F.IsHom G f := by simp [IsHom, hF]
  have he : F.homIndicator G = (fun _ : U → V => (1 : ℝ)) := by
    funext f
    exact F.homIndicator_of_hom G (hh f)
  rw [weightedHomDensity, he, weightedMean_const x hx]

def sourceSupport (F : RGraph U r) : Finset U := F.edges.biUnion id

@[simp] theorem mem_sourceSupport (F : RGraph U r) (u : U) :
    u ∈ F.sourceSupport ↔ ∃ e ∈ F.edges, u ∈ e := Finset.mem_biUnion

def withoutIsolates (F : RGraph U r) : RGraph F.sourceSupport r :=
  F.pullback (Function.Embedding.subtype _)

theorem edge_subset_sourceSupport (F : RGraph U r) {e : Finset U} (he : e ∈ F.edges) :
    e ⊆ F.sourceSupport := fun u hu => (F.mem_sourceSupport u).mpr ⟨e, he, hu⟩

theorem withoutIsolates_edges (F : RGraph U r) :
    F.withoutIsolates.edges.image (fun e => e.map (Function.Embedding.subtype _)) = F.edges :=
  F.sourcePullback_edges _ (fun e he u hu => ⟨⟨u, F.edge_subset_sourceSupport he hu⟩, rfl⟩)

theorem withoutIsolates_noIsolates (F : RGraph U r) : Uniformity.NoIsolates F.withoutIsolates := by
  intro u
  obtain ⟨e, he, hu⟩ := (F.mem_sourceSupport u.val).mp u.property
  rw [← F.withoutIsolates_edges] at he
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp he
  refine ⟨d, hd, ?_⟩
  rw [← he] at hu
  obtain ⟨v, hv, hvu⟩ := Finset.mem_map.mp hu
  have hvu' : v = u := Subtype.ext hvu
  simpa only [hvu'] using hv

theorem withoutIsolates_has_edges (F : RGraph U r) (hF : F.edges.Nonempty) :
    F.withoutIsolates.edges.Nonempty := by
  rw [← F.withoutIsolates_edges] at hF
  exact Finset.image_nonempty.mp hF

theorem weightedHomDensity_withoutIsolates (F : RGraph U r) (G : RGraph V r)
    (x : V → ℝ) (hx : ∑ v, x v = 1) :
    F.weightedHomDensity G x = F.withoutIsolates.weightedHomDensity G x :=
  F.weightedHomDensity_sourcePullback G _
    (fun e he u hu => ⟨⟨u, F.edge_subset_sourceSupport he hu⟩, rfl⟩) x hx

theorem noIsolates_pullback_equiv (F : RGraph U r) (e : W ≃ U)
    (hF : Uniformity.NoIsolates F) : Uniformity.NoIsolates (F.pullback e.toEmbedding) := by
  intro w
  obtain ⟨d, hd, hw⟩ := hF (e w)
  refine ⟨d.image e.symm, (F.pullback_equiv_inverse e).2 d hd, ?_⟩
  exact Finset.mem_image.mpr ⟨e w, hw, e.symm_apply_apply w⟩

theorem noIsolates_ofRGraph (F : RGraph U r) (hF : Uniformity.NoIsolates F) :
    Uniformity.NoIsolates (FiniteGraph.ofRGraph F).2 :=
  F.noIsolates_pullback_equiv (Fintype.equivFin U).symm hF

theorem ofRGraph_has_edges (F : RGraph U r) (hF : F.edges.Nonempty) :
    (FiniteGraph.ofRGraph F).2.edges.Nonempty := by
  obtain ⟨e, he⟩ := hF
  exact ⟨e.image (Fintype.equivFin U),
    (F.pullback_equiv_inverse (Fintype.equivFin U).symm).2 e he⟩

end TuranUniversality.RGraph

namespace TuranUniversality.SetFamily

variable {r : ℕ}

noncomputable def supportedTest (A : FiniteGraph r) : FiniteGraph r :=
  FiniteGraph.ofRGraph A.2.withoutIsolates

theorem supportedTest_noIsolates (A : FiniteGraph r) :
    Uniformity.NoIsolates (supportedTest A).2 :=
  A.2.withoutIsolates.noIsolates_ofRGraph A.2.withoutIsolates_noIsolates

theorem supportedTest_has_edges (A : FiniteGraph r) (hA : A.2.edges.Nonempty) :
    (supportedTest A).2.edges.Nonempty :=
  A.2.withoutIsolates.ofRGraph_has_edges (A.2.withoutIsolates_has_edges hA)

theorem IsLimitProfile.supportedTest_value (W : Profile r) (hW : IsLimitProfile W)
    (A : FiniteGraph r) : W (supportedTest A) = W A := by
  have hc : IsClosed {p : Profile r | p (supportedTest A) = p A} :=
    isClosed_eq (continuous_apply _) (continuous_apply _)
  apply closure_minimal _ hc hW
  rintro p ⟨G, hG, rfl⟩
  letI : Nonempty (Fin G.1) := ⟨⟨0, hG⟩⟩
  change (supportedTest A).2.homDensity G.2 = A.2.homDensity G.2
  rw [← RGraph.weightedHomDensity_uniform, ← RGraph.weightedHomDensity_uniform]
  have hx := probabilityWeights_uniform (V := Fin G.1)
  rw [supportedTest, RGraph.weightedHomDensity_source_ofRGraph _ _ _ hx.2]
  exact (A.2.weightedHomDensity_withoutIsolates G.2 _ hx.2).symm

theorem IsLimitProfile.edgeless_value (W : Profile r) (hW : IsLimitProfile W)
    (A : FiniteGraph r) (hA : A.2.edges = ∅) : W A = 1 := by
  have hc : IsClosed {p : Profile r | p A = 1} :=
    isClosed_eq (continuous_apply _) continuous_const
  apply closure_minimal _ hc hW
  rintro p ⟨G, hG, rfl⟩
  letI : Nonempty (Fin G.1) := ⟨⟨0, hG⟩⟩
  change A.2.homDensity G.2 = 1
  rw [← RGraph.weightedHomDensity_uniform]
  exact A.2.weightedHomDensity_edgeless hA G.2 _ (probabilityWeights_uniform (V := Fin G.1)).2

theorem IsLimitProfile.ext_of_noIsolates (W Z : Profile r)
    (hW : IsLimitProfile W) (hZ : IsLimitProfile Z)
    (h : ∀ A : FiniteGraph r, A.2.edges.Nonempty → Uniformity.NoIsolates A.2 → W A = Z A) :
    W = Z := by
  funext A
  by_cases hA : A.2.edges.Nonempty
  · rw [← hW.supportedTest_value W A, ← hZ.supportedTest_value Z A]
    exact h (supportedTest A) (supportedTest_has_edges A hA) (supportedTest_noIsolates A)
  · have he : A.2.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [hW.edgeless_value W A he, hZ.edgeless_value Z A he]

end TuranUniversality.SetFamily
