module

public import TuranUniversality.Structural.ReadbackLegality

@[expose] public section

/-! # Recovering the inner data roles from the ordinary test

An added edge already fills every target root role with the images of its
formal roots. Its three remaining vertices therefore map to data. The
no-isolated-vertices hypothesis then recovers the role of every inner
vertex; the witnessed label recovers its actual inner homomorphism.
-/

namespace TuranUniversality.Structural.Readback

open Cube Support TripleClasses

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

theorem extra_images_data_of_edge {b t : ℕ} (pools : Label → Finset (Word b))
    (R : RecordSystem V) (Z : Finset (Support.Vertex b)) (hZ : Z.card = 3 * b)
    (e : Finset U) (f : Vertex b t U → Compiled.Vertex b t V)
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin b))
    (τ : Fin b → Equiv.Perm (Fin 5)) (d : Fin 5 → V)
    (hroles : f ∘ Sum.inl = Frame.vertexMap σ π τ d)
    (he : (addedEdge t Z e).image f ∈ (Compiled.graph t pools R).edges)
    (hinj : Set.InjOn f (addedEdge t Z e : Set (Vertex b t U)))
    (u : U) (hu : u ∈ e) : ∃ v, f (Sum.inr u) = dataVertex v := by
  obtain ⟨Y, hY, W, hW, heq⟩ := (Compiled.mem_graph pools R _).mp he
  have hblock (z : Support.Vertex b) :
      f (.inl (.inr (.inl z))) = .inr (.inl (blockMap π τ z)) :=
    congrFun hroles (.inr (.inl z))
  have hsusp (i : Fin t) : f (.inl (.inl i)) = .inl (σ i) :=
    congrFun hroles (.inl i)
  have hsub : Z.image (blockMap π τ) ⊆ W := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    have hm : Sum.inr (Sum.inl (blockMap π τ z)) ∈ (addedEdge t Z e).image f :=
      Finset.mem_image.mpr ⟨.inl (.inr (.inl z)), by simpa using hz, hblock z⟩
    rw [← heq] at hm
    simpa only [Compiled.mem_edge_block] using hm
  have hsupport : Z.image (blockMap π τ) = W := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ (blockMap_injective π τ), hZ,
      (poolGraph _).uniform W hW]
  have hu' : Sum.inr u ∈ addedEdge t Z e := by simpa using hu
  cases hfu : f (Sum.inr u) with
  | inl i =>
    have hv : Sum.inl (Sum.inl (σ.symm i)) ∈ addedEdge t Z e := by simp
    have hh := hinj hv hu' (by rw [hsusp, hfu, Equiv.apply_symm_apply])
    cases hh
  | inr v =>
    cases v with
    | inl v =>
      have hvm : Sum.inr (Sum.inl v) ∈ (addedEdge t Z e).image f :=
        Finset.mem_image.mpr ⟨.inr u, hu', hfu⟩
      rw [← heq] at hvm
      have hvW : v ∈ W := by simpa only [Compiled.mem_edge_block] using hvm
      rw [← hsupport] at hvW
      obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hvW
      have hv : Sum.inl (Sum.inr (Sum.inl z)) ∈ addedEdge t Z e := by simpa using hz
      have hh := hinj hv hu' (by rw [hblock, hzv, hfu])
      cases hh
    | inr v => exact ⟨v, rfl⟩

theorem innerHom_of_extend_hom [Fintype V] (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    {B : Finset (FiniteGraph 3)} (O : LegalObject B V) (F : RGraph U 3) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5))
    (hact : Frame.AllowedBlockAction π τ) (d : Fin 5 → V)
    (hdn : ∀ a, d a ∉ O.active) (g : U → V)
    (hf : (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) O.records) (extend σ π τ d g)) :
    F.IsHom (O.inner phase) g := by
  intro e he
  have him := hf _ (addedEdge_mem _ _ _ _ F he)
  rw [image_addedEdge] at him
  obtain ⟨Y, hY, W, hW, heq⟩ := (Compiled.mem_graph _ _ _).mp him
  have hp : (W, Y) = (Z.image (blockMap π τ), insert (d 0) (e.image g)) :=
    Compiled.edge_injective heq
  have hWeq : W = Z.image (blockMap π τ) := congrArg Prod.fst hp
  have hYeq : Y = insert (d 0) (e.image g) := congrArg Prod.snd hp
  have hlabel : O.label (insert (d 0) (e.image g)) = .inr phase := by
    have hs := Frame.allowed_pool_preservation p q hpq π τ hact (.inr phase) Z hZ
    rw [hWeq, hYeq] at hW
    exact pool_label_unique p q hpq hW hs
  have hinner := (label_witness_iff O _ phase).mp hlabel
  have hinter : insert (d 0) (e.image g) ∩ O.active = e.image g ∩ O.active := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hv, ha⟩
      · exact False.elim (hdn 0 ha)
      · exact ⟨hv, ha⟩
    · rintro ⟨hv, ha⟩
      exact ⟨Or.inr hv, ha⟩
  rw [hinter] at hinner
  have hcard := (O.inner phase).uniform _ hinner
  have himcard : (e.image g).card ≤ 3 := (Finset.card_image_le).trans_eq (F.uniform e he)
  have heqactive : e.image g ∩ O.active = e.image g :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  simpa only [heqactive] using hinner

/-- Full ordinary-homomorphism normal form of the test. No injectivity of
the inner homomorphism is imposed. -/
theorem hom_normal_form [Fintype V] (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    {B : Finset (FiniteGraph 3)} (O : LegalObject B V) (F : RGraph U 3)
    (hno : Uniformity.NoIsolates F) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (f : Vertex (CodePools.blockCount q) t U → Compiled.Vertex (CodePools.blockCount q) t V)
    (hf : (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) O.records) f) :
    ∃ σ : Equiv.Perm (Fin t), ∃ π : Equiv.Perm (Fin (CodePools.blockCount q)),
      ∃ τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5),
        ∃ (d : Fin 5 → V) (g : U → V), Function.Injective d ∧
          (∀ a, d a ∉ O.active) ∧ Frame.AllowedBlockAction π τ ∧
            F.IsHom (O.inner phase) g ∧ f = extend σ π τ d g := by
  classical
  have hframe := (isHom_iff _ _ _ _ _ f).mp hf |>.1
  obtain ⟨σ, π, τ, d, hd, hroles, hact, hneutral⟩ := Frame.rigidity p q hpq hq hframe
  have hdn := frame_neutral_vertices O d hd (fun X hX => (hneutral X hX).2)
  have hex (u : U) : ∃ v, f (Sum.inr u) = dataVertex v := by
    obtain ⟨e, he, hue⟩ := hno u
    have hmem := addedEdge_mem t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F he
    exact extra_images_data_of_edge (CodePools.pool p q hpq) O.records Z
      ((poolGraph _).uniform Z hZ) e f σ π τ d hroles
      (hf _ hmem) (hf.injOn_edge hmem) u hue
  choose g hg using hex
  have hfeq : f = extend σ π τ d g := by
    funext u
    cases u with
    | inl v => exact congrFun hroles v
    | inr u => exact hg u
  refine ⟨σ, π, τ, d, g, hd, hdn, hact, ?_, hfeq⟩
  apply innerHom_of_extend_hom p q hpq O F phase Z hZ σ π τ hact d hdn g
  exact hfeq ▸ hf

end TuranUniversality.Structural.Readback
