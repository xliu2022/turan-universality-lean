module

public import TuranUniversality.Structural.ReadbackTest

@[expose] public section

/-! # Reading the actual complete labels

Neutral four-sets are exactly four-sets avoiding the active vertices.
A witnessed phase label is exactly an inner edge on the active part.
These facts give the converse construction of readback homomorphisms and
recover the inner edges once the root and data roles are known.
-/

namespace TuranUniversality.Structural.Readback

open Cube Support TripleClasses

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable {B : Finset (FiniteGraph 3)}

theorem label_witness_iff (O : LegalObject B V) (X : Finset V) (phase : Bool) :
    O.label X = .inr phase ↔ X ∩ O.active ∈ (O.inner phase).edges := by
  cases phase
  · by_cases hf : X ∩ O.active ∈ (O.inner false).edges
    · simp [LegalObject.label, hf]
    · by_cases ht : X ∩ O.active ∈ (O.inner true).edges <;>
        simp [LegalObject.label, hf, ht]
  · by_cases hf : X ∩ O.active ∈ (O.inner false).edges
    · have ht : X ∩ O.active ∉ (O.inner true).edges :=
        fun ht => O.phase_exclusive _ _ hf ht
      simp [LegalObject.label, hf, ht]
    · simp [LegalObject.label, hf]

theorem label_neutral_iff (O : LegalObject B V) (X : Finset V) (hX : X.card ≤ 4) :
    O.label X = CodePools.neutralLabel ↔ X ∩ O.active = ∅ := by
  constructor
  · intro hl
    have hc := ((O.labels_iff X hX CodePools.neutralLabel).mpr hl).1
    exact Finset.card_eq_zero.mp hc
  · intro he
    apply (O.labels_iff X hX CodePools.neutralLabel).mp
    refine ⟨by simp [he, CodePools.neutralLabel, Label.count], ?_⟩
    intro a
    simp only [CodePools.neutralLabel, Label.phase, reduceCtorEq, iff_false]
    intro hmem
    have hc := (O.inner a).uniform _ hmem
    simp [he] at hc

theorem frame_neutral_vertices (O : LegalObject B V) (d : Fin 5 → V)
    (hd : Function.Injective d)
    (hneutral : ∀ X : Finset (Fin 5), X.card = 4 →
      O.label (X.image d) = CodePools.neutralLabel) : ∀ a, d a ∉ O.active := by
  intro a ha
  obtain ⟨X, hX, haX, _⟩ := Frame.data_pair a a
  have hcard : (X.image d).card ≤ 4 := by rw [Finset.card_image_of_injective _ hd, hX]
  have he := (label_neutral_iff O (X.image d) hcard).mp (hneutral X hX)
  have hm : d a ∈ X.image d ∩ O.active :=
    Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a, haX, rfl⟩, ha⟩
  simpa [he] using hm

theorem witnessed_insert (O : LegalObject B V) (phase : Bool) {e : Finset V}
    (he : e ∈ (O.inner phase).edges) {v : V} (hv : v ∉ O.active) :
    (insert v e).card = 4 ∧ O.label (insert v e) = .inr phase := by
  have hs := O.supported phase e he
  have hv' : v ∉ e := fun h => hv (hs h)
  have hi : insert v e ∩ O.active = e := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hu, ha⟩
      · exact False.elim (hv ha)
      · exact hu
    · intro hu
      exact ⟨Or.inr hu, hs hu⟩
  refine ⟨by rw [Finset.card_insert_of_notMem hv', (O.inner phase).uniform e he], ?_⟩
  apply (label_witness_iff O _ phase).mpr
  rw [hi]
  exact he

theorem pool_label_unique (p q : ℕ) (hpq : p ≤ q) {l k : Label}
    {Z : Finset (Support.Vertex (CodePools.blockCount q))}
    (hl : Z ∈ (poolGraph (CodePools.pool p q hpq l)).edges)
    (hk : Z ∈ (poolGraph (CodePools.pool p q hpq k)).edges) : l = k := by
  obtain ⟨u, hu, hZu⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨v, hv, hZv⟩ := Finset.mem_biUnion.mp hk
  have huv : u = v := word_eq_of_common_edge hZu hZv
  subst v
  by_contra hne
  exact Finset.disjoint_left.mp (CodePools.pools_disjoint p q hpq hne) hu hv

theorem neutral_frame_hom [Fintype V] (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (O : LegalObject B V) (σ : Equiv.Perm (Fin t))
    (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5))
    (hact : Frame.AllowedBlockAction π τ) (d : Fin 5 → V)
    (hd : Function.Injective d) (hdn : ∀ a, d a ∉ O.active) :
    (Frame.graph (CodePools.blockCount q) t (CodePools.pool p q hpq CodePools.neutralLabel)).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) O.records) (Frame.vertexMap σ π τ d) := by
  intro e he
  obtain ⟨X, hX, Z, hZ, rfl⟩ := (Frame.mem_graph _ _).mp he
  rw [Frame.image_edge]
  have hcard : (X.image d).card = 4 := by rw [Finset.card_image_of_injective _ hd, hX]
  have hlabel : O.label (X.image d) = CodePools.neutralLabel := by
    apply (label_neutral_iff O _ hcard.le).mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hv, ha⟩ := Finset.mem_inter.mp hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
    exact hdn a ha
  apply (Compiled.mem_graph _ _ _).mpr
  refine ⟨X.image d, (O.mem_records _).mpr hcard, Z.image (blockMap π τ), ?_, rfl⟩
  change Z.image (blockMap π τ) ∈ (poolGraph (CodePools.pool p q hpq (O.label (X.image d)))).edges
  rw [hlabel]
  exact Frame.allowed_pool_preservation p q hpq π τ hact _ Z hZ

/-- Every allowed root assignment, injective neutral frame assignment and
inner homomorphism yields an actual ordinary readback homomorphism. -/
theorem extend_isHom [Fintype V] (p q : ℕ) (hpq : p ≤ q) {t : ℕ}
    (O : LegalObject B V) (F : RGraph U 3) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (σ : Equiv.Perm (Fin t)) (π : Equiv.Perm (Fin (CodePools.blockCount q)))
    (τ : Fin (CodePools.blockCount q) → Equiv.Perm (Fin 5))
    (hact : Frame.AllowedBlockAction π τ) (d : Fin 5 → V)
    (hd : Function.Injective d) (hdn : ∀ a, d a ∉ O.active)
    (g : U → V) (hg : F.IsHom (O.inner phase) g) :
    (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).IsHom
      (Compiled.graph t (CodePools.pool p q hpq) O.records) (extend σ π τ d g) := by
  apply (isHom_iff _ _ _ _ _ _).mpr
  refine ⟨neutral_frame_hom p q hpq O σ π τ hact d hd hdn, ?_⟩
  intro e he
  rw [image_addedEdge]
  have hc := witnessed_insert O phase (hg e he) (hdn 0)
  apply (Compiled.mem_graph _ _ _).mpr
  refine ⟨insert (d 0) (e.image g), (O.mem_records _).mpr hc.1,
    Z.image (blockMap π τ), ?_, rfl⟩
  change Z.image (blockMap π τ) ∈
    (poolGraph (CodePools.pool p q hpq (O.label (insert (d 0) (e.image g))))).edges
  rw [hc.2]
  exact Frame.allowed_pool_preservation p q hpq π τ hact _ Z hZ

end TuranUniversality.Structural.Readback
