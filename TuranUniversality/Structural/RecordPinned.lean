module

public import TuranUniversality.Structural.Record

@[expose] public section

/-! # Reconstructing legal inner graphs after the vertex types are fixed

Every obstruction has an actual finite witness: two records for a phase or
edge/nonedge conflict, or the vertices of a forbidden graph together with one
neutral witness per edge.  This is the finite local-to-global step in Claim 7.2.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.RecordSystem

variable {V : Type*} [DecidableEq V]

def failureBound (B : Finset (FiniteGraph 3)) : ℕ :=
  max 8 (B.sup (fun F => F.1 + F.2.edges.card))

theorem failureBound_ge_eight (B : Finset (FiniteGraph 3)) : 8 ≤ failureBound B :=
  le_max_left _ _

theorem failureBound_ge_forbidden (B : Finset (FiniteGraph 3)) {F : FiniteGraph 3}
    (hF : F ∈ B) : F.1 + F.2.edges.card ≤ failureBound B :=
  (Finset.le_sup (f := fun F : FiniteGraph 3 => F.1 + F.2.edges.card) hF).trans
    (le_max_right _ _)

theorem cutoff_eq (B : Finset (FiniteGraph 3)) : cutoff B = 5 + failureBound B := rfl

/-- Each bounded set has a genuine legal realization whose types agree with the
proposed active set on that set.  The realization may contain anchor vertices. -/
def PinnedLocallyLegal (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ N → S.card ≤ failureBound B →
    ∃ O : LegalObject B V, O.Realizes R S ∧
      ∀ v ∈ S, v ∈ O.active ↔ v ∈ U

theorem inter_eq_of_pin {S U A X : Finset V} (hX : X ⊆ S)
    (hp : ∀ v ∈ S, v ∈ A ↔ v ∈ U) : X ∩ A = X ∩ U := by
  ext v
  by_cases hv : v ∈ X
  · simp only [Finset.mem_inter, hv, true_and]
    exact hp v (hX hv)
  · simp [hv]

theorem PinnedLocallyLegal.count {R : RecordSystem V} {B : Finset (FiniteGraph 3)}
    {N U : Finset V} (h : R.PinnedLocallyLegal B N U)
    {X : Finset V} (hX : X ∈ R.recorded.edges) (hXN : X ⊆ N) :
    (X ∩ U).card = (R.label X).count := by
  have hb : X.card ≤ failureBound B := by
    have := failureBound_ge_eight B
    rw [R.recorded.uniform X hX]
    omega
  obtain ⟨O, hO, hp⟩ := h X hXN hb
  have hl := (hO X hX (Finset.Subset.refl X)).1
  rwa [inter_eq_of_pin (Finset.Subset.refl X) hp] at hl

def witnessedEdges (R : RecordSystem V) (N U : Finset V) (a : Bool) : Finset (Finset V) :=
  (R.recorded.edges.filter (fun X => X ⊆ N ∧ (R.label X).phase = some a)).image
    (fun X => X ∩ U)

@[simp] theorem mem_witnessedEdges (R : RecordSystem V) (N U : Finset V)
    (a : Bool) (e : Finset V) :
    e ∈ R.witnessedEdges N U a ↔
      ∃ X, X ∈ R.recorded.edges ∧ X ⊆ N ∧ (R.label X).phase = some a ∧ X ∩ U = e := by
  simp [witnessedEdges, and_assoc]

def witnessedGraph (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (h : R.PinnedLocallyLegal B N U) (a : Bool) : RGraph V 3 where
  edges := R.witnessedEdges N U a
  uniform := by
    intro e he
    obtain ⟨X, hX, hXN, ha, rfl⟩ := (R.mem_witnessedEdges N U a e).mp he
    exact (h.count hX hXN).trans (Label.count_of_phase ha)

theorem witnessedGraph_supported (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (h : R.PinnedLocallyLegal B N U)
    (a : Bool) (e : Finset V) (he : e ∈ (R.witnessedGraph B N U h a).edges) : e ⊆ U := by
  obtain ⟨X, _, _, _, rfl⟩ := (R.mem_witnessedEdges N U a e).mp he
  exact Finset.inter_subset_right

theorem witnessedGraph_onePhase (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (h : R.PinnedLocallyLegal B N U) :
    (R.witnessedGraph B N U h false).edges = ∅ ∨
      (R.witnessedGraph B N U h true).edges = ∅ := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨e, he⟩ := hn.1
  obtain ⟨f, hf⟩ := hn.2
  obtain ⟨X, hX, hXN, hx, _⟩ := (R.mem_witnessedEdges N U false e).mp he
  obtain ⟨Y, hY, hYN, hy, _⟩ := (R.mem_witnessedEdges N U true f).mp hf
  have hb : (X ∪ Y).card ≤ failureBound B := by
    have hc := Finset.card_union_le X Y
    have hbound := failureBound_ge_eight B
    rw [R.recorded.uniform X hX, R.recorded.uniform Y hY] at hc
    omega
  obtain ⟨O, hO, _⟩ := h (X ∪ Y) (Finset.union_subset hXN hYN) hb
  exact O.phase_exclusive _ _
    (((hO X hX Finset.subset_union_left).2 false).mpr hx)
    (((hO Y hY Finset.subset_union_right).2 true).mpr hy)

/-- An inner forbidden copy has a witness on at most `v(F)+e(F)` vertices,
including the images of any isolated vertices of `F`. -/
theorem witnessedGraph_free (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (hU : U ⊆ N) (h : R.PinnedLocallyLegal B N U)
    (a : Bool) (F : FiniteGraph 3) (hF : F ∈ B) (f : Fin F.1 → V)
    (hfa : ∀ v, f v ∈ U) : ¬ F.2.IsEmbedding (R.witnessedGraph B N U h a) f := by
  classical
  intro hf
  have hw (e : F.2.edges) : ∃ X, X ∈ R.recorded.edges ∧ X ⊆ N ∧
      (R.label X).phase = some a ∧ X ∩ U = e.val.image f :=
    (R.mem_witnessedEdges N U a _).mp (hf.2 e.val e.property)
  choose X hX hXN hphase hXU using hw
  let S := (Finset.univ.image f) ∪
    (Finset.univ : Finset F.2.edges).biUnion (fun e => X e \ U)
  have hdiff (e : F.2.edges) : (X e \ U).card = 1 := by
    have hc := R.recorded.uniform (X e) (hX e)
    have hi := (h.count (hX e) (hXN e)).trans (Label.count_of_phase (hphase e))
    have hd := Finset.card_inter_add_card_sdiff (X e) U
    omega
  have hSN : S ⊆ N := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact hU (hfa w)
    · obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hv
      exact hXN e (Finset.mem_sdiff.mp he).1
  have hSbound : S.card ≤ failureBound B := by
    have hc := Finset.card_union_le (Finset.univ.image f)
      ((Finset.univ : Finset F.2.edges).biUnion (fun e => X e \ U))
    have hr : (Finset.univ.image f).card ≤ F.1 := by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin F.1))) (f := f))
    have hd : ((Finset.univ : Finset F.2.edges).biUnion (fun e => X e \ U)).card ≤
        F.2.edges.card := by
      have he := Finset.card_biUnion_le (s := (Finset.univ : Finset F.2.edges))
        (t := fun e => X e \ U)
      simpa only [hdiff, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        smul_eq_mul, mul_one] using he
    have hb := failureBound_ge_forbidden B hF
    dsimp only [S]
    omega
  have hXS (e : F.2.edges) : X e ⊆ S := by
    intro v hv
    by_cases hva : v ∈ U
    · have hi : v ∈ e.val.image f := by rw [← hXU e]; exact Finset.mem_inter.mpr ⟨hv, hva⟩
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hv, hva⟩⟩)
  obtain ⟨O, hO, hp⟩ := h S hSN hSbound
  have hfv (v : Fin F.1) : f v ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  apply O.free a F hF f (fun v => (hp (f v) (hfv v)).mpr (hfa v))
  refine ⟨hf.1, ?_⟩
  intro e he
  let e' : F.2.edges := ⟨e, he⟩
  have hed := ((hO (X e') (hX e') (hXS e')).2 a).mpr (hphase e')
  rwa [inter_eq_of_pin (hXS e') hp, hXU e'] at hed

/-- The reconstructed actual legal object, with no additional edges beyond
those positively witnessed in the records. -/
def pinnedObject (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (hU : U ⊆ N) (h : R.PinnedLocallyLegal B N U) : LegalObject B V where
  active := U
  inner := R.witnessedGraph B N U h
  supported := R.witnessedGraph_supported B N U h
  onePhase := R.witnessedGraph_onePhase B N U h
  free := R.witnessedGraph_free B N U hU h

theorem pinnedObject_realizes (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (hU : U ⊆ N) (h : R.PinnedLocallyLegal B N U) :
    (R.pinnedObject B N U hU h).Realizes R N := by
  intro X hX hXN
  refine ⟨h.count hX hXN, ?_⟩
  intro a
  constructor
  · intro he
    obtain ⟨Y, hY, hYN, hy, heq⟩ :=
      (R.mem_witnessedEdges N U a (X ∩ U)).mp he
    have hb : (X ∪ Y).card ≤ failureBound B := by
      have hc := Finset.card_union_le X Y
      have hbound := failureBound_ge_eight B
      rw [R.recorded.uniform X hX, R.recorded.uniform Y hY] at hc
      omega
    obtain ⟨O, hO, hp⟩ := h (X ∪ Y) (Finset.union_subset hXN hYN) hb
    have hm := ((hO Y hY Finset.subset_union_right).2 a).mpr hy
    have hx := inter_eq_of_pin (X := X) Finset.subset_union_left hp
    have hy' := inter_eq_of_pin (X := Y) Finset.subset_union_right hp
    apply ((hO X hX Finset.subset_union_left).2 a).mp
    rwa [hy', heq, ← hx] at hm
  · intro ha
    exact (R.mem_witnessedEdges N U a (X ∩ U)).mpr ⟨X, hX, hXN, ha, rfl⟩

theorem exists_realization_of_pinned (R : RecordSystem V) (B : Finset (FiniteGraph 3))
    (N U : Finset V) (hU : U ⊆ N) (h : R.PinnedLocallyLegal B N U) :
    ∃ O : LegalObject B V, O.active = U ∧ O.Realizes R N :=
  ⟨R.pinnedObject B N U hU h, rfl, R.pinnedObject_realizes B N U hU h⟩

end TuranUniversality.Structural.RecordSystem
