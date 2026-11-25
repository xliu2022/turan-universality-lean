module

public import TuranUniversality.Structural.RecordComplete

@[expose] public section

/-! # Transporting legal objects and records along ordinary injections

Active carriers are transported explicitly, so isolated vertices in the
forbidden inner graphs remain part of ordinary avoidance.
-/

namespace TuranUniversality.Structural

universe u v

namespace LegalObject

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  {B : Finset (FiniteGraph 3)}

def map (O : LegalObject B V) (f : V ↪ W) : LegalObject B W where
  active := O.active.map f
  inner a :=
    { edges := (O.inner a).edges.image (fun e => e.map f)
      uniform := by
        intro e he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
        simpa using (O.inner a).uniform d hd }
  supported := by
    intro a e he w hw
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
    exact Finset.mem_map.mpr ⟨z, O.supported a d hd hz, rfl⟩
  onePhase := by
    rcases O.onePhase with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  free := by
    intro a F hF g hg hgem
    choose lift hlift hf using (fun z => Finset.mem_map.mp (hg z))
    have hinj : Function.Injective lift := by
      intro x y hxy
      apply hgem.1
      rw [← hf x, ← hf y, hxy]
    apply O.free a F hF lift hlift
    refine ⟨hinj, ?_⟩
    intro e he
    obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp (hgem.2 e he)
    have hmap : (e.image lift).map f = e.image g := by
      simp only [Finset.map_eq_image, Finset.image_image]
      exact Finset.image_congr (fun z _ => hf z)
    have heq : d = e.image lift := Finset.map_injective f (hde.trans hmap.symm)
    exact heq ▸ hd

@[simp] theorem mem_map_inner (O : LegalObject B V) (f : V ↪ W) (a : Bool) (e : Finset V) :
    e.map f ∈ ((O.map f).inner a).edges ↔ e ∈ (O.inner a).edges := by
  change e.map f ∈ (O.inner a).edges.image (fun d => d.map f) ↔ _
  constructor
  · intro h
    obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp h
    have heq := Finset.map_injective f hde
    exact heq ▸ hd
  · intro h
    exact Finset.mem_image.mpr ⟨e, h, rfl⟩

theorem map_labels (O : LegalObject B V) (f : V ↪ W) (X : Finset V) (l : Label) :
    (O.map f).Labels (X.map f) l ↔ O.Labels X l := by
  unfold Labels
  change ((X.map f) ∩ (O.active.map f)).card = l.count ∧
    (∀ a, (X.map f) ∩ (O.active.map f) ∈ ((O.map f).inner a).edges ↔ l.phase = some a) ↔ _
  rw [← Finset.map_inter]
  simp only [Finset.card_map, mem_map_inner]

theorem map_label (O : LegalObject B V) (f : V ↪ W) (X : Finset V) (hX : X.card ≤ 4) :
    (O.map f).label (X.map f) = O.label X := by
  exact ((O.map f).labels_label (X.map f) (by simpa using hX)).unique
    ((O.map_labels f X (O.label X)).mpr (O.labels_label X hX))

variable [Fintype V]

def pullback (O : LegalObject B W) (f : V ↪ W) : LegalObject B V where
  active := Finset.univ.filter (fun v => f v ∈ O.active)
  inner a := (O.inner a).pullback f
  supported := by
    intro a e he v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact O.supported a (e.map f) ((RGraph.mem_pullback _ _ _).mp he).2
      (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
  onePhase := by
    rcases O.onePhase with h | h
    · exact Or.inl (by simp [RGraph.pullback, h])
    · exact Or.inr (by simp [RGraph.pullback, h])
  free := by
    intro a F hF g hg hgem
    apply O.free a F hF (f ∘ g)
      (fun v => (Finset.mem_filter.mp (hg v)).2)
    exact ⟨f.injective.comp hgem.1, ((O.inner a).pullback_isHom f).comp hgem.2⟩

@[simp] theorem mem_pullback_active (O : LegalObject B W) (f : V ↪ W) (v : V) :
    v ∈ (O.pullback f).active ↔ f v ∈ O.active := by simp [pullback]

theorem pullback_active_inter (O : LegalObject B W) (f : V ↪ W) (X : Finset V) :
    (X ∩ (O.pullback f).active).map f = X.map f ∩ O.active := by
  ext w
  simp only [Finset.mem_map, Finset.mem_inter, mem_pullback_active]
  constructor
  · rintro ⟨v, ⟨hv, ha⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, ha⟩
  · rintro ⟨⟨v, hv, rfl⟩, ha⟩
    exact ⟨v, ⟨hv, ha⟩, rfl⟩

theorem mem_pullback_inner (O : LegalObject B W) (f : V ↪ W) (a : Bool) (e : Finset V) :
    e ∈ ((O.pullback f).inner a).edges ↔ e.map f ∈ (O.inner a).edges := by
  change e ∈ ((O.inner a).pullback f).edges ↔ _
  rw [RGraph.mem_pullback]
  constructor
  · exact And.right
  · intro h
    exact ⟨by simpa using (O.inner a).uniform _ h, h⟩

theorem pullback_labels (O : LegalObject B W) (f : V ↪ W) (X : Finset V) (l : Label) :
    (O.pullback f).Labels X l ↔ O.Labels (X.map f) l := by
  unfold Labels
  rw [← O.pullback_active_inter f X, Finset.card_map]
  simp only [mem_pullback_inner]

theorem pullback_label (O : LegalObject B W) (f : V ↪ W) (X : Finset V) (hX : X.card ≤ 4) :
    (O.pullback f).label X = O.label (X.map f) := by
  exact ((O.pullback f).labels_label X hX).unique
    ((O.pullback_labels f X _).mpr (O.labels_label _ (by simpa using hX)))

end LegalObject

namespace RecordSystem

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] [Fintype V]

def pullback (R : RecordSystem W) (f : V ↪ W) : RecordSystem V where
  recorded := R.recorded.pullback f
  label X := R.label (X.map f)

theorem mem_pullback (R : RecordSystem W) (f : V ↪ W) (X : Finset V) :
    X ∈ (R.pullback f).recorded.edges ↔ X.map f ∈ R.recorded.edges := by
  change X ∈ (R.recorded.pullback f).edges ↔ _
  rw [RGraph.mem_pullback]
  constructor
  · exact And.right
  · intro h
    exact ⟨by simpa using R.recorded.uniform _ h, h⟩

theorem LocallyLegal.pullback {B : Finset (FiniteGraph 3)} {R : RecordSystem W}
    (h : R.LocallyLegal B) (f : V ↪ W) : (R.pullback f).LocallyLegal B := by
  intro S hS
  obtain ⟨O, hO, hreal⟩ := h (S.map f) (by simpa using hS)
  refine ⟨O.pullback f, ?_, ?_⟩
  · intro v hv
    have hv' := hO ((O.mem_pullback_active f v).mp hv)
    exact (Finset.mem_map' f).mp hv'
  · intro X hX hXS
    apply (O.pullback_labels f X _).mpr
    apply hreal (X.map f) ((R.mem_pullback f X).mp hX)
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_map.mpr ⟨u, hXS hu, rfl⟩

def preSet (f : V ↪ W) (S : Finset W) : Finset V := Finset.univ.filter (fun v => f v ∈ S)

@[simp] theorem mem_preSet (f : V ↪ W) (S : Finset W) (v : V) :
    v ∈ preSet f S ↔ f v ∈ S := by simp [preSet]

@[simp] theorem preSet_map (f : V ↪ W) (S : Finset V) : preSet f (S.map f) = S := by
  ext v
  simp

def map (R : RecordSystem V) (f : V ↪ W) : RecordSystem W where
  recorded :=
    { edges := R.recorded.edges.image (fun X => X.map f)
      uniform := by
        intro Y hY
        obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
        simpa using R.recorded.uniform X hX }
  label X := R.label (preSet f X)

@[simp] theorem map_label (R : RecordSystem V) (f : V ↪ W) (X : Finset V) :
    (R.map f).label (X.map f) = R.label X := by simp [map]

theorem LocallyLegal.map {B : Finset (FiniteGraph 3)} {R : RecordSystem V}
    (h : R.LocallyLegal B) (f : V ↪ W) : (R.map f).LocallyLegal B := by
  intro S hS
  have hpre : (preSet f S).map f ⊆ S := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (mem_preSet f S v).mp hv
  have hcard : (preSet f S).card ≤ RecordSystem.cutoff B := by
    calc
      (preSet f S).card = ((preSet f S).map f).card := (Finset.card_map _).symm
      _ ≤ S.card := Finset.card_le_card hpre
      _ ≤ _ := hS
  obtain ⟨O, hO, hreal⟩ := h (preSet f S) hcard
  refine ⟨O.map f, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (mem_preSet f S v).mp (hO hv)
  · intro Y hY hYS
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
    rw [map_label]
    apply (O.map_labels f X _).mpr
    apply hreal X hX
    intro v hv
    exact (mem_preSet f S v).mpr (hYS (Finset.mem_map.mpr ⟨v, hv, rfl⟩))

end RecordSystem

end TuranUniversality.Structural
