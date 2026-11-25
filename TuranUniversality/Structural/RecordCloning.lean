module

public import TuranUniversality.Structural.RecordTransport
public import TuranUniversality.Structural.InnerWeights

@[expose] public section

/-! # Cloning actual legal records

The data map may identify vertices. A recorded four-set is retained only when
its image is an actual recorded four-set, so the map is injective on that set.
Ordinary avoidance of the homomorphic closure makes each cloned local inner
object legal, including the isolated vertices of the forbidden graphs.
-/

namespace TuranUniversality.Structural

universe u v

namespace LegalObject

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  {F : Finset (FiniteGraph 3)}

theorem homFree_on_active (O : LegalObject (homomorphicClosure F) W)
    (a : Bool) (A : FiniteGraph 3) (hA : A ∈ homomorphicClosure F)
    (f : Fin A.1 → W) (hf : ∀ v, f v ∈ O.active) :
    ¬ A.2.IsHom (O.inner a) f := by
  classical
  have hfree : familyHomFree (homomorphicClosure F) O.activeProjection :=
    (familyHomFree_homomorphicClosure_iff F O.activeProjection).mpr
      ((familyFree_homomorphicClosure_iff F O.activeProjection).mp O.activeProjection_free)
  intro hh
  let g : Fin A.1 → O.active := fun v => ⟨f v, hf v⟩
  apply hfree A hA
  refine ⟨g, ?_⟩
  intro e he
  apply (O.projection.mem_pullback (Function.Embedding.subtype _) _).mpr
  have hi : (e.image g).map (Function.Embedding.subtype _) = e.image f := by
    simp only [Finset.map_eq_image, Finset.image_image]
    rfl
  have hp : e.image f ∈ O.projection.edges := by
    apply (O.mem_projection _).mpr
    cases a with
    | false => exact Or.inl (hh e he)
    | true => exact Or.inr (hh e he)
  refine ⟨?_, hi ▸ hp⟩
  rw [← Finset.card_map (s := e.image g) (Function.Embedding.subtype _), hi]
  exact O.projection.uniform _ hp

variable [Fintype V]

def cloneOn (O : LegalObject (homomorphicClosure F) W) (f : V → W) (S : Finset V) :
    LegalObject (homomorphicClosure F) V where
  active := S.filter (fun v => f v ∈ O.active)
  inner a :=
    { edges := (Finset.univ.powersetCard 3).filter
        (fun e => e ⊆ S ∧ e.image f ∈ (O.inner a).edges)
      uniform := by
        intro e he
        exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2 }
  supported := by
    intro a e he v hv
    obtain ⟨_, hs, hi⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hs hv,
      O.supported a _ hi (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩
  onePhase := by
    rcases O.onePhase with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  free := by
    intro a A hA g hg hgem
    apply O.homFree_on_active a A hA (f ∘ g)
      (fun v => (Finset.mem_filter.mp (hg v)).2)
    intro e he
    have h := (Finset.mem_filter.mp (hgem.2 e he)).2.2
    simpa only [Finset.image_image, Function.comp_def] using h

@[simp] theorem mem_cloneOn_active (O : LegalObject (homomorphicClosure F) W)
    (f : V → W) (S : Finset V) (v : V) :
    v ∈ (O.cloneOn f S).active ↔ v ∈ S ∧ f v ∈ O.active := by
  simp [cloneOn]

theorem mem_cloneOn_inner (O : LegalObject (homomorphicClosure F) W)
    (f : V → W) (S e : Finset V) (a : Bool) :
    e ∈ ((O.cloneOn f S).inner a).edges ↔
      e.card = 3 ∧ e ⊆ S ∧ e.image f ∈ (O.inner a).edges := by
  simp [cloneOn, Finset.mem_powersetCard]

theorem cloneOn_active_inter (O : LegalObject (homomorphicClosure F) W)
    (f : V → W) (S X : Finset V) (hX : X ⊆ S) :
    (X ∩ (O.cloneOn f S).active).image f = X.image f ∩ O.active := by
  ext w
  simp only [Finset.mem_image, Finset.mem_inter, mem_cloneOn_active]
  constructor
  · rintro ⟨v, ⟨hv, _, ha⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, ha⟩
  · rintro ⟨⟨v, hv, rfl⟩, ha⟩
    exact ⟨v, ⟨hv, hX hv, ha⟩, rfl⟩

theorem cloneOn_labels (O : LegalObject (homomorphicClosure F) W)
    (f : V → W) (S X : Finset V) (hX : X ⊆ S)
    (hinj : Set.InjOn f (X : Set V)) (l : Label) :
    (O.cloneOn f S).Labels X l ↔ O.Labels (X.image f) l := by
  have hi : Set.InjOn f ((X ∩ (O.cloneOn f S).active : Finset V) : Set V) :=
    hinj.mono (by intro v hv; exact (Finset.mem_inter.mp hv).1)
  have hc : (X ∩ (O.cloneOn f S).active).card = (X.image f ∩ O.active).card := by
    rw [← O.cloneOn_active_inter f S X hX, Finset.card_image_of_injOn hi]
  have he (a : Bool) :
      X ∩ (O.cloneOn f S).active ∈ ((O.cloneOn f S).inner a).edges ↔
        X.image f ∩ O.active ∈ (O.inner a).edges := by
    rw [mem_cloneOn_inner, O.cloneOn_active_inter f S X hX]
    constructor
    · exact fun h => h.2.2
    · intro h
      exact ⟨hc.trans ((O.inner a).uniform _ h), Finset.inter_subset_left.trans hX, h⟩
  simp only [Labels, hc, he]

end LegalObject

namespace RecordSystem

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] [Fintype V]

def clone (R : RecordSystem W) (f : V → W) : RecordSystem V where
  recorded :=
    { edges := (Finset.univ.powersetCard 4).filter (fun X => X.image f ∈ R.recorded.edges)
      uniform := by
        intro X hX
        exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hX).1).2 }
  label X := R.label (X.image f)

@[simp] theorem mem_clone (R : RecordSystem W) (f : V → W) (X : Finset V) :
    X ∈ (R.clone f).recorded.edges ↔ X.card = 4 ∧ X.image f ∈ R.recorded.edges := by
  simp [clone, Finset.mem_powersetCard]

theorem clone_injOn (R : RecordSystem W) (f : V → W) (X : Finset V)
    (hX : X ∈ (R.clone f).recorded.edges) : Set.InjOn f (X : Set V) := by
  obtain ⟨hc, he⟩ := (R.mem_clone f X).mp hX
  apply Finset.card_image_iff.mp
  rw [hc, R.recorded.uniform _ he]

theorem LocallyLegal.clone {F : Finset (FiniteGraph 3)} {R : RecordSystem W}
    (h : R.LocallyLegal (homomorphicClosure F)) (f : V → W) :
    (R.clone f).LocallyLegal (homomorphicClosure F) := by
  intro S hS
  obtain ⟨O, hO, hreal⟩ := h (S.image f) (Finset.card_image_le.trans hS)
  refine ⟨O.cloneOn f S, Finset.filter_subset _ _, ?_⟩
  intro X hX hXS
  apply (O.cloneOn_labels f S X hXS (R.clone_injOn f X hX) _).mpr
  exact hreal (X.image f) ((R.mem_clone f X).mp hX).2 (Finset.image_subset_image hXS)

end RecordSystem

end TuranUniversality.Structural
