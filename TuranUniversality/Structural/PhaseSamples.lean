module

public import TuranUniversality.Structural.PhaseRoles
public import TuranUniversality.Density.WeightedHomPushforward
public import TuranUniversality.Density.Box

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Sampled inner patterns determine the outer test

When the active and neutral samples are injective, the finite role model
has exactly the same outer homomorphism predicate as the actual compiled
legal object. The only discarded events are genuine data collisions.
-/

namespace TuranUniversality.Structural.PhaseRoles

open Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable [Fintype U] [Fintype V] {b t : ℕ} {B : Finset (FiniteGraph 3)}

abbrev Neutral (O : LegalObject B V) := {v : V // v ∉ O.active}

def dataMap (O : LegalObject B V) (θ : U → Role b t)
    (a : U → O.active) (w : U → Neutral O) (u : Data θ) : V :=
  if θ u.val = .inr false then (a u.val).val else (w u.val).val

theorem dataMap_active_iff (O : LegalObject B V) (θ : U → Role b t)
    (a : U → O.active) (w : U → Neutral O) (u : Data θ) :
    dataMap O θ a w u ∈ O.active ↔ u ∈ activeSet θ := by
  by_cases h : θ u.val = .inr false
  · simp [dataMap, h, (a u.val).property]
  · simp [dataMap, h, (w u.val).property]

theorem dataMap_eq_active (O : LegalObject B V) (θ : U → Role b t)
    (a : U → O.active) (w : U → Neutral O) (u : Data θ) (hu : u ∈ activeSet θ) :
    dataMap O θ a w u = (a u.val).val := by
  simp only [dataMap, (mem_activeSet θ u).mp hu, if_pos, ite_true]

def sampleMap (O : LegalObject B V) (θ : U → Role b t)
    (a : U → O.active) (w : U → Neutral O) : U → Compiled.Vertex b t V :=
  Compiled.mapData (dataMap O θ a w) ∘ place θ

theorem dataMap_injective (O : LegalObject B V) (θ : U → Role b t)
    (a : U → O.active) (w : U → Neutral O)
    (ha : Function.Injective a) (hw : Function.Injective w) :
    Function.Injective (dataMap O θ a w) := by
  intro u v huv
  unfold dataMap at huv
  split_ifs at huv with hu hv hv
  · exact Subtype.ext (ha (Subtype.ext huv))
  · exact False.elim ((w v.val).property (huv ▸ (a u.val).property))
  · exact False.elim ((w u.val).property (huv.symm ▸ (a v.val).property))
  · exact Subtype.ext (hw (Subtype.ext huv))

theorem sampled_inner_relation (O : LegalObject B V) (θ : U → Role b t) (phase : Bool)
    (a : U → O.active) (w : U → Neutral O)
    (hi : Function.Injective (dataMap O θ a w))
    (e : Finset (Data θ)) (he : e ⊆ activeSet θ) :
    e.map (Function.Embedding.subtype _) ∈
        ((O.inner phase).inverseImage (fun u => (a u).val)).edges ↔
      e.map ⟨dataMap O θ a w, hi⟩ ∈ (O.inner phase).edges := by
  have him : (e.map (Function.Embedding.subtype _)).image (fun u => (a u).val) =
      e.map ⟨dataMap O θ a w, hi⟩ := by
    simp only [Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    exact (dataMap_eq_active O θ a w u (he hu)).symm
  rw [RGraph.mem_inverseImage, him, Finset.card_map]
  constructor
  · exact And.right
  · intro hm
    exact ⟨by simpa using (O.inner phase).uniform _ hm, hm⟩

theorem sampled_compatible_iff (O : LegalObject B V) (θ : U → Role b t) (phase : Bool)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (a : U → O.active) (w : U → Neutral O)
    (hi : Function.Injective (dataMap O θ a w))
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    Compatible Ω phase H θ ((O.inner phase).inverseImage (fun u => (a u).val)) ↔
      H.IsHom (Compiled.graph t Ω O.records) (sampleMap O θ a w) := by
  exact compatible_iff θ phase _ O ⟨dataMap O θ a w, hi⟩
    (dataMap_active_iff O θ a w) hphase (sampled_inner_relation O θ phase a w hi) Ω H

theorem sampled_indicator_eq (O : LegalObject B V) (θ : U → Role b t) (phase : Bool)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (a : U → O.active) (w : U → Neutral O)
    (ha : Function.Injective a) (hw : Function.Injective w)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    H.homIndicator (Compiled.graph t Ω O.records) (sampleMap O θ a w) =
      truth (Compatible Ω phase H θ ((O.inner phase).inverseImage (fun u => (a u).val))) := by
  unfold RGraph.homIndicator truth
  rw [sampled_compatible_iff O θ phase hphase a w (dataMap_injective O θ a w ha hw) Ω H]
  split_ifs <;> rfl

/-- The pointwise error is supported on active or neutral collisions. -/
theorem sampled_indicator_error (O : LegalObject B V) (θ : U → Role b t) (phase : Bool)
    (hphase : ∀ s, s ≠ phase → (O.inner s).edges = ∅)
    (a : U → O.active) (w : U → Neutral O)
    (Ω : Label → Finset (Cube.Word b)) (H : RGraph U (t + (3 * b + 4))) :
    |H.homIndicator (Compiled.graph t Ω O.records) (sampleMap O θ a w) -
      truth (Compatible Ω phase H θ ((O.inner phase).inverseImage (fun u => (a u).val)))| ≤
        truth (¬ Function.Injective a) + truth (¬ Function.Injective w) := by
  classical
  by_cases ha : Function.Injective a
  · by_cases hw : Function.Injective w
    · rw [sampled_indicator_eq O θ phase hphase a w ha hw Ω H]
      simp [truth, ha, hw]
    · simp only [truth, hw, not_false_eq_true, ite_true, ha, not_true_eq_false, ite_false, zero_add]
      unfold RGraph.homIndicator
      split <;> split <;> norm_num
  · simp only [truth, ha, not_false_eq_true, ite_true]
    unfold RGraph.homIndicator
    split <;> split <;> split <;> norm_num

end TuranUniversality.Structural.PhaseRoles
