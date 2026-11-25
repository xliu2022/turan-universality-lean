module

public import TuranUniversality.Structural.Record

@[expose] public section

/-! # The actual inner projection of a legal record object -/

namespace TuranUniversality.Structural.LegalObject

variable {V : Type*} [DecidableEq V] {B : Finset (FiniteGraph 3)}

def projection (O : LegalObject B V) : RGraph V 3 where
  edges := (O.inner false).edges ∪ (O.inner true).edges
  uniform := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact (O.inner false).uniform e h
    · exact (O.inner true).uniform e h

@[simp] theorem mem_projection (O : LegalObject B V) (e : Finset V) :
    e ∈ O.projection.edges ↔ e ∈ (O.inner false).edges ∨ e ∈ (O.inner true).edges :=
  Finset.mem_union

theorem projection_supported (O : LegalObject B V) (e : Finset V)
    (he : e ∈ O.projection.edges) : e ⊆ O.active := by
  rcases (O.mem_projection e).mp he with h | h
  · exact O.supported false e h
  · exact O.supported true e h

theorem projection_eq_inner (O : LegalObject B V) : ∃ a, O.projection = O.inner a := by
  rcases O.onePhase with h | h
  · exact ⟨true, RGraph.ext (by simp [projection, h])⟩
  · exact ⟨false, RGraph.ext (by simp [projection, h])⟩

theorem projection_free (O : LegalObject B V) (F : FiniteGraph 3) (hF : F ∈ B)
    (f : Fin F.1 → V) (hactive : ∀ v, f v ∈ O.active) :
    ¬ F.2.IsEmbedding O.projection f := by
  obtain ⟨a, h⟩ := O.projection_eq_inner
  rw [h]
  exact O.free a F hF f hactive

def activeProjection (O : LegalObject B V) : RGraph O.active 3 :=
  O.projection.pullback (Function.Embedding.subtype _)

theorem activeProjection_free (O : LegalObject B V) : familyFree B O.activeProjection := by
  intro F hF hf
  obtain ⟨f, hf⟩ := hf
  have hemb : O.activeProjection.IsEmbedding O.projection Subtype.val :=
    ⟨Subtype.val_injective, O.projection.pullback_isHom (Function.Embedding.subtype _)⟩
  exact O.projection_free F hF (Subtype.val ∘ f) (fun v => (f v).property) (hemb.comp hf)

end TuranUniversality.Structural.LegalObject
