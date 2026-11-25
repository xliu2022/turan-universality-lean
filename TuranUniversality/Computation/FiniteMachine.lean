module

public import TuranUniversality.Computation.TapeMachine

/-!
# Restricting a supported machine to genuinely finitely many states

A finite closed set of reachable states can be made into the literal state type
of a machine without changing whether a run halts.  This removes the infinite
ambient label types used by Mathlib's compiler from the universal interpreter.
-/

@[expose] public section

namespace TuranUniversality.Computation

open Turing
open Nat.Partrec (Code)

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a tape machine to a finite closed state set containing its start
state.  The existential `Inhabited` instance specifies the same initial state. -/
theorem finiteSupport_restriction {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S) :
    ∃ (initial : Inhabited {q // q ∈ S})
      (N : @TM0.Machine Γ {q // q ∈ S} initial),
      ∀ l : List Γ,
        (@TM0.eval Γ {q // q ∈ S} initial inferInstance N l).Dom ↔
          (TM0.eval M l).Dom := by
  classical
  have h0 : (default : Λ) ∈ S := hS.1
  let initial : Inhabited {q // q ∈ S} := ⟨⟨default, hS.1⟩⟩
  let idΓ : PointedMap Γ Γ := ⟨id, rfl⟩
  let clamp : PointedMap Λ {q // q ∈ S} :=
    ⟨fun q => if h : q ∈ S then ⟨q, h⟩ else default,
      by rw [dite_eq_left h0]; rfl⟩
  have hclamp : ∀ q ∈ (↑S : Set Λ), (clamp q).val = q := by
    intro q hq
    have hq' : q ∈ S := hq
    simp [clamp, hq']
  let N : TM0.Machine Γ {q // q ∈ S} :=
    M.map idΓ idΓ clamp Subtype.val
  refine ⟨initial, N, fun l => ?_⟩
  have hinit :
      (TM0.init l : TM0.Cfg Γ Λ).map idΓ clamp =
        (TM0.init l : TM0.Cfg Γ {q // q ∈ S}) := by
    simpa [idΓ] using TM0.map_init idΓ clamp l
  have hsim := M.map_respects idΓ idΓ clamp Subtype.val hS (fun _ => rfl) hclamp
  exact StateTransition.tr_eval_dom hsim ⟨hS.1, hinit⟩

/-- One universal tape machine has a literal finite state type, not only a
finite set of reachable states inside an infinite ambient type. -/
theorem exists_finite_universal_tapeMachine :
    ∃ (c : ToPartrec.Code)
      (initial : Inhabited {q // q ∈ tapeStateSupport c})
      (M : @TM0.Machine TapeAlphabet {q // q ∈ tapeStateSupport c} initial),
      ∀ e : Code,
        (@TM0.eval TapeAlphabet {q // q ∈ tapeStateSupport c} initial inferInstance
          M (tapeInput (Encodable.encode e))).Dom ↔ Halts e := by
  obtain ⟨c, hc⟩ := exists_universal_tapeProgram
  let _ : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  obtain ⟨initial, M, hM⟩ :=
    finiteSupport_restriction tapeProgram (tapeStateSupport c) (tapeStateSupport_closed c)
  refine ⟨c, initial, M, fun e => ?_⟩
  exact (hM (tapeInput (Encodable.encode e))).trans (hc e)

/-- The exact binary-word evaluator has a fixed ordinary machine with a finite
state type and the fixed finite tape alphabet. -/
theorem exists_finite_word_tapeMachine :
    ∃ (c : ToPartrec.Code)
      (initial : Inhabited {q // q ∈ tapeStateSupport c})
      (M : @TM0.Machine TapeAlphabet {q // q ∈ tapeStateSupport c} initial),
      ∀ w : BinaryWord,
        (@TM0.eval TapeAlphabet {q // q ∈ tapeStateSupport c} initial inferInstance
          M (tapeInput (encodeWord w))).Dom ↔ WordHalts w := by
  obtain ⟨c, hc⟩ := exists_word_tapeProgram
  let _ : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  obtain ⟨initial, M, hM⟩ :=
    finiteSupport_restriction tapeProgram (tapeStateSupport c) (tapeStateSupport_closed c)
  refine ⟨c, initial, M, fun w => ?_⟩
  exact (hM (tapeInput (encodeWord w))).trans (hc w)

end TuranUniversality.Computation
