module

public import TuranUniversality.Computation.FrameConstruction
public import TuranUniversality.Computation.RowInput

/-! # Exact input-prefix checks on the constructed horizontal cycle -/

@[expose] public section

namespace TuranUniversality.Computation.LocalSystem

open Turing Cellular ResetProtocol

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

theorem framedLabel_start {n : ℕ} (s : Fin n → StaticInput.Symbol Γ)
    (r : Segment n Γ Λ) (i : Fin (n + 2)) (h : IsStart (framedLabel s r i)) :
    ∃ k : Fin n, i = centerIndex k ∧ ∃ a, s k = .start a := by
  unfold framedLabel at h
  split_ifs at h with h0 hn
  · exact h.elim
  · exact h.elim
  · let k : Fin n := ⟨i.val - 1, by omega⟩
    refine ⟨k, ?_, ?_⟩
    · apply Fin.ext
      simp only [centerIndex, k]
      omega
    · change IsStart (.cell (s k) (r k)) at h
      cases hs : s k with
      | start a => exact ⟨a, rfl⟩
      | before | input a | finish | after => simp only [hs, IsStart] at h

theorem framedLabel_prefix {n : ℕ} (input : List Γ)
    (s : Fin n → StaticInput.Symbol Γ) (r : Segment n Γ Λ)
    (hv : StaticInput.Valid input (List.ofFn s)) (i : Fin (n + 2))
    (h : IsStart (framedLabel s r i)) (j : ℕ)
    (hj : j < (StaticInput.inputWord input ++ [StaticInput.Symbol.finish]).length) :
    staticPart (framedLabel s r ((finRotate (n + 2))^[j] i)) =
      (StaticInput.inputWord input ++ [StaticInput.Symbol.finish])[j]? := by
  obtain ⟨k, rfl, a, ha⟩ := framedLabel_start s r i h
  have hk : k.val < (List.ofFn s).length := by simpa using k.isLt
  have hs : (List.ofFn s)[k.val]? = some (.start a) := by
    rw [List.getElem?_eq_getElem hk]
    simpa only [List.getElem_ofFn] using congrArg some ha
  have hp := (StaticInput.prefixCheck_positions input (List.ofFn s)).mp hv.2 k.val a hs
  have hlen := hp.length_le
  simp only [List.length_drop, List.length_ofFn] at hlen
  have hkn : k.val + j < n := by omega
  have hrot : (finRotate (n + 2))^[j] (centerIndex k) = centerIndex ⟨k.val + j, hkn⟩ := by
    rw [finRotate_iterate_of_lt (centerIndex k) j (by simp only [centerIndex]; omega)]
    apply Fin.ext
    simp only [centerIndex]
    omega
  rw [hrot, framedLabel_center]
  change some (s ⟨k.val + j, hkn⟩) = _
  have heq := (List.prefix_iff_getElem?).mp hp j hj
  have hks : k.val + j < (List.ofFn s).length := by simpa using hkn
  simpa only [List.getElem?_drop, List.getElem?_eq_getElem hks,
    List.getElem_ofFn, List.getElem?_eq_getElem hj] using heq

end TuranUniversality.Computation.LocalSystem
