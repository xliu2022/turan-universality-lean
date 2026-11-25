module

public import TuranUniversality.Computation.Restriction
public import TuranUniversality.Computation.DecidableRules

/-!
# Bounded witnesses for failure of the actual local conditions

All witnesses include the intermediate colors of their indexed matching
edges.  No distinctness convention is imposed on witnesses.  The only
input-dependent clause follows a path shorter than the given prefix.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

variable {D E Alphabet : Type*} [DecidableEq D] [DecidableEq E] [DecidableEq Alphabet]

/-- A uniform bound for the retained data vertices of a failed local rule. -/
def Specification.witnessBound (P : Specification Alphabet) : ℕ :=
  11 + 2 * P.inputPrefix.length

namespace Realization

variable (A : Realization D Alphabet) (P : Specification Alphabet)

theorem legal_of_small_restrictions
    (h : ∀ U : Finset D, U.card ≤ P.witnessBound → (A.restrict U).Legal P) :
    A.Legal P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x e n y z hxe hxn hey hnz
    obtain ⟨b₁, hj₁, hr₁⟩ := hxe
    obtain ⟨b₂, hj₂, hs₂⟩ := hxn
    obtain ⟨b₃, hj₃, hs₃⟩ := hey
    obtain ⟨b₄, hj₄, hr₄⟩ := hnz
    let U := [x, e, n, y, z, b₁, b₂, b₃, b₄].toFinset
    have hc := [x, e, n, y, z, b₁, b₂, b₃, b₄].toFinset_card_le
    change U.card ≤ 9 at hc
    have hU := h U (by unfold Specification.witnessBound; omega)
    exact hU.1 x e n y z
      (A.retain_h hj₁ hr₁ (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_v hj₂ hs₂ (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_v hj₃ hs₃ (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_h hj₄ hr₄ (by simp [U]) (by simp [U]) (by simp [U]))
  · intro l x r x' al ax ar b hlx hxr hxx' hll hlx' hlr hlx''
    obtain ⟨b₁, hj₁, hr₁⟩ := hlx
    obtain ⟨b₂, hj₂, hr₂⟩ := hxr
    obtain ⟨b₃, hj₃, hs₃⟩ := hxx'
    obtain ⟨bl, hjl, hll⟩ := hll
    obtain ⟨bx, hjx, hlx'⟩ := hlx'
    obtain ⟨br, hjr, hlr⟩ := hlr
    obtain ⟨bx', hjx', hlx''⟩ := hlx''
    let U := [l, x, r, x', b₁, b₂, b₃, bl, bx, br, bx'].toFinset
    have hc := [l, x, r, x', b₁, b₂, b₃, bl, bx, br, bx'].toFinset_card_le
    change U.card ≤ 11 at hc
    have hU := h U (by unfold Specification.witnessBound; omega)
    exact hU.2.1 l x r x' al ax ar b
      (A.retain_h hj₁ hr₁ (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_h hj₂ hr₂ (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_v hj₃ hs₃ (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_lab hjl hll (by simp [U]) (by simp [U]))
      (A.retain_lab hjx hlx' (by simp [U]) (by simp [U]))
      (A.retain_lab hjr hlr (by simp [U]) (by simp [U]))
      (A.retain_lab hjx' hlx'' (by simp [U]) (by simp [U]))
  · intro x y a b hxy hxa hyb
    obtain ⟨c, hj, hr⟩ := hxy
    obtain ⟨bx, hjx, hlx⟩ := hxa
    obtain ⟨by', hjy, hly⟩ := hyb
    let U := [x, y, c, bx, by'].toFinset
    have hc := [x, y, c, bx, by'].toFinset_card_le
    change U.card ≤ 5 at hc
    have hU := h U (by unfold Specification.witnessBound; omega)
    exact hU.2.2.1 x y a b
      (A.retain_h hj hr (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_lab hjx hlx (by simp [U]) (by simp [U]))
      (A.retain_lab hjy hly (by simp [U]) (by simp [U]))
  · intro a ha y sy sa hya hys has
    obtain ⟨b, hj, hr⟩ := hya
    obtain ⟨by', hjy, hly⟩ := hys
    obtain ⟨ba, hja, hla⟩ := has
    let U := [a, y, b, by', ba].toFinset
    have hc := [a, y, b, by', ba].toFinset_card_le
    change U.card ≤ 5 at hc
    have hU := h U (by unfold Specification.witnessBound; omega)
    exact hU.2.2.2.1 a (by simp [ha, U]) y sy sa
      (A.retain_h hj hr (by simp [U]) (by simp [U]) (by simp [U]))
      (A.retain_lab hjy hly (by simp [U]) (by simp [U]))
      (A.retain_lab hja hla (by simp [U]) (by simp [U]))
  · intro x sx hxs ht j hj z sz hp hzs
    obtain ⟨bx, hjx, hlx⟩ := hxs
    obtain ⟨bz, hjz, hlz⟩ := hzs
    obtain ⟨U, hc, hxU, hzU, hpU⟩ := A.path_small_support hp
    let W := insert bx (insert bz U)
    have hUW : U ⊆ W := by intro a ha; simp [W, ha]
    have hcW : W.card ≤ U.card + 2 :=
      (Finset.card_insert_le _ _).trans (by have := Finset.card_insert_le bz U; omega)
    have hW := h W (by unfold Specification.witnessBound; omega)
    exact hW.2.2.2.2 x sx
      (A.retain_lab hjx hlx (hUW hxU) (by simp [W])) ht j hj z sz
      (A.path_restrict_mono hUW hpU)
      (A.retain_lab hjz hlz (hUW hzU) (by simp [W]))

/-- Failure is witnessed on at most `11 + 2 * prefix.length` data vertices. -/
theorem exists_small_failure (h : ¬A.Legal P) :
    ∃ U : Finset D, U.card ≤ P.witnessBound ∧ ¬(A.restrict U).Legal P := by
  classical
  by_contra hn
  apply h
  apply A.legal_of_small_restrictions P
  intro U hU
  by_contra hb
  exact hn ⟨U, hU, hb⟩

/-- A failed positive-witness condition persists in every containing realization. -/
theorem failure_persists {B : Realization E Alphabet} (F : Pullback A B)
    (h : ¬A.Legal P) : ¬B.Legal P := fun hB => h (F.legal P hB)

end Realization
end TuranUniversality.Computation.MatchingSystem
