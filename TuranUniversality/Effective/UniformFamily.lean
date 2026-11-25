module

public import TuranUniversality.Effective.UniformAdmissible
public import TuranUniversality.Effective.UniformExtensions
public import TuranUniversality.Uniformity.Transfer

@[expose] public section

/-! # The actual finite forbidden family as a bounded list algorithm -/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

def basisCodes (r : ℕ) (p : Code) : List Code :=
  (boundedCodes r (Uniformity.obstructionBound r p.1)).filter fun g => ¬ Admissible r p g

theorem basisCodes_decode (r : ℕ) (p : Code) :
    ((basisCodes r p).map (decodeFinite r)).toFinset =
      Uniformity.basis (decodeFinite 3 p) r := by
  ext G
  simp only [List.mem_toFinset, List.mem_map, Uniformity.mem_basis]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hbound, hcheck⟩ := List.mem_filter.mp hg
    exact ⟨mem_boundedCodes_size hbound,
      fun h => (of_decide_eq_true hcheck) ((admissible_iff r p g).mpr h)⟩
  · rintro ⟨hbound, hbad⟩
    refine ⟨encodeFinite G, List.mem_filter.mpr
      ⟨encode_mem_boundedCodes G hbound, ?_⟩, decode_encodeFinite G⟩
    apply decide_eq_true
    intro h
    apply hbad
    simpa [decodeFinite, encodeFinite, decode_encode] using
      (admissible_iff r p (encodeFinite G)).mp h

def familyCodes (r : ℕ) (p : Code) : List Code :=
  (basisCodes r p).flatMap (extensionCodes r)

theorem familyCodes_decode (r : ℕ) (p : Code) :
    ((familyCodes r p).map (decodeFinite r)).toFinset =
      Uniformity.family (decodeFinite 3 p) r := by
  ext G
  rw [Uniformity.family, ← basisCodes_decode r p]
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_biUnion]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, hg⟩ := List.mem_flatMap.mp hg
    refine ⟨decodeFinite r a, ⟨a, ha, rfl⟩, ?_⟩
    rw [← extensionCodes_decode r a]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨g, hg, rfl⟩)
  · rintro ⟨A, ⟨a, ha, rfl⟩, hG⟩
    rw [← extensionCodes_decode r a] at hG
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hG)
    exact ⟨g, List.mem_flatMap.mpr ⟨a, ha, hg⟩, rfl⟩

end TuranUniversality.Effective.Uniform
