module

public import TuranUniversality.Effective.StructuralLocalPrimrec
public import TuranUniversality.Effective.NaturalArithmetic
public import TuranUniversality.Structural.OrdinaryFamily

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact primitive-recursive bounds and the rooted forbidden basis -/

open scoped BigOperators

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform FiniteApproximation Structural

def geometricSum (a n : ℕ) : ℕ := ((List.range n).map fun j => a ^ j).sum

theorem geometricSum_eq (a n : ℕ) : geometricSum a n = ∑ j ∈ Finset.range n, a ^ j := by
  induction n with
  | zero => simp [geometricSum]
  | succ n ih => simpa [geometricSum, List.range_succ, Finset.sum_range_succ] using congrArg (· + a ^ n) ih

theorem geometricSum_primrec : Primrec₂ geometricSum := by
  have hsum : Primrec (List.sum (α := ℕ)) :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
        (fun xs => by induction xs <;> simp_all)
  exact hsum.comp (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    (power_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

def witnessBound (b t : ℕ) (fs : List Code) : ℕ := t + 5 * b + cutoff fs

def obstructionBound (b t : ℕ) (fs : List Code) : ℕ :=
  witnessBound b t fs * geometricSum ((t + 5 * b) * witnessBound b t fs) (t + 5 * b + 1)

theorem witnessBound_correct (b t : ℕ) (fs : List Code) :
    witnessBound b t fs = Rooted.witnessBound b t (decodeFamily 3 fs) := by
  rw [witnessBound, cutoff_correct, Rooted.witnessBound]

theorem obstructionBound_correct (b t : ℕ) (fs : List Code) :
    obstructionBound b t fs = Rooted.obstructionBound b t (decodeFamily 3 fs) := by
  rw [obstructionBound, witnessBound_correct, geometricSum_eq, Rooted.obstructionBound]

theorem witnessBound_primrec (b : ℕ) : Primrec₂ (witnessBound b) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const (5 * b)))
    (cutoff_primrec.comp Primrec.snd)

theorem obstructionBound_primrec (b : ℕ) : Primrec₂ (obstructionBound b) :=
  Primrec.nat_mul.comp (witnessBound_primrec b)
    (geometricSum_primrec.comp (Primrec.nat_mul.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const (5 * b))) (witnessBound_primrec b))
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const (5 * b))) (Primrec.const 1)))

noncomputable def basisCodes {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) : List Code :=
  (boundedCodes (t + (3 * b + 4)) (obstructionBound b t fs)).filter fun g => ¬ Admits Ω t fs g

theorem basisCodes_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : Primrec₂ (basisCodes Ω) := by
  have hbad : PrimrecRel (fun p : ℕ × List Code => fun g => ¬ Admits Ω p.1 p.2 g) :=
    ((admits_primrec Ω).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).not
  exact (filter_primrec hbad).comp Primrec.id
    (boundedCodes_primrec.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const (3 * b + 4)))
      (obstructionBound_primrec b))

theorem basisCodes_decode {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) :
    decodeFamily (t + (3 * b + 4)) (basisCodes Ω t fs) = Rooted.basis (decodeFamily 3 fs) Ω t := by
  classical
  ext A
  rw [mem_decodeFamily, Rooted.mem_basis]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hbound, hbad⟩ := List.mem_filter.mp hg
    exact ⟨(mem_boundedCodes_size hbound).trans_eq (obstructionBound_correct b t fs),
      fun hh => of_decide_eq_true hbad ((admits_correct Ω t fs g).mpr hh)⟩
  · rintro ⟨hbound, hbad⟩
    refine ⟨encodeFinite A, List.mem_filter.mpr ⟨?_, ?_⟩, decode_encodeFinite A⟩
    · apply encode_mem_boundedCodes A
      rw [obstructionBound_correct]
      exact hbound
    · apply decide_eq_true
      intro hh
      apply hbad
      have hs := (admits_correct Ω t fs (encodeFinite A)).mp hh
      simpa only [encodeFinite, decode_encode] using hs

noncomputable def basisExtensionMax {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) : ℕ :=
  listMax ((basisCodes Ω t fs).map fun g => Uniformity.extensionBound (t + (3 * b + 4)) g.1)

theorem basisExtensionMax_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) :
    basisExtensionMax Ω t fs = (Rooted.basis (decodeFamily 3 fs) Ω t).sup
      (fun A => Uniformity.extensionBound (t + (3 * b + 4)) A.1) := by
  classical
  rw [← basisCodes_decode Ω t fs]
  apply Nat.le_antisymm
  · apply (listMax_le_iff _ _).mpr
    intro n hn
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
    exact Finset.le_sup (f := fun A : FiniteGraph (t + (3 * b + 4)) =>
      Uniformity.extensionBound (t + (3 * b + 4)) A.1)
      ((mem_decodeFamily _ _ _).mpr ⟨g, hg, rfl⟩)
  · apply Finset.sup_le
    intro A hA
    obtain ⟨g, hg, rfl⟩ := (mem_decodeFamily _ _ A).mp hA
    exact le_listMax (List.mem_map.mpr ⟨g, hg, rfl⟩)

theorem basisExtensionMax_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) :
    Primrec₂ (basisExtensionMax Ω) :=
  listMax_primrec.comp (Primrec.list_map (basisCodes_primrec Ω)
    (extensionBound_primrec.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const (3 * b + 4)))
      (Primrec.fst.comp Primrec.snd)).to₂)

noncomputable def orderCutoff {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) : ℕ :=
  max (basisExtensionMax Ω t (closureCodes 3 fs))
    ((t + (3 * b + 4)) ^ 2 * (t + 5 * b + 1) * max 2 (7 * (cutoff fs).choose 4) + 2)

theorem orderCutoff_correct {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) :
    orderCutoff Ω t fs = Ordinary.orderCutoff (decodeFamily 3 fs) Ω t := by
  rw [orderCutoff, basisExtensionMax_correct, closureCodes_decode, cutoff_correct,
    Ordinary.orderCutoff, Ordinary.roleWitnessEdges, RecordSystem.cutoff_homomorphicClosure]

theorem orderCutoff_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) :
    Primrec₂ (orderCutoff Ω) := by
  have hr : Primrec (fun p : ℕ × List Code => p.1 + (3 * b + 4)) :=
    Primrec.nat_add.comp Primrec.fst (Primrec.const (3 * b + 4))
  have hm : Primrec (fun p : ℕ × List Code => p.1 + 5 * b + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const (5 * b))) (Primrec.const 1)
  have hQ : Primrec (fun p : ℕ × List Code => max 2 (7 * (cutoff p.2).choose 4)) :=
    Primrec.nat_max.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 7)
      ((choose_fixed_primrec 4).comp (cutoff_primrec.comp Primrec.snd)))
  exact Primrec.nat_max.comp ((basisExtensionMax_primrec Ω).comp Primrec.fst
    (closureCodes_primrec.comp (Primrec.const 3) Primrec.snd))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (power_primrec.comp hr (Primrec.const 2)) hm) hQ) (Primrec.const 2))

end TuranUniversality.Effective.StructuralCodes
