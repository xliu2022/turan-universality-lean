module

public import TuranUniversality.Effective.StructuralObjectsPrimrec
public import TuranUniversality.Structural.ClosureCutoff

@[expose] public section

/-! # Exact effective local cutoff, retaining forbidden isolated vertices -/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform FiniteApproximation Structural

def maxOrderEdges (fs : List Code) : ℕ := listMax (fs.map fun f => f.1 + edgeCount 3 f)

theorem maxOrderEdges_correct (fs : List Code) :
    maxOrderEdges fs = (decodeFamily 3 fs).sup (fun F => F.1 + F.2.edges.card) := by
  classical
  apply Nat.le_antisymm
  · apply (listMax_le_iff _ _).mpr
    intro n hn
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
    rw [edgeCount_eq_card]
    exact Finset.le_sup (f := fun F : FiniteGraph 3 => F.1 + F.2.edges.card)
      ((mem_decodeFamily 3 fs _).mpr ⟨g, hg, rfl⟩)
  · apply Finset.sup_le
    intro F hF
    obtain ⟨g, hg, rfl⟩ := (mem_decodeFamily 3 fs F).mp hF
    change g.1 + (decode 3 g).edges.card ≤ _
    rw [← edgeCount_eq_card]
    exact le_listMax (List.mem_map.mpr ⟨g, hg, rfl⟩)

def cutoff (fs : List Code) : ℕ := 5 + max 8 (maxOrderEdges fs)

theorem cutoff_correct (fs : List Code) : cutoff fs = RecordSystem.cutoff (decodeFamily 3 fs) := by
  rw [cutoff, maxOrderEdges_correct, RecordSystem.cutoff]

theorem maxOrderEdges_primrec : Primrec maxOrderEdges :=
  listMax_primrec.comp (Primrec.list_map Primrec.id
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (edgeCount_primrec.comp (Primrec.const 3) Primrec.snd)).to₂)

theorem cutoff_primrec : Primrec cutoff :=
  Primrec.nat_add.comp (Primrec.const 5)
    (Primrec.nat_max.comp (Primrec.const 8) maxOrderEdges_primrec)

theorem cutoff_closureCodes (fs : List Code) : cutoff (closureCodes 3 fs) = cutoff fs := by
  rw [cutoff_correct, closureCodes_decode, RecordSystem.cutoff_homomorphicClosure, ← cutoff_correct]

end TuranUniversality.Effective.StructuralCodes
