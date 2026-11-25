module

public import TuranUniversality.Effective.StructuralCompilerBounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A joint primitive-recursive compiler for the actual structural family

The seven support pools are fixed finite constants. Both the suspension
count and the raw finite inner family vary as inputs. Malformed rows are
handled by the existing uniform decoder, and duplicate rows are ignored
by the exact set semantics. The output is the literal bounded family of
noncanonical graphs used in the ordinary structural theorem.
-/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform Structural

noncomputable def compiler {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (t : ℕ) (fs : List Code) : List Code :=
  (boundedCodes (t + (3 * b + 4)) (orderCutoff Ω t fs)).filter
    (fun g => ¬ Canonical Ω t (closureCodes 3 fs) g)

theorem compiler_primrec {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : Primrec₂ (compiler Ω) := by
  have hbad : PrimrecRel (fun p : ℕ × List Code => fun g => ¬ Canonical Ω p.1 (closureCodes 3 p.2) g) :=
    ((canonical_primrec Ω).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (closureCodes_primrec.comp (Primrec.const 3) (Primrec.snd.comp Primrec.fst))
        Primrec.snd))).not
  exact (filter_primrec hbad).comp Primrec.id
    (boundedCodes_primrec.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const (3 * b + 4)))
      (orderCutoff_primrec Ω))

theorem compiler_computable {b : ℕ} (Ω : Label → Finset (Cube.Word b)) : Computable₂ (compiler Ω) :=
  (compiler_primrec Ω).to_comp

theorem compiler_decode {b : ℕ} (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k)) (t : ℕ) (fs : List Code) :
    decodeFamily (t + (3 * b + 4)) (compiler Ω t fs) =
      Ordinary.forbidden (decodeFamily 3 fs) Ω t := by
  classical
  ext A
  rw [mem_decodeFamily, Ordinary.mem_forbidden]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hbound, hbad⟩ := List.mem_filter.mp hg
    refine ⟨(mem_boundedCodes_size hbound).trans_eq (orderCutoff_correct Ω t fs), ?_⟩
    intro hh
    apply of_decide_eq_true hbad
    apply (canonical_correct Ω hdis t (closureCodes 3 fs) g).mpr
    rwa [closureCodes_decode]
  · rintro ⟨hbound, hbad⟩
    refine ⟨encodeFinite A, List.mem_filter.mpr ⟨?_, ?_⟩, decode_encodeFinite A⟩
    · apply encode_mem_boundedCodes A
      rw [orderCutoff_correct]
      exact hbound
    · apply decide_eq_true
      intro hh
      apply hbad
      have hs := (canonical_correct Ω hdis t (closureCodes 3 fs) (encodeFinite A)).mp hh
      simpa only [closureCodes_decode, encodeFinite, decode_encode] using hs

end TuranUniversality.Effective.StructuralCodes
