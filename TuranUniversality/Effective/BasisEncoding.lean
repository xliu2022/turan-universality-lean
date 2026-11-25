module

public import TuranUniversality.Effective.GraphEncoding

/-! # The exact code-level bounded filtering algorithm -/

@[expose] public section

namespace TuranUniversality.Effective

variable {A : Type*} [Primcodable A]

/-- The actual output list of codes, retaining precisely the rejected graphs. -/
def filteredGraphCodes (B : A → ℕ) (reject : A → GraphCode → Bool) (a : A) : List GraphCode :=
  (boundedGraphCodes (B a)).filter (reject a)

theorem filteredGraphCodes_primrec (B : A → ℕ) (reject : A → GraphCode → Bool)
    (hB : Primrec B) (hr : Primrec₂ reject) : Primrec (filteredGraphCodes B reject) := by
  have hp : PrimrecRel (fun a g => reject a g = true) :=
    Primrec.eq.comp hr (Primrec.const true)
  exact ((filter_primrec hp).comp Primrec.id (boundedGraphCodes_primrec.comp hB)).of_eq
    (fun a => by congr 1)

/-- Semantic verification of the code algorithm against the actual finite
forbidden basis.  The separate primitive-recursiveness theorem above requires
a proved primitive-recursive rejection procedure, not merely decidability. -/
theorem filteredGraphCodes_decode (C : A → FiniteGraph 3 → Prop)
    [∀ a, DecidablePred (C a)] (B : A → ℕ) (reject : A → GraphCode → Bool)
    (hr : ∀ a g, reject a g = true ↔ ¬ C a (decodeGraphCode g)) (a : A) :
    ((filteredGraphCodes B reject a).map decodeGraphCode).toFinset =
      FiniteGraph.forbiddenBasis (C a) (B a) := by
  ext G
  simp only [List.mem_toFinset, List.mem_map, filteredGraphCodes,
    List.mem_filter, FiniteGraph.mem_forbiddenBasis]
  constructor
  · rintro ⟨g, ⟨hg, hrej⟩, rfl⟩
    exact ⟨mem_boundedGraphCodes_size hg, (hr a g).mp hrej⟩
  · rintro ⟨hsize, hbad⟩
    refine ⟨encodeFiniteGraph G,
      ⟨encode_mem_boundedGraphCodes G hsize, ?_⟩, decode_encode_finiteGraph G⟩
    apply (hr a _).mpr
    simpa using hbad

end TuranUniversality.Effective
