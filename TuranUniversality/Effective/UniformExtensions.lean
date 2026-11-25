module

public import TuranUniversality.Effective.UniformMaps
public import TuranUniversality.Uniformity.Extensions

@[expose] public section

/-! # A numeric test for genuine pair-covering extensions -/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

def CoveredPair (r : ℕ) (g : Code) (a b : ℕ) : Prop :=
  ∃ w ∈ allRows r g.1, Edge r g w ∧ a ∈ w ∧ b ∈ w

instance (r : ℕ) (g : Code) (a b : ℕ) : Decidable (CoveredPair r g a b) := by
  unfold CoveredPair
  infer_instance

theorem coveredPair_iff (r : ℕ) (g : Code) (a b : Fin g.1) :
    CoveredPair r g a.val b.val ↔
      ∃ e ∈ (decode r g).edges, a ∈ e ∧ b ∈ e := by
  constructor
  · rintro ⟨w, _, hw, ha, hb⟩
    exact ⟨rowSet g.1 w, edge_rowSet r g w hw,
      (mem_rowSet g.1 w a).mpr ha, (mem_rowSet g.1 w b).mpr hb⟩
  · rintro ⟨e, he, ha, hb⟩
    have hw := edge_canonical r g e he
    refine ⟨e.toList.map Fin.val,
      (mem_allRows r g.1 _).mpr ⟨hw.1.1, hw.1.2.2⟩, hw, ?_, ?_⟩ <;>
      simpa [Fin.val_inj] using ‹_ ∈ e›

def NoIsolates (r : ℕ) (g : Code) : Prop :=
  ∀ a < g.1, CoveredPair r g a a

instance (r : ℕ) (g : Code) : Decidable (NoIsolates r g) := by
  unfold NoIsolates
  infer_instance

theorem noIsolates_iff (r : ℕ) (g : Code) :
    NoIsolates r g ↔ Uniformity.NoIsolates (decode r g) := by
  constructor
  · intro h a
    obtain ⟨e, he, ha, _⟩ := (coveredPair_iff r g a a).mp (h a.val a.isLt)
    exact ⟨e, he, ha⟩
  · intro h a ha
    obtain ⟨e, he, hea⟩ := h ⟨a, ha⟩
    exact (coveredPair_iff r g ⟨a, ha⟩ ⟨a, ha⟩).mpr ⟨e, he, hea, hea⟩

def CoversAssignment (r : ℕ) (a g : Code) (xs : List ℕ) : Prop :=
  ∀ i < a.1, ∀ j < a.1, i ≠ j → CoveredPair r g (xs.getD i 0) (xs.getD j 0)

instance (r : ℕ) (a g : Code) (xs : List ℕ) : Decidable (CoversAssignment r a g xs) := by
  unfold CoversAssignment
  infer_instance

theorem coversAssignment_iff (r : ℕ) (a g : Code) (xs : List ℕ)
    (hx : xs ∈ assignments a g) :
    CoversAssignment r a g xs ↔
      Uniformity.CoversImagePairs (decode r g) (assignmentMap a g xs hx) := by
  constructor
  · intro h i j hij
    exact (coveredPair_iff r g _ _).mp
      (h i.val i.isLt j.val j.isLt (fun h => hij (Fin.ext h)))
  · intro h i hi j hj hij
    exact (coveredPair_iff r g _ _).mpr (h ⟨i, hi⟩ ⟨j, hj⟩
      (fun h => hij (congrArg Fin.val h)))

def IsExtension (r : ℕ) (a g : Code) : Prop :=
  NoIsolates r g ∧ ∃ xs ∈ assignments a g,
    InjectiveAssignment a.1 xs ∧ HomAssignment r a g xs ∧ CoversAssignment r a g xs

instance (r : ℕ) (a g : Code) : Decidable (IsExtension r a g) := by
  unfold IsExtension
  infer_instance

theorem isExtension_iff (r : ℕ) (a g : Code) :
    IsExtension r a g ↔ Uniformity.IsExtension (decode r a) (decode r g) := by
  constructor
  · rintro ⟨hn, xs, hx, hi, hh, hc⟩
    exact ⟨(noIsolates_iff r g).mp hn, assignmentMap a g xs hx,
      ⟨(injectiveAssignment_iff a g xs hx).mp hi, (homAssignment_iff r a g xs hx).mp hh⟩,
      (coversAssignment_iff r a g xs hx).mp hc⟩
  · rintro ⟨hn, f, hf, hc⟩
    obtain ⟨xs, hx, hxs⟩ := map_assignment a g f
    exact ⟨(noIsolates_iff r g).mpr hn, xs, hx,
      (injectiveAssignment_iff a g xs hx).mpr (hxs ▸ hf.1),
      (homAssignment_iff r a g xs hx).mpr (hxs ▸ hf.2),
      (coversAssignment_iff r a g xs hx).mpr (hxs ▸ hc)⟩

def extensionCodes (r : ℕ) (a : Code) : List Code :=
  (boundedCodes r (Uniformity.extensionBound r a.1)).filter fun g => IsExtension r a g

theorem extensionCodes_decode (r : ℕ) (a : Code) :
    ((extensionCodes r a).map (decodeFinite r)).toFinset =
      Uniformity.extensions (decodeFinite r a) := by
  ext G
  simp only [List.mem_toFinset, List.mem_map, Uniformity.mem_extensions]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hbound, hcheck⟩ := List.mem_filter.mp hg
    exact ⟨mem_boundedCodes_size hbound,
      (isExtension_iff r a g).mp (of_decide_eq_true hcheck)⟩
  · rintro ⟨hbound, hext⟩
    refine ⟨encodeFinite G, List.mem_filter.mpr
      ⟨encode_mem_boundedCodes G hbound, ?_⟩, decode_encodeFinite G⟩
    apply decide_eq_true
    apply (isExtension_iff r a (encodeFinite G)).mpr
    simpa [decodeFinite, encodeFinite, decode_encode] using hext

end TuranUniversality.Effective.Uniform
