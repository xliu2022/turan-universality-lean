module

public import TuranUniversality.Effective.UniformFiniteSets
public import TuranUniversality.Effective.HomomorphicClosurePrimrec
public import TuranUniversality.Structural.Record

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Bounded numeric encodings of actual legal inner objects

The free predicate checks injective maps whose entire vertex image lies in
the active set. In particular, isolated vertices of a forbidden graph are
retained. Every search ranges over explicit lists of finite objects.
-/

namespace TuranUniversality.Effective.StructuralCodes

open Uniform Structural

abbrev ObjectCode := List ℕ × List (List ℕ) × List (List ℕ)

def objectCodes (n : ℕ) : List ObjectCode :=
  (subsetRows n).flatMap fun a =>
    (allRows 3 n).sublists'.flatMap fun e₀ =>
      (allRows 3 n).sublists'.map fun e₁ => (a, e₀, e₁)

theorem mem_objectCodes (n : ℕ) (z : ObjectCode) :
    z ∈ objectCodes n ↔ z.1 ∈ subsetRows n ∧
      z.2.1.Sublist (allRows 3 n) ∧ z.2.2.Sublist (allRows 3 n) := by
  rcases z with ⟨a, e₀, e₁⟩
  simp only [objectCodes, List.mem_flatMap, List.mem_map, List.mem_sublists',
    Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', e₀', he₀', e₁', he₁', rfl, rfl, rfl⟩
    exact ⟨ha', he₀', he₁'⟩
  · rintro ⟨ha, he₀, he₁⟩
    exact ⟨a, ha, e₀, he₀, e₁, he₁, rfl, rfl, rfl⟩

def Supported (n : ℕ) (es : List (List ℕ)) (a : List ℕ) : Prop :=
  ∀ w ∈ allRows 3 n, Edge 3 (n, es) w → ∀ v ∈ w, v ∈ a

instance (n : ℕ) (es : List (List ℕ)) (a : List ℕ) : Decidable (Supported n es a) := by
  unfold Supported
  infer_instance

theorem supported_iff (n : ℕ) (es : List (List ℕ)) (a : List ℕ) :
    Supported n es a ↔ ∀ e ∈ (decode 3 (n, es)).edges, e ⊆ rowSet n a := by
  constructor
  · intro h e he
    have hw := edge_canonical 3 (n, es) e he
    have hh := h _ ((mem_allRows _ _ _).mpr ⟨hw.1.1, hw.1.2.2⟩) hw
    intro v hv
    exact (mem_rowSet n a v).mpr (hh v.val (List.mem_map.mpr
      ⟨v, Finset.mem_toList.mpr hv, rfl⟩))
  · intro h w _ hw
    exact (rowSet_subset_iff_mem w a hw.1.2.2).mp (h _ (edge_rowSet _ _ _ hw))

def ImageActive (n : ℕ) (a xs : List ℕ) : Prop :=
  ∀ v < n, xs.getD v 0 ∈ a

instance (n : ℕ) (a xs : List ℕ) : Decidable (ImageActive n a xs) := by
  unfold ImageActive
  infer_instance

theorem imageActive_iff (g h : Code) (a xs : List ℕ) (hx : xs ∈ assignments g h) :
    ImageActive g.1 a xs ↔ ∀ v, assignmentMap g h xs hx v ∈ rowSet h.1 a := by
  constructor
  · intro hh v
    exact (mem_rowSet h.1 a _).mpr (hh v.val v.isLt)
  · intro hh v hv
    exact (mem_rowSet h.1 a _).mp (hh ⟨v, hv⟩)

def ActiveFree (fs : List Code) (n : ℕ) (es : List (List ℕ)) (a : List ℕ) : Prop :=
  ∀ f ∈ fs, ∀ xs ∈ assignments f (n, es), ImageActive f.1 a xs →
    ¬ (InjectiveAssignment f.1 xs ∧ HomAssignment 3 f (n, es) xs)

instance (fs : List Code) (n : ℕ) (es : List (List ℕ)) (a : List ℕ) :
    Decidable (ActiveFree fs n es a) := by
  unfold ActiveFree
  infer_instance

theorem activeFree_iff (fs : List Code) (n : ℕ) (es : List (List ℕ)) (a : List ℕ) :
    ActiveFree fs n es a ↔ ∀ F ∈ decodeFamily 3 fs, ∀ f : Fin F.1 → Fin n,
      (∀ v, f v ∈ rowSet n a) → ¬ F.2.IsEmbedding (decode 3 (n, es)) f := by
  constructor
  · intro h F hF f hactive hf
    obtain ⟨g, hg, rfl⟩ := (mem_decodeFamily 3 fs F).mp hF
    obtain ⟨xs, hx, hxs⟩ := map_assignment g (n, es) f
    exact h g hg xs hx ((imageActive_iff g (n, es) a xs hx).mpr (hxs ▸ hactive))
      ⟨(injectiveAssignment_iff g (n, es) xs hx).mpr (hxs ▸ hf.1),
        (homAssignment_iff 3 g (n, es) xs hx).mpr (hxs ▸ hf.2)⟩
  · intro h g hg xs hx hactive hf
    exact h (decodeFinite 3 g) ((mem_decodeFamily 3 fs _).mpr ⟨g, hg, rfl⟩)
      (assignmentMap g (n, es) xs hx) ((imageActive_iff g (n, es) a xs hx).mp hactive)
      ⟨(injectiveAssignment_iff g (n, es) xs hx).mp hf.1,
        (homAssignment_iff 3 g (n, es) xs hx).mp hf.2⟩

def Legal (fs : List Code) (n : ℕ) (z : ObjectCode) : Prop :=
  Supported n z.2.1 z.1 ∧ Supported n z.2.2 z.1 ∧
    (Edgeless 3 (n, z.2.1) ∨ Edgeless 3 (n, z.2.2)) ∧
    ActiveFree fs n z.2.1 z.1 ∧ ActiveFree fs n z.2.2 z.1

instance (fs : List Code) (n : ℕ) (z : ObjectCode) : Decidable (Legal fs n z) := by
  unfold Legal
  infer_instance

def object (fs : List Code) (n : ℕ) (z : ObjectCode) (h : Legal fs n z) :
    LegalObject (decodeFamily 3 fs) (Fin n) where
  active := rowSet n z.1
  inner a := if a then decode 3 (n, z.2.2) else decode 3 (n, z.2.1)
  supported := by
    intro a
    cases a
    · exact (supported_iff n z.2.1 z.1).mp h.1
    · exact (supported_iff n z.2.2 z.1).mp h.2.1
  onePhase := by
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      h.2.2.1.imp ((edgeless_iff 3 (n, z.2.1)).mp) ((edgeless_iff 3 (n, z.2.2)).mp)
  free := by
    intro a
    cases a
    · exact (activeFree_iff fs n z.2.1 z.1).mp h.2.2.2.1
    · exact (activeFree_iff fs n z.2.2 z.1).mp h.2.2.2.2

def encodeObject {B : Finset (FiniteGraph 3)} {n : ℕ} (O : LegalObject B (Fin n)) :
    ObjectCode := (subsetRow O.active, (Uniform.encode (O.inner false)).2,
      (Uniform.encode (O.inner true)).2)

theorem encodeObject_mem {B : Finset (FiniteGraph 3)} {n : ℕ}
    (O : LegalObject B (Fin n)) : encodeObject O ∈ objectCodes n := by
  rw [mem_objectCodes]
  exact ⟨subsetRow_mem _, List.filter_sublist, List.filter_sublist⟩

theorem encodeObject_legal (fs : List Code) {n : ℕ}
    (O : LegalObject (decodeFamily 3 fs) (Fin n)) : Legal fs n (encodeObject O) := by
  have hd (a : Bool) : decode 3 (n, (Uniform.encode (O.inner a)).2) = O.inner a :=
    decode_encode (O.inner a)
  have hs (a : Bool) : Supported n (Uniform.encode (O.inner a)).2 (subsetRow O.active) := by
    rw [supported_iff, hd, rowSet_subsetRow]
    exact O.supported a
  have hf (a : Bool) : ActiveFree fs n (Uniform.encode (O.inner a)).2 (subsetRow O.active) := by
    rw [activeFree_iff, hd, rowSet_subsetRow]
    exact O.free a
  refine ⟨hs false, hs true, ?_, hf false, hf true⟩
  change Edgeless 3 (n, (Uniform.encode (O.inner false)).2) ∨
    Edgeless 3 (n, (Uniform.encode (O.inner true)).2)
  rw [edgeless_iff, edgeless_iff, hd, hd]
  exact O.onePhase

theorem object_ext {B : Finset (FiniteGraph 3)} {n : ℕ} (O P : LegalObject B (Fin n))
    (ha : O.active = P.active) (hi : O.inner = P.inner) : O = P := by
  cases O
  cases P
  cases ha
  cases hi
  rfl

theorem object_encodeObject (fs : List Code) {n : ℕ}
    (O : LegalObject (decodeFamily 3 fs) (Fin n)) :
    object fs n (encodeObject O) (encodeObject_legal fs O) = O := by
  apply object_ext
  · exact rowSet_subsetRow O.active
  · funext a
    cases a <;> exact decode_encode _

end TuranUniversality.Effective.StructuralCodes
