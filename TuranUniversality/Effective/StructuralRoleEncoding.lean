module

public import TuranUniversality.Effective.StructuralObjectsPrimrec
public import TuranUniversality.Structural.RootedRoles

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Numeric roles and the fixed finite support tables

Zero denotes a data vertex. Positive codes enumerate the suspension roots
and the five-point block roots. The finite support tables are fixed once
the block count and the seven actual pools have been fixed.
-/

namespace TuranUniversality.Effective.StructuralCodes

open TuranUniversality.Effective.Uniform Structural

noncomputable def supportEquiv (b : ℕ) : Support.Vertex b ≃ Fin (5 * b) :=
  Fintype.equivOfCardEq (by simp [Support.Vertex, Nat.mul_comm])

noncomputable def rootEquiv (b t : ℕ) : Rooted.Roots b t ≃ Fin (t + 5 * b) :=
  (Equiv.sumCongr (Equiv.refl _) (supportEquiv b)).trans finSumFinEquiv

noncomputable def roleEquiv (b t : ℕ) : Option (Rooted.Roots b t) ≃ Fin (t + 5 * b + 1) :=
  (Equiv.optionCongr (rootEquiv b t)).trans (finSuccEquiv _).symm

@[simp] theorem rootEquiv_left (b t : ℕ) (i : Fin t) :
    (rootEquiv b t (.inl i)).val = i.val := rfl

@[simp] theorem rootEquiv_right (b t : ℕ) (v : Support.Vertex b) :
    (rootEquiv b t (.inr v)).val = t + (supportEquiv b v).val := rfl

@[simp] theorem roleEquiv_none (b t : ℕ) : (roleEquiv b t none).val = 0 := rfl

@[simp] theorem roleEquiv_some (b t : ℕ) (m : Rooted.Roots b t) :
    (roleEquiv b t (some m)).val = (rootEquiv b t m).val + 1 := by
  simp [roleEquiv]

def roleAssignments (b t n : ℕ) : List (List ℕ) :=
  assignments (n, []) (t + 5 * b + 1, [])

noncomputable def roleMap (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n) :
    Fin n → Option (Rooted.Roots b t) :=
  fun v => (roleEquiv b t).symm (assignmentMap (n, []) (t + 5 * b + 1, []) xs hx v)

@[simp] theorem roleMap_index (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (v : Fin n) : (roleEquiv b t (roleMap b t n xs hx v)).val = xs.getD v.val 0 := by
  simp [roleMap, assignmentMap]

theorem roleMap_none_iff (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (v : Fin n) : roleMap b t n xs hx v = none ↔ xs.getD v.val 0 = 0 := by
  constructor
  · intro h
    rw [← roleMap_index b t n xs hx v, h, roleEquiv_none]
  · intro h
    apply (roleEquiv b t).injective
    apply Fin.ext
    rw [roleMap_index, roleEquiv_none, h]

theorem roleMap_some_iff (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (v : Fin n) (m : Rooted.Roots b t) :
    roleMap b t n xs hx v = some m ↔ xs.getD v.val 0 = (rootEquiv b t m).val + 1 := by
  constructor
  · intro h
    rw [← roleMap_index b t n xs hx v, h, roleEquiv_some]
  · intro h
    apply (roleEquiv b t).injective
    apply Fin.ext
    rw [roleMap_index, roleEquiv_some, h]

theorem encode_roleMap (b t n : ℕ) (ρ : Fin n → Option (Rooted.Roots b t)) :
    ∃ xs, ∃ hx : xs ∈ roleAssignments b t n, roleMap b t n xs hx = ρ := by
  obtain ⟨xs, hx, hxs⟩ := map_assignment (n, []) (t + 5 * b + 1, [])
    (fun v => roleEquiv b t (ρ v))
  refine ⟨xs, hx, ?_⟩
  funext v
  change (roleEquiv b t).symm (assignmentMap _ _ xs hx v) = ρ v
  rw [hxs]
  exact (roleEquiv b t).symm_apply_apply _

def dataRow (xs w : List ℕ) : List ℕ := w.filter (fun v => xs.getD v 0 = 0)

theorem dataRow_good {n : ℕ} {w : List ℕ} (hw : Good w.length n w) (xs : List ℕ) :
    Good (dataRow xs w).length n (dataRow xs w) := by
  refine ⟨rfl, (distinct_iff _).mpr (((distinct_iff _).mp hw.2.1).filter _), ?_⟩
  intro a ha
  exact hw.2.2 a (List.mem_of_mem_filter ha)

theorem rowSet_dataRow (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (w : List ℕ) : rowSet n (dataRow xs w) = Roles.dataSet (roleMap b t n xs hx) (rowSet n w) := by
  ext v
  simp [mem_rowSet, dataRow, Roles.mem_dataSet, roleMap_none_iff]

theorem root_mem_imageRow (b t n : ℕ) (xs : List ℕ) (hx : xs ∈ roleAssignments b t n)
    (w : List ℕ) (hw : ∀ a ∈ w, a < n) (m : Rooted.Roots b t) :
    (rootEquiv b t m).val + 1 ∈ imageRow xs w ↔
      ∃ v ∈ rowSet n w, roleMap b t n xs hx v = some m := by
  constructor
  · intro h
    obtain ⟨a, ha, ham⟩ := List.mem_map.mp h
    exact ⟨⟨a, hw a ha⟩, (mem_rowSet n w _).mpr ha,
      (roleMap_some_iff b t n xs hx _ m).mpr ham⟩
  · rintro ⟨v, hv, hm⟩
    exact List.mem_map.mpr ⟨v.val, (mem_rowSet n w v).mp hv,
      (roleMap_some_iff b t n xs hx v m).mp hm⟩

noncomputable def supportGraph {b : ℕ} (Ω : Label → Finset (Cube.Word b)) (l : Label) :
    RGraph (Fin (5 * b)) (3 * b) :=
  (Support.poolGraph (Ω l)).pullback (supportEquiv b).symm.toEmbedding

noncomputable def supportTable {b : ℕ} (Ω : Label → Finset (Cube.Word b)) :
    List (List (List ℕ)) := List.ofFn fun l : Fin 7 => (Uniform.encode (supportGraph Ω (CodePools.labelEquiv l))).2

noncomputable def supportCode {b : ℕ} (Ω : Label → Finset (Cube.Word b)) (l : ℕ) : Code :=
  (5 * b, (supportTable Ω).getD l [])

theorem supportCode_eq {b : ℕ} (Ω : Label → Finset (Cube.Word b)) (l : Fin 7) :
    supportCode Ω l.val = Uniform.encode (supportGraph Ω (CodePools.labelEquiv l)) := by
  fin_cases l <;> rfl

theorem decode_supportCode {b : ℕ} (Ω : Label → Finset (Cube.Word b)) (l : Fin 7) :
    decode (3 * b) (supportCode Ω l.val) = supportGraph Ω (CodePools.labelEquiv l) := by
  have h := congrArg Prod.snd (supportCode_eq Ω l)
  change decode (3 * b) (5 * b, (supportCode Ω l.val).2) = _
  rw [h]
  exact decode_encode _

theorem supportGraph_image_mem {b : ℕ} (Ω : Label → Finset (Cube.Word b)) (l : Label)
    (z : Finset (Fin (5 * b))) :
    z ∈ (supportGraph Ω l).edges ↔
      z.image (supportEquiv b).symm ∈ (Support.poolGraph (Ω l)).edges := by
  rw [supportGraph, RGraph.mem_pullback]
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    have hc := (Support.poolGraph (Ω l)).uniform _ h
    simpa only [Finset.card_image_of_injective _ (supportEquiv b).symm.injective] using hc

end TuranUniversality.Effective.StructuralCodes
