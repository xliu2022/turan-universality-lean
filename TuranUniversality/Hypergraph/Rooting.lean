module

public import TuranUniversality.Hypergraph.BoundedSearch
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-! # Partial injective root assignments and bounded root elimination -/

open scoped BigOperators

namespace TuranUniversality

universe u v

/-- A root label may be unassigned; assigned labels have distinct images. -/
abbrev Rooting (M : Type u) (V : Type v) :=
  {f : M → Option V // ∀ a b v, f a = some v → f b = some v → a = b}

namespace Rooting

variable {M : Type u} {V : Type v} [Fintype M] [DecidableEq M] [DecidableEq V]

def empty : Rooting M V := ⟨fun _ => none, by intros; contradiction⟩

def Extends (mu nu : Rooting M V) : Prop :=
  ∀ a v, mu.val a = some v → nu.val a = some v

omit [Fintype M] [DecidableEq M] [DecidableEq V] in
theorem empty_extends (nu : Rooting M V) : Extends empty nu := by
  intro a v h
  cases h

def domain (mu : Rooting M V) : Finset M :=
  Finset.univ.filter (fun a => mu.val a ≠ none)

def range (mu : Rooting M V) : Finset V :=
  Finset.univ.biUnion (fun a => (mu.val a).toFinset)

omit [DecidableEq M] in
@[simp] theorem mem_range (mu : Rooting M V) (v : V) :
    v ∈ mu.range ↔ ∃ a, mu.val a = some v := by
  simp [range]

def rank (mu : Rooting M V) : ℕ := mu.domain.card

omit [DecidableEq M] [DecidableEq V] in
theorem rank_le (mu : Rooting M V) : mu.rank ≤ Fintype.card M :=
  Finset.card_le_univ _

def add (mu : Rooting M V) (a : M) (v : V)
    (_ha : mu.val a = none) (hv : v ∉ mu.range) : Rooting M V := by
  refine ⟨Function.update mu.val a (some v), ?_⟩
  intro b c w hb hc
  by_cases hba : b = a
  · subst b
    by_cases hca : c = a
    · exact hca.symm
    · simp only [Function.update_self, Option.some.injEq] at hb
      subst w
      rw [Function.update_of_ne hca] at hc
      exact False.elim (hv ((mem_range mu v).mpr ⟨c, hc⟩))
  · by_cases hca : c = a
    · subst c
      simp only [Function.update_self, Option.some.injEq] at hc
      subst w
      rw [Function.update_of_ne hba] at hb
      exact False.elim (hv ((mem_range mu v).mpr ⟨b, hb⟩))
    · rw [Function.update_of_ne hba] at hb
      rw [Function.update_of_ne hca] at hc
      exact mu.property b c w hb hc

@[simp] theorem add_value (mu : Rooting M V) (a : M) (v : V)
    (ha : mu.val a = none) (hv : v ∉ mu.range) :
    (mu.add a v ha hv).val = Function.update mu.val a (some v) := rfl

theorem domain_add (mu : Rooting M V) (a : M) (v : V)
    (ha : mu.val a = none) (hv : v ∉ mu.range) :
    (mu.add a v ha hv).domain = insert a mu.domain := by
  ext b
  constructor
  · intro hb
    by_cases hba : b = a
    · exact Finset.mem_insert.mpr (Or.inl hba)
    · have hb' : (mu.add a v ha hv).val b ≠ none := (Finset.mem_filter.mp hb).2
      rw [add_value, Function.update_of_ne hba] at hb'
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hb'⟩))
  · intro hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hb with hba | hb
    · subst b
      rw [add_value, Function.update_self]
      exact Option.some_ne_none v
    · have hb' : mu.val b ≠ none := (Finset.mem_filter.mp hb).2
      have hba : b ≠ a := by intro h; subst b; exact hb' ha
      rwa [add_value, Function.update_of_ne hba]

theorem rank_add (mu : Rooting M V) (a : M) (v : V)
    (ha : mu.val a = none) (hv : v ∉ mu.range) :
    (mu.add a v ha hv).rank = mu.rank + 1 := by
  rw [rank, mu.domain_add]
  apply Finset.card_insert_of_notMem
  simp [domain, ha]

theorem add_extends (mu nu : Rooting M V) (a : M) (v : V)
    (ha : mu.val a = none) (hv : v ∉ mu.range)
    (hmu : Extends mu nu) (hnu : nu.val a = some v) :
    Extends (mu.add a v ha hv) nu := by
  intro b w hb
  by_cases hba : b = a
  · subst b
    simp only [add_value, Function.update_self, Option.some.injEq] at hb
    simpa [hb] using hnu
  · rw [add_value, Function.update_of_ne hba] at hb
    exact hmu b w hb

def availablePairs (mu : Rooting M V) (S : Finset V) : Finset (M × V) :=
  (Finset.univ ×ˢ S).filter (fun p => mu.val p.1 = none ∧ p.2 ∉ mu.range)

def children (mu : Rooting M V) (S : Finset V) : Finset (Rooting M V) :=
  (mu.availablePairs S).attach.image (fun p => mu.add p.val.1 p.val.2
    (Finset.mem_filter.mp p.property).2.1 (Finset.mem_filter.mp p.property).2.2)

theorem children_rank (mu : Rooting M V) (S : Finset V)
    {nu : Rooting M V} (hnu : nu ∈ mu.children S) : nu.rank = mu.rank + 1 := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hnu
  exact mu.rank_add _ _ _ _

theorem children_card_le (mu : Rooting M V) (S : Finset V) :
    (mu.children S).card ≤ Fintype.card M * S.card := by
  calc
    (mu.children S).card ≤ (mu.availablePairs S).attach.card := Finset.card_image_le
    _ = (mu.availablePairs S).card := Finset.card_attach
    _ ≤ (Finset.univ ×ˢ S).card := Finset.card_filter_le _ _
    _ = _ := by simp

theorem child_of_repair (mu nu : Rooting M V) (S : Finset V)
    (hmu : Extends mu nu) (a : M) (v : V)
    (ha : mu.val a = none) (hv : v ∉ mu.range)
    (hS : v ∈ S) (hnu : nu.val a = some v) :
    ∃ rho ∈ mu.children S, Extends rho nu := by
  let p : mu.availablePairs S := ⟨(a, v),
    Finset.mem_filter.mpr ⟨by simp [hS], ha, hv⟩⟩
  refine ⟨mu.add a v ha hv, ?_, mu.add_extends nu a v ha hv hmu hnu⟩
  exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩

/-- Bounded root elimination on a fixed finite host. Admissibility on a retained
vertex set may use a partial rooting. Every failed rooting supplies a bounded
witness whose repair must assign a new root inside that witness. -/
theorem bounded_obstruction [Fintype V]
    (Admissible : Finset V → Rooting M V → Prop) (w : ℕ)
    (hfailed : ∀ mu, ¬ Admissible Finset.univ mu)
    (hwitness : ∀ mu, ¬ Admissible Finset.univ mu → ∃ S : Finset V,
      S.card ≤ w ∧ ∀ T nu, S ⊆ T → Extends mu nu → Admissible T nu →
        ∃ a v, mu.val a = none ∧ nu.val a = some v ∧ v ∈ S ∧ v ∉ mu.range) :
    ∃ T : Finset V,
      T.card ≤ w * ∑ j ∈ Finset.range (Fintype.card M + 1), (Fintype.card M * w) ^ j ∧
      ∀ nu, ¬ Admissible T nu := by
  classical
  choose witness hw hpersist using fun mu => hwitness mu (hfailed mu)
  apply BoundedSearch.bounded_obstruction
    (fun mu => mu.children (witness mu)) (empty : Rooting M V) rank witness
    (Fintype.card M) (Fintype.card M * w) w rank_le
    (fun mu nu h => mu.children_rank (witness mu) h)
    (fun mu => (mu.children_card_le (witness mu)).trans (Nat.mul_le_mul_left _ (hw mu)))
    hw Admissible Extends empty_extends
  intro T nu hadm mu hext hsub
  obtain ⟨a, v, ha, hnu, hv, hnew⟩ := hpersist mu T nu hsub hext hadm
  exact mu.child_of_repair nu (witness mu) hext a v ha hnew hv hnu

end Rooting
end TuranUniversality
