module

public import TuranUniversality.Effective.UniformAdmissible
public import TuranUniversality.Effective.UniformPrimrec

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Bounded list encodings of actual finite vertex subsets -/

namespace TuranUniversality.Effective.Uniform

def subsetRows (n : ℕ) : List (List ℕ) := (List.range n).sublists'

theorem subsetRows_primrec : Primrec subsetRows :=
  sublists_primrec.comp Primrec.list_range

theorem mem_subsetRows (n : ℕ) (s : List ℕ) :
    s ∈ subsetRows n ↔ s.Sublist (List.range n) := List.mem_sublists'

theorem subsetRows_good {n : ℕ} {s : List ℕ} (hs : s ∈ subsetRows n) : Good s.length n s := by
  have hsub := (mem_subsetRows n s).mp hs
  refine ⟨rfl, (distinct_iff s).mpr (List.nodup_range.sublist hsub), ?_⟩
  intro a ha
  exact List.mem_range.mp (hsub.subset ha)

def subsetRow {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  (List.range n).filter (fun a => a ∈ S.image Fin.val)

theorem subsetRow_mem {n : ℕ} (S : Finset (Fin n)) : subsetRow S ∈ subsetRows n :=
  (mem_subsetRows _ _).mpr List.filter_sublist

theorem rowSet_subsetRow {n : ℕ} (S : Finset (Fin n)) : rowSet n (subsetRow S) = S := by
  ext v
  simp only [mem_rowSet, subsetRow, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hv⟩
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    exact Fin.val_injective huv ▸ hu
  · intro hv
    exact ⟨v.isLt, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

theorem subsetRow_length {n : ℕ} (S : Finset (Fin n)) : (subsetRow S).length = S.card := by
  rw [← rowSet_card (subsetRows_good (subsetRow_mem S)), rowSet_subsetRow]

theorem rowSet_subset_iff_mem {n : ℕ} (s t : List ℕ) (hs : ∀ a ∈ s, a < n) :
    rowSet n s ⊆ rowSet n t ↔ ∀ a ∈ s, a ∈ t := by
  constructor
  · intro h a ha
    exact (mem_rowSet n t ⟨a, hs a ha⟩).mp (h ((mem_rowSet n s _).mpr ha))
  · intro h v hv
    exact (mem_rowSet n t v).mpr (h v.val ((mem_rowSet n s v).mp hv))

theorem edge_iff_rowSet_of_distinct {r n : ℕ} (es : List (List ℕ)) (s : List ℕ)
    (hd : Distinct s) (hb : ∀ a ∈ s, a < n) :
    Edge r (n, es) s ↔ rowSet n s ∈ (decode r (n, es)).edges := by
  constructor
  · exact edge_rowSet r (n, es) s
  · intro he
    have hc := (decode r (n, es)).uniform _ he
    rw [rowSet_card (show Good s.length n s from ⟨rfl, hd, hb⟩)] at hc
    exact (edge_iff_of_image r (n, es) _ s hc (rowSet_image n s hb)).mpr he

def intersectionRow (s t : List ℕ) : List ℕ := s.filter (fun a => a ∈ t)

theorem intersectionRow_primrec : Primrec₂ intersectionRow :=
  (filter_primrec list_mem_primrec.swap).comp Primrec.snd Primrec.fst

theorem rowSet_intersectionRow (n : ℕ) (s t : List ℕ) :
    rowSet n (intersectionRow s t) = rowSet n s ∩ rowSet n t := by
  ext v
  simp [mem_rowSet, intersectionRow]

theorem intersectionRow_good {n : ℕ} {s : List ℕ} (hs : Good s.length n s) (t : List ℕ) :
    Good (intersectionRow s t).length n (intersectionRow s t) := by
  refine ⟨rfl, (distinct_iff _).mpr (((distinct_iff _).mp hs.2.1).filter _), ?_⟩
  intro a ha
  exact hs.2.2 a (List.mem_of_mem_filter ha)

end TuranUniversality.Effective.Uniform
