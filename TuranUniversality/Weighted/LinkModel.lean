module

public import TuranUniversality.Weighted.Model

/-! # Building actual rooted 3-graphs from their four link families -/

@[expose] public section

namespace TuranUniversality.Weighted

universe u v
variable {Roots : Type u} {Data : Type v}
  [DecidableEq Roots] [Fintype Roots] [DecidableEq Data] [Fintype Data]

structure LinkData (Roots : Type u) (Data : Type v)
    [DecidableEq Roots] [DecidableEq Data] where
  rootTriples : Finset (Finset Roots)
  rootLink : Data → Finset (Finset Roots)
  dataLink : Roots → Finset (Finset Data)
  dataTriples : Finset (Finset Data)
  rootTriples_uniform : ∀ p ∈ rootTriples, p.card = 3
  rootLink_uniform : ∀ d p, p ∈ rootLink d → p.card = 2
  dataLink_uniform : ∀ r p, p ∈ dataLink r → p.card = 2
  dataTriples_uniform : ∀ p ∈ dataTriples, p.card = 3

namespace LinkData

def model (A : LinkData Roots Data) : RootedModel Roots Data where
  edges := Finset.univ.filter fun p =>
    (p.2 = ∅ ∧ p.1 ∈ A.rootTriples) ∨
    (∃ d, p.2 = {d} ∧ p.1 ∈ A.rootLink d) ∨
    (∃ r, p.1 = {r} ∧ p.2 ∈ A.dataLink r) ∨
    (p.1 = ∅ ∧ p.2 ∈ A.dataTriples)
  uniform := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with h | h | h | h
    · rw [h.1, Finset.card_empty, A.rootTriples_uniform p.1 h.2, add_zero]
    · obtain ⟨d, hd, hp⟩ := h
      rw [hd, Finset.card_singleton, A.rootLink_uniform d p.1 hp]
    · obtain ⟨r, hr, hp⟩ := h
      rw [hr, Finset.card_singleton, A.dataLink_uniform r p.2 hp]
    · rw [h.1, Finset.card_empty, A.dataTriples_uniform p.2 h.2, zero_add]

@[simp] theorem mem_model_edges (A : LinkData Roots Data) (p : Finset Roots) (q : Finset Data) :
    (p, q) ∈ A.model.edges ↔
      (q = ∅ ∧ p ∈ A.rootTriples) ∨
      (∃ d, q = {d} ∧ p ∈ A.rootLink d) ∨
      (∃ r, p = {r} ∧ q ∈ A.dataLink r) ∨
      (p = ∅ ∧ q ∈ A.dataTriples) := by
  simp [model]

@[simp] theorem model_rootLink (A : LinkData Roots Data) (d : Data) :
    A.model.rootLink d = A.rootLink d := by
  ext p
  rw [A.model.mem_rootLink, A.mem_model_edges]
  constructor
  · rintro (⟨h, hp⟩ | ⟨d', hd', hp⟩ | ⟨r, hr, hp⟩ | ⟨he, hp⟩)
    · exact False.elim (Finset.singleton_ne_empty _ h)
    · have hd : d = d' := Finset.singleton_inj.mp hd'
      simpa only [hd] using hp
    · have hc := A.dataLink_uniform r {d} hp
      simp at hc
    · have hc := A.dataTriples_uniform {d} hp
      simp at hc
  · exact fun hp => Or.inr (Or.inl ⟨d, rfl, hp⟩)

@[simp] theorem model_dataLink (A : LinkData Roots Data) (r : Roots) :
    A.model.dataLink r = A.dataLink r := by
  ext p
  rw [A.model.mem_dataLink, A.mem_model_edges]
  constructor
  · rintro (⟨h, hp⟩ | ⟨d, hd, hp⟩ | ⟨r', hr', hp⟩ | ⟨he, hp⟩)
    · have hc := A.rootTriples_uniform {r} hp
      simp at hc
    · have hc := A.rootLink_uniform d {r} hp
      simp at hc
    · have hr : r = r' := Finset.singleton_inj.mp hr'
      simpa only [hr] using hp
    · exact False.elim (Finset.singleton_ne_empty _ he)
  · exact fun hp => Or.inr (Or.inr (Or.inl ⟨r, rfl, hp⟩))

@[simp] theorem model_rootTriples (A : LinkData Roots Data) : A.model.rootTriples = A.rootTriples := by
  ext p
  rw [A.model.mem_rootTriples, A.mem_model_edges]
  constructor
  · rintro (⟨h, hp⟩ | ⟨d, hd, hp⟩ | ⟨r, hr, hp⟩ | ⟨he, hp⟩)
    · exact hp
    · exact False.elim (Finset.empty_ne_singleton _ hd)
    · have hc := A.dataLink_uniform r ∅ hp
      simp at hc
    · have hc := A.dataTriples_uniform ∅ hp
      simp at hc
  · exact fun hp => Or.inl ⟨rfl, hp⟩

@[simp] theorem model_dataTriples (A : LinkData Roots Data) : A.model.dataTriples = A.dataTriples := by
  ext p
  rw [A.model.mem_dataTriples, A.mem_model_edges]
  constructor
  · rintro (⟨h, hp⟩ | ⟨d, hd, hp⟩ | ⟨r, hr, hp⟩ | ⟨he, hp⟩)
    · have hc := A.rootTriples_uniform ∅ hp
      simp at hc
    · have hc := A.rootLink_uniform d ∅ hp
      simp at hc
    · exact False.elim (Finset.empty_ne_singleton _ hr)
    · exact hp
  · exact fun hp => Or.inr (Or.inr (Or.inr ⟨rfl, hp⟩))

end LinkData

end TuranUniversality.Weighted
