module

public import TuranUniversality.Effective.GraphBuild
public import TuranUniversality.Effective.WordEnumeration
public import TuranUniversality.Effective.RuleEncoding
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # Exact finite-code embedding search -/

namespace TuranUniversality.Effective

def EmbeddingAssignment (p : GraphCode × GraphCode) (xs : List ℕ) : Prop :=
  (∀ x < p.1.1, ∀ y < p.1.1, xs.getD x 0 = xs.getD y 0 → x = y) ∧
  (∀ x < p.1.1, ∀ y < p.1.1, ∀ z < p.1.1,
    CodeEdge p.1 (x, y, z) →
      CodeEdge p.2 (xs.getD x 0, xs.getD y 0, xs.getD z 0))

instance (p : GraphCode × GraphCode) (xs : List ℕ) : Decidable (EmbeddingAssignment p xs) := by
  unfold EmbeddingAssignment
  infer_instance

def CodeContains (g h : GraphCode) : Prop :=
  ∃ xs ∈ allWords (List.range h.1) g.1, EmbeddingAssignment (g, h) xs

instance (g h : GraphCode) : Decidable (CodeContains g h) := by
  unfold CodeContains
  infer_instance

theorem codeContains_iff (g h : GraphCode) :
    CodeContains g h ↔ ∃ f, (decodeGraph g).IsEmbedding (decodeGraph h) f := by
  constructor
  · rintro ⟨xs, hxs, hinj, hedges⟩
    obtain ⟨hlen, hbound⟩ := (mem_allWords (List.range h.1) g.1 xs).mp hxs
    have hget (i : Fin g.1) : xs.getD i.val 0 < h.1 := by
      have hi : i.val < xs.length := by simpa only [hlen] using i.isLt
      rw [List.getD_eq_getElem _ _ hi]
      exact List.mem_range.mp (hbound _ (List.getElem_mem hi))
    let f : Fin g.1 → Fin h.1 := fun i => ⟨xs.getD i.val 0, hget i⟩
    refine ⟨f, ?_, ?_⟩
    · intro a b hab
      exact Fin.ext (hinj a.val a.isLt b.val b.isLt (congrArg Fin.val hab))
    · apply RGraph.isHom_of_triples
      intro a b c he
      apply (codeEdge_iff h (f a) (f b) (f c)).mp
      exact hedges a.val a.isLt b.val b.isLt c.val c.isLt ((codeEdge_iff g a b c).mpr he)
  · rintro ⟨f, hf⟩
    let xs := List.ofFn fun i : Fin g.1 => (f i).val
    have hget (i : Fin g.1) : xs.getD i.val 0 = (f i).val := by
      simp [xs, List.getD_eq_getElem?_getD]
    refine ⟨xs, (mem_allWords _ _ _).mpr ⟨by simp [xs], ?_⟩, ?_, ?_⟩
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact List.mem_range.mpr (f i).isLt
    · intro x hx y hy hxy
      have hxy' : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
        apply Fin.ext
        simpa only [← hget] using hxy
      exact congrArg Fin.val (hf.1 hxy')
    · intro x hx y hy z hz he
      let a : Fin g.1 := ⟨x, hx⟩
      let b : Fin g.1 := ⟨y, hy⟩
      let c : Fin g.1 := ⟨z, hz⟩
      have he' : {a, b, c} ∈ (decodeGraph g).edges := (codeEdge_iff g a b c).mp he
      have him : {f a, f b, f c} ∈ (decodeGraph h).edges := by simpa using hf.2 _ he'
      have hc := (codeEdge_iff h (f a) (f b) (f c)).mpr him
      simpa only [← hget] using hc

end TuranUniversality.Effective
