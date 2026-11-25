module

public import TuranUniversality.Effective.StructuralObjects
public import TuranUniversality.Structural.CodePools

@[expose] public section

/-! # Numeric seven-label tests for actual four-vertex records -/

namespace TuranUniversality.Effective.StructuralCodes

open Uniform Structural

def labelCount (l : ℕ) : ℕ := if l < 5 then l else 3

theorem labelCount_correct (l : Fin 7) : labelCount l.val = (CodePools.labelEquiv l).count := by
  fin_cases l <;> rfl

def Labels (n : ℕ) (z : ObjectCode) (d : List ℕ) (l : ℕ) : Prop :=
  (intersectionRow d z.1).length = labelCount l ∧
    (Edge 3 (n, z.2.1) (intersectionRow d z.1) ↔ l = 5) ∧
    (Edge 3 (n, z.2.2) (intersectionRow d z.1) ↔ l = 6)

instance (n : ℕ) (z : ObjectCode) (d : List ℕ) (l : ℕ) : Decidable (Labels n z d l) := by
  unfold Labels
  infer_instance

theorem labels_correct (fs : List Code) (n : ℕ) (z : ObjectCode) (h : Legal fs n z)
    (d : List ℕ) (hd : Good d.length n d) (l : Fin 7) :
    Labels n z d l.val ↔ (object fs n z h).Labels (rowSet n d) (CodePools.labelEquiv l) := by
  have hi := intersectionRow_good hd z.1
  have hset := rowSet_intersectionRow n d z.1
  have he₀ := edge_iff_rowSet_of_distinct (r := 3) z.2.1 (intersectionRow d z.1) hi.2.1 hi.2.2
  have he₁ := edge_iff_rowSet_of_distinct (r := 3) z.2.2 (intersectionRow d z.1) hi.2.1 hi.2.2
  rw [hset] at he₀ he₁
  have hc : (rowSet n d ∩ rowSet n z.1).card = (intersectionRow d z.1).length := by
    rw [← hset]
    exact rowSet_card hi
  unfold Labels LegalObject.Labels
  change _ ↔ (rowSet n d ∩ rowSet n z.1).card = (CodePools.labelEquiv l).count ∧ _
  rw [hc, ← labelCount_correct, he₀, he₁]
  fin_cases l <;> simp [CodePools.labelEquiv, object, Label.phase]

end TuranUniversality.Effective.StructuralCodes
