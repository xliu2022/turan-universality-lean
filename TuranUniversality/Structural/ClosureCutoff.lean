module

public import TuranUniversality.Structural.Record
public import TuranUniversality.Density.HomomorphicClosure

@[expose] public section

/-! # The local record cutoff is unchanged by homomorphic closure -/

namespace TuranUniversality

theorem homomorphicClosure_sup_order_edges {r : ℕ} (F : Finset (FiniteGraph r)) :
    (homomorphicClosure F).sup (fun A => A.1 + A.2.edges.card) =
      F.sup (fun A => A.1 + A.2.edges.card) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro Q hQ
    obtain ⟨_, A, hA, f, hf, he⟩ := (mem_homomorphicClosure F Q).mp hQ
    have hn : Q.1 ≤ A.1 := by simpa using Fintype.card_le_of_surjective f hf
    have hm : Q.2.edges.card ≤ A.2.edges.card := by rw [he]; exact Finset.card_image_le
    exact (Nat.add_le_add hn hm).trans (Finset.le_sup (f := fun A : FiniteGraph r =>
      A.1 + A.2.edges.card) hA)
  · apply Finset.sup_le
    intro A hA
    exact Finset.le_sup (f := fun A : FiniteGraph r => A.1 + A.2.edges.card)
      (mem_homomorphicClosure_of_mem F hA)

namespace Structural.RecordSystem

theorem cutoff_homomorphicClosure (F : Finset (FiniteGraph 3)) :
    cutoff (homomorphicClosure F) = cutoff F := by
  simp only [cutoff, homomorphicClosure_sup_order_edges]

end Structural.RecordSystem

end TuranUniversality
