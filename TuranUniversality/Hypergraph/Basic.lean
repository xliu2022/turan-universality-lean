module

/- Adapted from xliu2022/improved-sidorenko-lean, commit
   ba6f109bf01436ca15e55fdf5d35dbea85ffd9c9, under Apache-2.0.
   Changes: project namespace and retained only graph definitions and edge bound. -/

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

@[expose] public section

namespace TuranUniversality
universe u v
/-- A simple r-uniform hypergraph with a finite edge set. The main statements
use finite vertex types Fin k. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace RGraph

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

@[ext] theorem ext {G H : RGraph V r} (h : G.edges = H.edges) : G = H := by
  cases G
  cases H
  cases h
  rfl

instance : DecidableEq (RGraph V r) := fun G H =>
  if h : G.edges = H.edges then isTrue (ext h)
  else isFalse (fun h' => h (congrArg RGraph.edges h'))

/-- The paper requires global injectivity, including on isolated vertices. -/
def IsEmbedding (F : RGraph V r) (H : RGraph W r) (f : V → W) : Prop :=
  Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges

instance [Fintype V] (F : RGraph V r) (H : RGraph W r) (f : V → W) :
    Decidable (F.IsEmbedding H f) :=
  inferInstanceAs (Decidable (Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges))

/-- Every host edge belongs to the family of all `r`-subsets of its vertices. -/
theorem edge_card_le_choose {r n : ℕ} (H : RGraph (Fin n) r) :
    H.edges.card ≤ n.choose r := by
  classical
  have hsub : H.edges ⊆ (Finset.univ : Finset (Fin n)).powersetCard r := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, H.uniform e he⟩
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card hsub

end RGraph
end TuranUniversality
