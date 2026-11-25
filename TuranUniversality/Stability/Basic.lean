module

public import TuranUniversality.Hypergraph.InducedMaps
public import TuranUniversality.Density.LowDegree

@[expose] public section

/-! # Graph classes and the genuine stability hypotheses

Classes range over actual finite vertex types. `EmbeddingClosed` means
closure under subgraphs, as for the class of graphs contained in an intended
extremal configuration. `VertexExtendable` is a one-vertex statement for
graphs of large minimum degree, not a stability conclusion.
-/

namespace TuranUniversality.Stability

universe u

abbrev GraphClass (r : ℕ) :=
  ∀ {V : Type u}, [DecidableEq V] → [Fintype V] → RGraph V r → Prop

def EmbeddingClosed {r : ℕ} (C : GraphClass.{u} r) : Prop :=
  ∀ {V W : Type u} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
    {G : RGraph V r} {H : RGraph W r} {f : V → W}, G.IsEmbedding H f → C H → C G

def HomClosed {r : ℕ} (B : GraphClass.{u} r) : Prop :=
  ∀ {V W : Type u} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
    {G : RGraph V r} {H : RGraph W r} {f : V → W}, G.IsHom H f → B H → B G

def PolynomialBound {r : ℕ} (B : GraphClass.{u} r) (Λ : ℝ) : Prop :=
  ∀ {V : Type u} [DecidableEq V] [Fintype V] (G : RGraph V r), B G →
    ∀ x, ProbabilityWeights x → G.edgePolynomial x ≤ Λ

def MinimumDegree {r : ℕ} {V : Type u} [DecidableEq V] [Fintype V]
    (G : RGraph V r) (d : ℝ) : Prop :=
  ∀ v, d * (Fintype.card V : ℝ) ^ (r - 1) ≤ (G.degree v : ℝ)

def VertexExtendable {r : ℕ} (B C : GraphClass.{u} r) (d : ℝ) (N : ℕ) : Prop :=
  ∀ {V : Type u} [DecidableEq V] [Fintype V] (G : RGraph V r),
    B G → N ≤ Fintype.card V → MinimumDegree G d →
      ∀ v, C (G.induced (Finset.univ.erase v)) → C G

def SymmetrizedStable {r : ℕ} (B C : GraphClass.{u} r) (Λ ε : ℝ) (N : ℕ) : Prop :=
  ∀ {V : Type u} [DecidableEq V] [Fintype V] (G : RGraph V r),
    B G → N ≤ Fintype.card V →
      (Λ - ε) * (Fintype.card V : ℝ) ^ r ≤ (G.edges.card : ℝ) →
        G.Symmetrized → C G

def DegreeStable {r : ℕ} (B C : GraphClass.{u} r) (Λ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
    ∀ {V : Type u} [DecidableEq V] [Fintype V] (G : RGraph V r),
      B G → N ≤ Fintype.card V → MinimumDegree G ((r : ℝ) * Λ - ε) → C G

end TuranUniversality.Stability
