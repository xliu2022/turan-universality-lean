module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Halting

/-!
# Turing Universality in Hypergraph Turán Theory

Independent combined statements for Theorems 1.1, 1.2 and 1.3.
Formalization author and maintainer: Xizhi Liu.

Theorem 1.1 reduces the fixed binary halting problem to ordinary Turán density
for one finite three-uniform hypergraph with an explicit rational threshold.
Theorem 1.2 gives the joint primitive-recursive family and template compilers,
exact density scaling, and a globally optimal fixed template for every r >= 3.
Theorem 1.3 gives fixed balanced finite patterns and edge-edit stability in the
nonhalting case, and two nonempty compact phases with the full homeomorphism
conclusions in the halting case.

Each theorem retains its original quantifiers and witnesses. All mathematical
definitions are independently restated here, with common declarations shared.
Only Mathlib is imported. The three deliberate target proof holes are filled
by same-named theorems in Solution.lean, which does not import this module.
-/

@[expose] public section

open scoped BigOperators symmDiff
open Filter Topology

namespace TuranUniversality

universe u v

/-- A simple uniform hypergraph consists of a finite set of edges, each an
unordered vertex subset of the indicated cardinality. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- Ordinary subgraph embeddings preserve edges and are globally injective,
including on isolated vertices. Induced embeddings are not required. -/
def RGraph.IsEmbedding {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] {r : ℕ}
    (F : RGraph V r) (H : RGraph W r) (f : V → W) : Prop :=
  Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges

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

def IsHom (F : RGraph V r) (G : RGraph W r) (f : V → W) : Prop :=
  ∀ e ∈ F.edges, e.image f ∈ G.edges

def HomFree (F : RGraph V r) (G : RGraph W r) : Prop :=
  ¬ ∃ f : V → W, F.IsHom G f

abbrev BlowupVertex {V : Type u} (sizes : V → ℕ) := Σ v, Fin (sizes v)

noncomputable def blowup {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (sizes : V → ℕ) : RGraph (BlowupVertex sizes) r := by
  classical
  exact ⟨(Finset.univ.powersetCard r).filter
    (fun e => e.image Sigma.fst ∈ G.edges),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

end RGraph

abbrev FiniteGraph (r : ℕ) := Σ n : ℕ, RGraph (Fin n) r

def familyFree {r : ℕ} {V : Type u} [DecidableEq V]
    (F : Finset (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, ¬ ∃ f, A.2.IsEmbedding G f

def familyHomFree {r : ℕ} {V : Type u} [DecidableEq V]
    (F : Finset (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, A.2.HomFree G

open scoped BigOperators

def RGraph.edgePolynomial {V : Type u} [DecidableEq V] {r : ℕ}
    (G : RGraph V r) (x : V → ℝ) : ℝ := ∑ e ∈ G.edges, ∏ v ∈ e, x v

def ProbabilityWeights {V : Type u} [Fintype V] (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1

noncomputable section

/-- The largest edge count of an ordinary `F`-free simple uniform hypergraph
on `Fin n`, with zero as the default if there is no such host. -/
def extremalNumber {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ∃ H : RGraph (Fin n) r,
    (¬ ∃ f, F.IsEmbedding H f) ∧ H.edges.card = m) (n.choose r)

/-- The ordinary binomial normalization `ex(n,F) / choose(n,r)`. -/
def extremalDensity {r k : ℕ} (F : RGraph (Fin k) r) (n : ℕ) : ℝ :=
  (extremalNumber F n : ℝ) / (n.choose r : ℝ)

/-- The infimum of the normalized extremal numbers for orders at least the
uniformity. The main statement also asserts convergence to this value. -/
def turanDensity {r k : ℕ} (F : RGraph (Fin k) r) : ℝ :=
  ⨅ n : ℕ, extremalDensity F (n + r)

namespace RGraph

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

instance [Fintype V] (F : RGraph V r) (H : RGraph W r) (f : V → W) :
    Decidable (F.IsEmbedding H f) :=
  inferInstanceAs (Decidable (Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges))

end RGraph

namespace RGraph

variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

/-- Explicit enumeration fixes the finite search used by the family extremal number. -/
def enumerate (V : Type u) [DecidableEq V] [Fintype V] (r : ℕ) : Finset (RGraph V r) :=
  ((Finset.univ : Finset V).powersetCard r).powerset.attach.image fun p =>
    ⟨p.val, fun _e he => (Finset.mem_powersetCard.mp
      (Finset.mem_powerset.mp p.property he)).2⟩

@[simp] theorem mem_enumerate (G : RGraph V r) : G ∈ enumerate V r := by
  let p : ((Finset.univ : Finset V).powersetCard r).powerset :=
    ⟨G.edges, Finset.mem_powerset.mpr (fun e he =>
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, G.uniform e he⟩)⟩
  exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, RGraph.ext rfl⟩

instance : Fintype (RGraph V r) := ⟨enumerate V r, mem_enumerate⟩

end RGraph

instance {r : ℕ} {V : Type u} [DecidableEq V] [Fintype V]
    (F : Finset (FiniteGraph r)) (G : RGraph V r) : Decidable (familyFree F G) :=
  inferInstanceAs (Decidable (∀ A ∈ F, ¬ ∃ f, A.2.IsEmbedding G f))

/-- Ordinary extremal number for a finite forbidden family. -/
def familyExtremalNumber {r : ℕ} (F : Finset (FiniteGraph r)) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun m => ∃ G : RGraph (Fin n) r,
    familyFree F G ∧ G.edges.card = m) (n.choose r)

def familyExtremalDensity {r : ℕ} (F : Finset (FiniteGraph r)) (n : ℕ) : ℝ :=
  (familyExtremalNumber F n : ℝ) / (n.choose r : ℝ)

def familyTuranDensity {r : ℕ} (F : Finset (FiniteGraph r)) : ℝ :=
  ⨅ n : ℕ, familyExtremalDensity F (n + r)

end

namespace Weighted

/-- The manuscript's explicit rational value `6 B*`. Here `q` is its quartic
root count, `k` is the parameter κ, and `t = κ / (q + κ)` is the maximizing
data mass in the rational baseline polynomial. -/
def rationalThreshold (m : ℚ) : ℚ :=
  let q := (m ^ 4 - 10 * m ^ 3 + 13 * m ^ 2 + 12 * m + 4) / 8
  let k := m / 2 - 1 / (m - 1)
  let t := k / (q + k)
  6 * ((q - 1) * (q - 2) / (6 * q ^ 2) * (1 - t) ^ 3 +
    (q - 2) / (2 * q) * (1 - t) ^ 2 * t +
    (m - 1) / (2 * m) * (1 - t) * t ^ 2)

end Weighted

namespace Effective

/-- An ordered triple of natural-number vertex labels. -/
abbrev Triple := ℕ × ℕ × ℕ

/-- A graph code records its number of vertices and a finite list of triples.
Order and repeated listed triples do not create directed edges or multiplicity. -/
abbrev GraphCode := ℕ × List Triple

/-- Forget the ordering and repeated vertices of one listed triple. -/
def tripleSet (t : Triple) : Finset ℕ := {t.1, t.2.1, t.2.2}

/-- Decode a finite simple three-uniform hypergraph. A listed triple creates
an edge exactly when it names three distinct vertices within the recorded
vertex range; every other listed triple is ignored. -/
def decodeGraph (g : GraphCode) : RGraph (Fin g.1) 3 where
  edges := (Finset.univ.powersetCard 3).filter fun e =>
    ∃ t ∈ g.2, e.image Fin.val = tripleSet t
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

def decodeGraphCode (g : GraphCode) : FiniteGraph 3 := ⟨g.1, decodeGraph g⟩

namespace Uniform

/-- A rank-independent finite code: order and lists of vertex labels. -/
abbrev Code := ℕ × List (List ℕ)

def decode (r : ℕ) (g : Code) : RGraph (Fin g.1) r where
  edges := (Finset.univ.powersetCard r).filter fun e =>
    ∃ w ∈ g.2, w.length = r ∧ e.image Fin.val = w.toFinset
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

def decodeFinite (r : ℕ) (g : Code) : FiniteGraph r := ⟨g.1, decode r g⟩

noncomputable def decodeFamily (r : ℕ) (gs : List Code) : Finset (FiniteGraph r) := by
  classical
  exact (gs.map (decodeFinite r)).toFinset

end Uniform
end Effective

namespace Computation

open Nat.Partrec (Code)

/-- A literal finite word over the two-symbol alphabet. -/
abbrev BinaryWord := List Bool

/-- The numerical value of a little-endian word. This payload decoder does
not identify the input words themselves; the compiler accepts literal lists. -/
def binaryValue (w : BinaryWord) : ℕ :=
  w.foldr (fun b n => bif b then 2 * n + 1 else 2 * n) 0

/-- The tail of an input is interpreted as the standard natural-number code
of a Mathlib partial-recursive program. -/
def decodeProgram (w : BinaryWord) : Code :=
  Denumerable.ofNat Code (binaryValue w.tail)

/-- A leading true bit enables execution. The empty word and words with a
leading false bit are reserved divergent inputs. -/
def inputEnabled (w : BinaryWord) : Bool := w.head?.getD false

/-- Run the decoded partial-recursive program on zero when enabled; diverge
otherwise. Every partial-recursive program occurs among the enabled inputs. -/
def wordEval (w : BinaryWord) : Part ℕ :=
  bif inputEnabled w then (decodeProgram w).eval 0 else Part.none

/-- Halting means that the explicitly specified partial evaluation is defined. -/
def WordHalts (w : BinaryWord) : Prop := (wordEval w).Dom

end Computation

namespace Uniformity

def densityScale (r : ℕ) : ℚ := 27 * (r.factorial : ℚ) / (6 * (r : ℚ) ^ r)

end Uniformity

namespace RGraph

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

instance (F : RGraph V r) (G : RGraph W r) (f : V → W) : Decidable (F.IsHom G f) :=
  inferInstanceAs (Decidable (∀ e ∈ F.edges, e.image f ∈ G.edges))

noncomputable def homIndicator (F : RGraph V r) (G : RGraph W r) (f : V → W) : ℝ := by
  classical
  exact if F.IsHom G f then 1 else 0

def oneEdge (r : ℕ) : RGraph (Fin r) r where
  edges := {Finset.univ}
  uniform e he := by
    rw [Finset.mem_singleton] at he
    rw [he]
    exact Finset.card_fin r

end RGraph

namespace RGraph

variable {U V : Type*} [DecidableEq U] [DecidableEq V] {r : ℕ}

def edgeSymmDifference (G H : RGraph V r) : RGraph V r where
  edges := G.edges ∆ H.edges
  uniform e he := by
    rcases Finset.mem_symmDiff.mp he with h | h
    · exact G.uniform e h.1
    · exact H.uniform e h.1

end RGraph

noncomputable def RGraph.normalizedEditDistance {V : Type u}
    [DecidableEq V] [Fintype V] {r : ℕ} (G H : RGraph V r) : ℝ :=
  ((G.edgeSymmDifference H).edges.card : ℝ) / (Fintype.card V : ℝ) ^ r

namespace RGraph

end RGraph

namespace Selector
noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ := 𝔼 x, f x
end Selector

noncomputable def RGraph.homDensity {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] {r : ℕ} [Fintype V] [Fintype W]
    (F : RGraph V r) (G : RGraph W r) : ℝ := Selector.mean (F.homIndicator G)

namespace SetFamily

abbrev Profile (r : ℕ) := FiniteGraph r → ℝ

noncomputable def profile {r : ℕ} (G : FiniteGraph r) : Profile r :=
  fun A => A.2.homDensity G.2

noncomputable def finiteProfiles (r : ℕ) : Set (Profile r) :=
  {W | ∃ G : FiniteGraph r, 0 < G.1 ∧ W = profile G}

def IsLimitProfile {r : ℕ} (W : Profile r) : Prop := W ∈ closure (finiteProfiles r)

def edgeTest (r : ℕ) : FiniteGraph r := ⟨r, RGraph.oneEdge r⟩

def Vanishes {r : ℕ} (F : Set (FiniteGraph r)) (W : Profile r) : Prop :=
  ∀ A ∈ F, W A = 0

def freeLimitProfiles {r : ℕ} (F : Set (FiniteGraph r)) : Set (Profile r) :=
  {W | IsLimitProfile W ∧ Vanishes F W}

noncomputable def extremalProfiles {r : ℕ} (F : Finset (FiniteGraph r)) : Set (Profile r) :=
  freeLimitProfiles (F : Set (FiniteGraph r)) ∩ {W | W (edgeTest r) = familyTuranDensity F}

end SetFamily

namespace Density

variable {A B V : Type*}

def productWeight [Fintype A] (x : V → ℝ) (f : A → V) : ℝ :=
  ∏ a, x (f a)

def weightedMean [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (F : (A → V) → ℝ) : ℝ := ∑ f, productWeight x f * F f

noncomputable def truth (p : Prop) : ℝ := by classical exact if p then 1 else 0

end Density

structure FiniteRolePattern (R : Type*) (r : ℕ) where
  edges : Finset (Multiset R)
  uniform : ∀ m ∈ edges, m.card = r

namespace FiniteRolePattern

variable {R V W : Type*} [DecidableEq R] [DecidableEq V] [DecidableEq W]
variable [Fintype V] {r : ℕ}

def graph (P : FiniteRolePattern R r) (ρ : V → R) : RGraph V r where
  edges := (Finset.univ.powersetCard r).filter (fun e => e.val.map ρ ∈ P.edges)
  uniform e he := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

end FiniteRolePattern

namespace FiniteRolePattern

variable {R U V : Type*} [DecidableEq R] [DecidableEq U] [DecidableEq V]
variable [Fintype R] [Fintype U] [Fintype V] {r : ℕ}

def Compatible (P : FiniteRolePattern R r) (H : RGraph U r) (θ : U → R) : Prop :=
  ∀ e ∈ H.edges, e.val.map θ ∈ P.edges

noncomputable def coordinate (P : FiniteRolePattern R r) (H : RGraph U r) (z : R → ℝ) : ℝ :=
  Density.weightedMean z (fun θ => Density.truth (P.Compatible H θ))

noncomputable def profile (P : FiniteRolePattern R r) (z : R → ℝ) : SetFamily.Profile r :=
  fun H => P.coordinate H.2 z

end FiniteRolePattern

namespace PartitionRounding

variable {V : Type u} {A : Type v} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A]

def fiberSize (ρ : V → A) (a : A) : ℕ := (Finset.univ.filter fun v => ρ v = a).card

end PartitionRounding

namespace Registry

/-- Theorem 1.1: one fixed rational threshold and one primitive-recursive
compiler reduce this fixed universal binary halting problem to ordinary
Turán-density equality and strict inequality for single finite three-graphs.
There are no assumed extremal, semantic, or compiler-correctness hypotheses. -/
def mainStatement : Prop :=
  ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
    (∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧ τ = Weighted.rationalThreshold (m : ℚ)) ∧
    ∃ compiler : List Bool → Effective.GraphCode, Primrec compiler ∧
      ∀ w : List Bool,
        1 ≤ (Effective.decodeGraph (compiler w)).edges.card ∧
        Tendsto (extremalDensity (Effective.decodeGraph (compiler w))) atTop
          (𝓝 (turanDensity (Effective.decodeGraph (compiler w)))) ∧
        (turanDensity (Effective.decodeGraph (compiler w)) = (τ : ℝ) ↔
          ¬ Computation.WordHalts w) ∧
        ((τ : ℝ) < turanDensity (Effective.decodeGraph (compiler w)) ↔
          Computation.WordHalts w)

/-- Theorem 1.1. The threshold, primitive-recursive compiler, ordinary density
limit and both halting equivalences are stated explicitly. -/
theorem main_theorem :
    ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
      (∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧ τ = Weighted.rationalThreshold (m : ℚ)) ∧
      ∃ compiler : List Bool → Effective.GraphCode, Primrec compiler ∧
        ∀ w : List Bool,
          1 ≤ (Effective.decodeGraph (compiler w)).edges.card ∧
          Tendsto (extremalDensity (Effective.decodeGraph (compiler w))) atTop
            (𝓝 (turanDensity (Effective.decodeGraph (compiler w)))) ∧
          (turanDensity (Effective.decodeGraph (compiler w)) = (τ : ℝ) ↔
            ¬ Computation.WordHalts w) ∧
          ((τ : ℝ) < turanDensity (Effective.decodeGraph (compiler w)) ↔
            Computation.WordHalts w) := by
  sorry

/-- Theorem 1.2. The literal r=3 singleton, ordinary density limit, exact
scaling, fixed template, global uniform optimality and joint effectivity
are all part of the same statement. -/
theorem numerical_main_theorem :
  ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
    (∃ m : ℕ, 30 ≤ m ∧ m % 4 = 2 ∧ τ = Weighted.rationalThreshold (m : ℚ)) ∧
    ∃ single : List Bool → Effective.GraphCode, Primrec single ∧
    ∃ families : ℕ × List Bool → List Effective.Uniform.Code, Primrec families ∧
    ∃ templates : ℕ → Effective.Uniform.Code, Primrec templates ∧
      (∀ w, Effective.Uniform.decodeFamily 3 (families (3, w)) =
        {Effective.decodeGraphCode (single w)}) ∧
      ∀ r : ℕ, 3 ≤ r →
        let τr := Uniformity.densityScale r * τ
        let K := Effective.Uniform.decode r (templates r)
        0 < τr ∧ τr < 1 ∧ 0 < (templates r).1 ∧
        (r.factorial : ℝ) * K.edgePolynomial (fun _ => ((templates r).1 : ℝ)⁻¹) = (τr : ℝ) ∧
        (∀ x, ProbabilityWeights x → (r.factorial : ℝ) * K.edgePolynomial x ≤ (τr : ℝ)) ∧
        ∀ w : List Bool,
          let F := Effective.Uniform.decodeFamily r (families (r, w))
          (∀ A ∈ F, 1 ≤ A.2.edges.card) ∧
          Tendsto (familyExtremalDensity F) atTop (𝓝 (familyTuranDensity F)) ∧
          familyTuranDensity F = (Uniformity.densityScale r : ℝ) *
            turanDensity (Effective.decodeGraph (single w)) ∧
          (familyTuranDensity F = (τr : ℝ) ↔ ¬ Computation.WordHalts w) ∧
          ((τr : ℝ) < familyTuranDensity F ↔ Computation.WordHalts w) ∧
          familyHomFree F K ∧
          ∀ sizes, familyFree F (K.blowup sizes) := by
  sorry

end Registry
end TuranUniversality

namespace TuranUniversality.Registry.Structural

/-- A fixed balanced rounding for the role proportions, valid at every order. -/
def BalancedCounts {k : ℕ} (z : Fin k → ℝ) (d : ℕ → Fin k → ℕ) : Prop :=
  ∀ n, (∑ a, d n a) = n ∧
    ∀ a, d n a = ⌊(n : ℝ) * z a⌋₊ ∨ d n a = ⌈(n : ℝ) * z a⌉₊

/-- Every ordinary near-extremal free sequence is close, on its original
vertex set, to the same finite multiset pattern with the fixed class sizes. -/
def StableWithPattern {r k : ℕ} (F : Finset (FiniteGraph r))
    (P : FiniteRolePattern (Fin k) r) (d : ℕ → Fin k → ℕ) : Prop :=
  ∀ (n : ℕ → ℕ) (G : ∀ i, RGraph (Fin (n i)) r),
    (∀ i, 0 < n i) → Tendsto n atTop atTop →
    (∀ i, familyFree F (G i)) →
    Tendsto (fun i => (RGraph.oneEdge r).homDensity (G i)) atTop
      (𝓝 (familyTuranDensity F)) →
    ∃ θ : ∀ i, Fin (n i) → Fin k,
      (∀ i a, PartitionRounding.fiberSize (θ i) a = d (n i) a) ∧
      Tendsto (fun i => (G i).normalizedEditDistance (P.graph (θ i))) atTop (𝓝 0)

/-- The separator uses two fixed ordinary finite test graphs. -/
def Separator {r : ℕ} (T₁ T₂ : FiniteGraph r) (W : SetFamily.Profile r) : ℝ :=
  W T₁ - W T₂

/-- Both compact phases retain the entire inner extremal space. -/
def TwoPhases {r : ℕ} (F : Finset (FiniteGraph r)) (P : FiniteGraph 3)
    (T₁ T₂ : FiniteGraph r) : Prop :=
  ∃ (c : ℝ), 0 < c ∧ ∃ phase : Bool → Set (SetFamily.Profile r),
    SetFamily.extremalProfiles F = phase false ∪ phase true ∧
    Disjoint (phase false) (phase true) ∧
    (∀ s, IsCompact (phase s) ∧ (phase s).Nonempty ∧
      Nonempty (SetFamily.extremalProfiles {P} ≃ₜ phase s) ∧
      ∀ W ∈ phase s, Separator T₁ T₂ W = if s then -c else c) ∧
    Nonempty ((Bool × SetFamily.extremalProfiles {P}) ≃ₜ SetFamily.extremalProfiles F)

end Structural

/-- V4 Theorem 1.3, including the actual edge-edit conclusion. The fixed
rank threshold, numbered profile, rounding counts and separator graphs are
chosen independently of the binary input. The inner singleton compiler also
retains the ordinary density dichotomy of Theorem 1.1. -/
def structuralStatement : Prop :=
  ∃ τ : ℚ, 0 < τ ∧ τ < 1 ∧
    ∃ inner : Computation.BinaryWord → Effective.GraphCode,
      Primrec inner ∧
      (∀ β, (Effective.decodeGraph (inner β)).edges.Nonempty ∧
        (turanDensity (Effective.decodeGraph (inner β)) = (τ : ℝ) ↔
          ¬ Computation.WordHalts β) ∧
        ((τ : ℝ) < turanDensity (Effective.decodeGraph (inner β)) ↔
          Computation.WordHalts β)) ∧
      ∃ R : ℕ, 4 ≤ R ∧
        ∃ compiler : ℕ → Computation.BinaryWord → List Effective.Uniform.Code,
          Primrec₂ compiler ∧
          ∀ r, R ≤ r →
            ∃ (k : ℕ) (P : FiniteRolePattern (Fin k) r) (z : Fin k → ℝ)
              (d : ℕ → Fin k → ℕ) (T₁ T₂ : FiniteGraph r),
              0 < k ∧ ProbabilityWeights z ∧ Structural.BalancedCounts z d ∧
              (∀ β,
                let F := Effective.Uniform.decodeFamily r (compiler r β)
                (¬ Computation.WordHalts β →
                  SetFamily.extremalProfiles F = {P.profile z} ∧
                    Structural.Separator T₁ T₂ (P.profile z) = 0 ∧
                    Structural.StableWithPattern F P d) ∧
                (Computation.WordHalts β →
                  Structural.TwoPhases F (Effective.decodeGraphCode (inner β)) T₁ T₂))

end TuranUniversality.Registry

namespace TuranUniversality.Registry

theorem structural_main_theorem : structuralStatement := by
  sorry

end TuranUniversality.Registry
