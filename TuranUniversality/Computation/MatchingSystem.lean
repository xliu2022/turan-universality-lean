module

public import TuranUniversality.Computation.StaticWindow
public import TuranUniversality.Weighted.Matching

/-!
# The actual three-indexed-partial-matching computation signature

The color map is read only at a present `J` neighbor.  Horizontal/vertical
successors are the two-edge paths `J;R` and `J;S`.  Missing witnesses do not
activate a local condition, and a single `J` edge may witness several uses.
The finite local specification is a table, not an opaque legality hypothesis.
-/

@[expose] public section

namespace TuranUniversality.Computation.MatchingSystem

open TuranUniversality.Weighted

variable {D Alphabet : Type*} [DecidableEq D]

/-- A finite realization on one ambient vertex carrier. -/
structure Realization (D Alphabet : Type*) [DecidableEq D] where
  cells : Finset D
  colors : Finset D
  disjoint : Disjoint cells colors
  label : D → Alphabet
  J : PartialMatching cells colors
  R : PartialMatching colors cells
  S : PartialMatching colors cells
  marks : Finset D
  marks_cells : marks ⊆ cells

namespace Realization

variable (A : Realization D Alphabet)

def H (x y : D) : Prop := ∃ b, (x, b) ∈ A.J.pairs ∧ (b, y) ∈ A.R.pairs

def V (x y : D) : Prop := ∃ b, (x, b) ∈ A.J.pairs ∧ (b, y) ∈ A.S.pairs

def Lab (x : D) (a : Alphabet) : Prop := ∃ b, (x, b) ∈ A.J.pairs ∧ A.label b = a

theorem pair_left_unique {U V : Finset D} (P : PartialMatching U V)
    {x y z : D} (hxy : (x, y) ∈ P.pairs) (hxz : (x, z) ∈ P.pairs) : y = z :=
  congrArg Prod.snd (P.left_injective hxy hxz rfl)

theorem pair_right_unique {U V : Finset D} (P : PartialMatching U V)
    {x y z : D} (hxz : (x, z) ∈ P.pairs) (hyz : (y, z) ∈ P.pairs) : x = y :=
  congrArg Prod.fst (P.right_injective hxz hyz rfl)

theorem lab_unique {x : D} {a b : Alphabet} (ha : A.Lab x a) (hb : A.Lab x b) : a = b := by
  obtain ⟨y, hy, ha⟩ := ha
  obtain ⟨z, hz, hb⟩ := hb
  have hyz := pair_left_unique A.J hy hz
  exact ha.symm.trans (hyz ▸ hb)

theorem h_left_unique {x y z : D} (hy : A.H x y) (hz : A.H x z) : y = z := by
  obtain ⟨b, hj, hr⟩ := hy
  obtain ⟨c, hj', hr'⟩ := hz
  have hbc := pair_left_unique A.J hj hj'
  subst c
  exact pair_left_unique A.R hr hr'

theorem h_right_unique {x y z : D} (hx : A.H x z) (hy : A.H y z) : x = y := by
  obtain ⟨b, hj, hr⟩ := hx
  obtain ⟨c, hj', hr'⟩ := hy
  have hbc := pair_right_unique A.R hr hr'
  subst c
  exact pair_right_unique A.J hj hj'

theorem v_left_unique {x y z : D} (hy : A.V x y) (hz : A.V x z) : y = z := by
  obtain ⟨b, hj, hs⟩ := hy
  obtain ⟨c, hj', hs'⟩ := hz
  have hbc := pair_left_unique A.J hj hj'
  subst c
  exact pair_left_unique A.S hs hs'

theorem v_right_unique {x y z : D} (hx : A.V x z) (hy : A.V y z) : x = y := by
  obtain ⟨b, hj, hs⟩ := hx
  obtain ⟨c, hj', hs'⟩ := hy
  have hbc := pair_right_unique A.S hs hs'
  subst c
  exact pair_right_unique A.J hj hj'

/-- Undirected incidence adjacency, retaining all three indexed relations. -/
def Neighbor (x y : D) : Prop :=
  (x, y) ∈ A.J.pairs ∨ (y, x) ∈ A.J.pairs ∨
  (x, y) ∈ A.R.pairs ∨ (y, x) ∈ A.R.pairs ∨
  (x, y) ∈ A.S.pairs ∨ (y, x) ∈ A.S.pairs

def Connected (x y : D) : Prop := Relation.ReflTransGen A.Neighbor x y

theorem neighbor_symm {x y : D} (h : A.Neighbor x y) : A.Neighbor y x := by
  unfold Neighbor at *
  tauto

theorem connected_symm {x y : D} (h : A.Connected x y) : A.Connected y x := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.head (A.neighbor_symm h)

def CellComplete (x : D) : Prop :=
  (∃ b, (x, b) ∈ A.J.pairs) ∧
  (∃ b, (b, x) ∈ A.R.pairs) ∧ (∃ b, (b, x) ∈ A.S.pairs)

def ColorComplete (b : D) : Prop :=
  (∃ x, (x, b) ∈ A.J.pairs) ∧
  (∃ x, (b, x) ∈ A.R.pairs) ∧ (∃ x, (b, x) ∈ A.S.pairs)

/-- Every indexed incidence is present throughout the marked component. -/
def ClosedAt (a : D) : Prop := ∀ x, A.Connected a x →
  (x ∈ A.cells → A.CellComplete x) ∧ (x ∈ A.colors → A.ColorComplete x)

end Realization

/-- A present path of exactly `n` horizontal successor steps. -/
def Path (r : D → D → Prop) : ℕ → D → D → Prop
  | 0, x, y => x = y
  | n + 1, x, z => ∃ y, r x y ∧ Path r n y z

theorem path_mono {r s : D → D → Prop} (h : ∀ x y, r x y → s x y)
    {n : ℕ} {x y : D} (hp : Path r n x y) : Path s n x y := by
  induction n generalizing x with
  | zero => exact hp
  | succ n ih =>
    obtain ⟨z, hxz, hzy⟩ := hp
    exact ⟨z, h x z hxz, ih hzy⟩

/-- A finite, inspectable local table and its finite Start-prefix constraints. -/
structure Specification (Alphabet : Type*) [DecidableEq Alphabet] where
  leftWall : Alphabet
  initial : Finset Alphabet
  horizontal : Finset (Alphabet × Alphabet)
  evolution : Finset (Alphabet × Alphabet × Alphabet × Alphabet)
  prefixTrigger : Finset Alphabet
  inputPrefix : List (Finset Alphabet)

namespace Realization

variable [DecidableEq Alphabet] (A : Realization D Alphabet) (P : Specification Alphabet)

def Q1 : Prop := ∀ x e n y z,
  A.H x e → A.V x n → A.V e y → A.H n z → y = z

def Q2 : Prop := ∀ l x r x' al ax ar b,
  A.H l x → A.H x r → A.V x x' →
  A.Lab l al → A.Lab x ax → A.Lab r ar → A.Lab x' b →
  (al, ax, ar, b) ∈ P.evolution

def Q3 : Prop := ∀ x y a b,
  A.H x y → A.Lab x a → A.Lab y b → (a, b) ∈ P.horizontal

/-- The marked first cell has a left-wall predecessor and initial phase. -/
def Q4Marked : Prop := ∀ a ∈ A.marks, ∀ y sy sa,
  A.H y a → A.Lab y sy → A.Lab a sa → sy = P.leftWall ∧ sa ∈ P.initial

/-- Every static Start color enforces the entire prescribed finite prefix.
The conditions activate only when their paths and endpoint labels are present. -/
def Q4Prefix : Prop := ∀ x sx, A.Lab x sx → sx ∈ P.prefixTrigger →
  ∀ j (hj : j < P.inputPrefix.length) z sz,
    Path A.H j x z → A.Lab z sz → sz ∈ P.inputPrefix[j]

/-- All five clauses are concrete finite positive-witness conditions. -/
def Legal : Prop := A.Q1 ∧ A.Q2 P ∧ A.Q3 P ∧ A.Q4Marked P ∧ A.Q4Prefix P

end Realization

end TuranUniversality.Computation.MatchingSystem
