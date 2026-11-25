module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# A bounded witness search tree

The tree argument underlying bounded-root elimination is finite. A node has
at most b children, the rank increases by one on every edge, and ranks are at
most q. The union of witnesses of size at most w therefore has order at most
w ∑_{j=0}^q b^j, and cannot admit a compatible repair that always creates a child.
-/

open scoped BigOperators

namespace TuranUniversality.BoundedSearch

universe u v z
variable {S : Type u} {V : Type v} {R : Type z}
variable [DecidableEq S] [DecidableEq V]

def layer (children : S → Finset S) (start : S) : ℕ → Finset S
  | 0 => {start}
  | n + 1 => (layer children start n).biUnion children

theorem layer_card_le (children : S → Finset S) (start : S) (b : ℕ)
    (hb : ∀ s, (children s).card ≤ b) (n : ℕ) :
    (layer children start n).card ≤ b ^ n := by
  induction n with
  | zero => simp [layer]
  | succ n ih =>
      calc
        (layer children start (n + 1)).card ≤
            ∑ s ∈ layer children start n, (children s).card := Finset.card_biUnion_le
        _ ≤ ∑ _s ∈ layer children start n, b := Finset.sum_le_sum (fun s _ => hb s)
        _ = (layer children start n).card * b := by simp
        _ ≤ b ^ n * b := Nat.mul_le_mul_right b ih
        _ = b ^ (n + 1) := (pow_succ b n).symm

theorem rank_on_layer (children : S → Finset S) (start : S) (rank : S → ℕ)
    (hr : ∀ s t, t ∈ children s → rank t = rank s + 1)
    (n : ℕ) {s : S} (hs : s ∈ layer children start n) :
    rank s = rank start + n := by
  induction n generalizing s with
  | zero =>
      have hs' : s = start := by simpa only [layer, Finset.mem_singleton] using hs
      simp [hs']
  | succ n ih =>
      obtain ⟨t, ht, hts⟩ := Finset.mem_biUnion.mp hs
      rw [hr t s hts, ih ht]
      omega

theorem terminal_layer_empty (children : S → Finset S) (start : S) (rank : S → ℕ)
    (q : ℕ) (hq : ∀ s, rank s ≤ q)
    (hr : ∀ s t, t ∈ children s → rank t = rank s + 1) :
    layer children start (q + 1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have h := rank_on_layer children start rank hr (q + 1) hs
  have hsq := hq s
  omega

def witnesses (children : S → Finset S) (start : S) (witness : S → Finset V)
    (q : ℕ) : Finset V :=
  (Finset.range (q + 1)).biUnion fun n => (layer children start n).biUnion witness

theorem witness_subset (children : S → Finset S) (start : S) (witness : S → Finset V)
    {q n : ℕ} (hn : n ≤ q) {s : S} (hs : s ∈ layer children start n) :
    witness s ⊆ witnesses children start witness q := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by omega),
    Finset.mem_biUnion.mpr ⟨s, hs, hv⟩⟩

theorem witnesses_card_le (children : S → Finset S) (start : S)
    (witness : S → Finset V) (q b w : ℕ)
    (hb : ∀ s, (children s).card ≤ b) (hw : ∀ s, (witness s).card ≤ w) :
    (witnesses children start witness q).card ≤ w * ∑ n ∈ Finset.range (q + 1), b ^ n := by
  have hl (n : ℕ) : ((layer children start n).biUnion witness).card ≤ b ^ n * w := by
    calc
      ((layer children start n).biUnion witness).card ≤
          ∑ s ∈ layer children start n, (witness s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ layer children start n, w := Finset.sum_le_sum (fun s _ => hw s)
      _ = (layer children start n).card * w := by simp
      _ ≤ b ^ n * w := Nat.mul_le_mul_right w (layer_card_le children start b hb n)
  calc
    (witnesses children start witness q).card ≤
        ∑ n ∈ Finset.range (q + 1), ((layer children start n).biUnion witness).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ n ∈ Finset.range (q + 1), b ^ n * w := Finset.sum_le_sum (fun n _ => hl n)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem no_infinite_compatible_branch (children : S → Finset S) (start : S)
    (rank : S → ℕ) (q : ℕ) (hq : ∀ s, rank s ≤ q)
    (hr : ∀ s t, t ∈ children s → rank t = rank s + 1)
    (Good : S → Prop) (hstart : Good start)
    (hstep : ∀ n ≤ q, ∀ s ∈ layer children start n,
      Good s → ∃ t ∈ children s, Good t) : False := by
  have hreach (n : ℕ) (hn : n ≤ q + 1) : ∃ s ∈ layer children start n, Good s := by
    induction n with
    | zero => exact ⟨start, by simp [layer], hstart⟩
    | succ n ih =>
        obtain ⟨s, hs, hgs⟩ := ih (by omega)
        obtain ⟨t, ht, hgt⟩ := hstep n (by omega) s hs hgs
        exact ⟨t, Finset.mem_biUnion.mpr ⟨s, hs, ht⟩, hgt⟩
  obtain ⟨s, hs, _⟩ := hreach (q + 1) le_rfl
  rw [terminal_layer_empty children start rank q hq hr] at hs
  exact Finset.notMem_empty s hs

/-- The bounded-search obstruction theorem. `Admissible T rho` is any proposed
repair on the retained witness set T. The repair rule must actually extend the
search by a child whenever a compatible node's witness has been retained. -/
theorem bounded_obstruction (children : S → Finset S) (start : S)
    (rank : S → ℕ) (witness : S → Finset V) (q b w : ℕ)
    (hq : ∀ s, rank s ≤ q)
    (hr : ∀ s t, t ∈ children s → rank t = rank s + 1)
    (hb : ∀ s, (children s).card ≤ b) (hw : ∀ s, (witness s).card ≤ w)
    (Admissible : Finset V → R → Prop) (Compatible : S → R → Prop)
    (hstart : ∀ rho, Compatible start rho)
    (hrepair : ∀ T rho, Admissible T rho → ∀ s, Compatible s rho →
      witness s ⊆ T → ∃ t ∈ children s, Compatible t rho) :
    ∃ T : Finset V, T.card ≤ w * ∑ n ∈ Finset.range (q + 1), b ^ n ∧
      ∀ rho, ¬ Admissible T rho := by
  let T := witnesses children start witness q
  refine ⟨T, witnesses_card_le children start witness q b w hb hw, ?_⟩
  intro rho hadm
  apply no_infinite_compatible_branch children start rank q hq hr
    (fun s => Compatible s rho) (hstart rho)
  intro n hn s hs hcompat
  exact hrepair T rho hadm s hcompat (witness_subset children start witness hn hs)

end TuranUniversality.BoundedSearch
