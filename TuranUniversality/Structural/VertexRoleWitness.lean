module

public import TuranUniversality.Structural.CanonicalWitness

@[expose] public section

/-! # Simultaneous witnesses for every role of one new vertex

At least one edge in each witness contains the new vertex. Taking the
union of the old vertices gives exactly the bound used in Section 9.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem failed_vertex_role_witness (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G G₀ : RGraph V (t + (3 * b + 4))) (v : V) (ρ : V → Option (Roots b t))
    (hG₀ : G₀.edges = G.edges.filter (fun e => v ∉ e))
    (hρ : Admissible B Ω G₀ ρ) (a : Option (Roots b t))
    (hbad : ¬ Admissible B Ω G (Function.update ρ v a)) :
    ∃ E : Finset (Finset V), ∃ W : Finset V,
      E ⊆ G.edges ∧ E.card ≤ Ordinary.roleWitnessEdges B ∧ v ∉ W ∧
      W.card ≤ (t + (3 * b + 4)) * Ordinary.roleWitnessEdges B - 1 ∧
      (∀ e ∈ E, e ⊆ insert v W) ∧
      ∀ (H : RGraph V (t + (3 * b + 4))) (σ : V → Option (Roots b t)),
        E ⊆ H.edges →
        (∀ e ∈ E, ∀ w ∈ e, σ w = Function.update ρ v a w) → ¬ Admissible B Ω H σ := by
  classical
  obtain ⟨E, hEG, hEcard, hfail⟩ := failed_role_witness B Ω hdis G _ hbad
  have hex : ∃ e ∈ E, v ∈ e := by
    by_contra h
    push Not at h
    have hE₀ : E ⊆ G₀.edges := by
      intro e he
      rw [hG₀]
      exact Finset.mem_filter.mpr ⟨hEG he, h e he⟩
    apply hfail G₀ ρ hE₀ _ hρ
    intro e he w hw
    have hwv : w ≠ v := fun h' => h e he (h' ▸ hw)
    simp [Function.update_of_ne hwv]
  let U := E.biUnion id
  have hvU : v ∈ U := by
    obtain ⟨e, he, hv⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩
  have hU : U.card ≤ (t + (3 * b + 4)) * Ordinary.roleWitnessEdges B := by
    calc
      U.card ≤ ∑ e ∈ E, e.card := Finset.card_biUnion_le
      _ = ∑ _e ∈ E, (t + (3 * b + 4)) :=
        Finset.sum_congr rfl (fun e he => G.uniform e (hEG he))
      _ = E.card * (t + (3 * b + 4)) := by simp
      _ ≤ _ := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (t + (3 * b + 4)) hEcard
  refine ⟨E, U.erase v, hEG, hEcard, Finset.notMem_erase _ _, ?_, ?_, hfail⟩
  · rw [Finset.card_erase_of_mem hvU]
    exact Nat.sub_le_sub_right hU 1
  · intro e he w hw
    rw [Finset.insert_erase hvU]
    exact Finset.mem_biUnion.mpr ⟨e, he, hw⟩

theorem all_roles_witness (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Cube.Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G G₀ : RGraph V (t + (3 * b + 4))) (v : V) (ρ : V → Option (Roots b t))
    (hG₀ : G₀.edges = G.edges.filter (fun e => v ∉ e))
    (hρ : Admissible B Ω G₀ ρ) (hbad : ¬ Canonical B Ω G) :
    ∃ (E : Option (Roots b t) → Finset (Finset V)) (S : Finset V),
      v ∉ S ∧ S.card ≤ (t + 5 * b + 1) *
        ((t + (3 * b + 4)) * Ordinary.roleWitnessEdges B - 1) ∧
      (∀ a, E a ⊆ G.edges ∧ (E a).card ≤ Ordinary.roleWitnessEdges B ∧
        ∀ e ∈ E a, e ⊆ insert v S) ∧
      ∀ a (H : RGraph V (t + (3 * b + 4))) (σ : V → Option (Roots b t)),
        E a ⊆ H.edges →
        (∀ e ∈ E a, ∀ w ∈ e, σ w = Function.update ρ v a w) → ¬ Admissible B Ω H σ := by
  classical
  have hfailed (a : Option (Roots b t)) : ¬ Admissible B Ω G (Function.update ρ v a) := by
    intro h
    exact hbad ((canonical_iff B Ω hdis G).mpr ⟨_, h⟩)
  choose E W hEG hEcard hvW hWcard hEW hfail using
    (fun a => failed_vertex_role_witness B Ω hdis G G₀ v ρ hG₀ hρ a (hfailed a))
  let S := Finset.univ.biUnion W
  have hWS (a : Option (Roots b t)) : W a ⊆ S :=
    fun w hw => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hw⟩
  refine ⟨E, S, ?_, ?_, ?_, hfail⟩
  · intro hv
    obtain ⟨a, _, hva⟩ := Finset.mem_biUnion.mp hv
    exact hvW a hva
  · calc
      S.card ≤ ∑ a : Option (Roots b t), (W a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a : Option (Roots b t),
          ((t + (3 * b + 4)) * Ordinary.roleWitnessEdges B - 1) :=
        Finset.sum_le_sum (fun a _ => hWcard a)
      _ = _ := by simp [Fintype.card_option, roots_card, Nat.mul_comm]
  · intro a
    exact ⟨hEG a, hEcard a, fun e he => (hEW a e he).trans
      (Finset.insert_subset_insert v (hWS a))⟩

end TuranUniversality.Structural.Roles
