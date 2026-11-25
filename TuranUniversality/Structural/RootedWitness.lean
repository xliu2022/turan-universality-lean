module

public import TuranUniversality.Structural.RootedLocal

@[expose] public section

/-! # The structural compiler's bounded rooted failures

Every failed fixed rooting is witnessed on at most `|M| + Q` vertices.
If a larger retained graph repairs that failure by extending the rooting,
it must assign a fresh root to a vertex of this witness. The finite root
elimination theorem then supplies the actual explicit obstruction bound.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Rooted

open Cube Support

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

def witnessBound (b t : ℕ) (B : Finset (FiniteGraph 3)) : ℕ :=
  t + 5 * b + RecordSystem.cutoff B

def obstructionBound (b t : ℕ) (B : Finset (FiniteGraph 3)) : ℕ :=
  witnessBound b t B * ∑ j ∈ Finset.range (t + 5 * b + 1),
    ((t + 5 * b) * witnessBound b t B) ^ j

theorem failed_rooting_witness (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Word b)) (G : RGraph V (t + (3 * b + 4)))
    (μ : Rooting (Roots b t) V) (hbad : ¬ AdmissibleOn B Ω G Finset.univ μ) :
    ∃ W : Finset V, W.card ≤ witnessBound b t B ∧
      ∀ T ν, W ⊆ T → Rooting.Extends μ ν → AdmissibleOn B Ω G T ν →
        ∃ r v, μ.val r = none ∧ ν.val r = some v ∧ v ∈ W ∧ v ∉ μ.range := by
  classical
  by_cases hgood : ∀ e ∈ G.edges, GoodEdge Ω μ e
  · have hlocal : ¬ LocallyLegalOn B Ω G Finset.univ μ :=
      fun h => hbad ⟨fun e he _ => hgood e he, h⟩
    unfold LocallyLegalOn at hlocal
    push Not at hlocal
    obtain ⟨S, hS, hdata, hcard, hfailure⟩ := hlocal
    refine ⟨μ.range ∪ S, ?_, ?_⟩
    · calc
        (μ.range ∪ S).card ≤ μ.range.card + S.card := Finset.card_union_le _ _
        _ ≤ Fintype.card (Roots b t) + RecordSystem.cutoff B :=
          Nat.add_le_add (Selector.rooting_range_card μ) hcard
        _ = witnessBound b t B := by simp [witnessBound, Nat.mul_comm]
    · intro T ν hWT hext hlegal
      by_contra hnew
      have hagree := Selector.inverse_eq_on_of_no_new_root μ ν (μ.range ∪ S) hext hnew
      have hST : S ⊆ T := (Finset.subset_union_right).trans hWT
      have hdataν : ∀ v ∈ S, ν.inverse.val v = none := by
        intro v hv
        rw [hagree v (Finset.mem_union_right _ hv)]
        exact hdata v hv
      obtain ⟨O, hOS, hfitν⟩ := hlegal.2 S hST hdataν hcard
      obtain ⟨e, he, heU, heS, hnot⟩ := hfailure O hOS
      have heW : e ⊆ μ.range ∪ S :=
        (edge_subset_roots_data μ e).trans (Finset.union_subset_union_right heS)
      have heq : ∀ v ∈ e, ν.inverse.val v = μ.inverse.val v :=
        fun v hv => hagree v (heW hv)
      have hdatae : dataSet ν e ⊆ S := by rw [dataSet_congr ν μ e heq]; exact heS
      have hfits := hfitν e he (heW.trans hWT) hdatae
      exact hnot ((fits_congr Ω ν μ O e heq).mp hfits)
  · push Not at hgood
    obtain ⟨e, he, hfail⟩ := hgood
    refine ⟨e, ?_, ?_⟩
    · rw [G.uniform e he]
      have hQ := RecordSystem.cutoff_ge_thirteen B
      unfold witnessBound
      omega
    · intro T ν heT hext hlegal
      by_contra hnew
      have hagree := Selector.inverse_eq_on_of_no_new_root μ ν e hext hnew
      exact hfail ((goodEdge_congr Ω ν μ e hagree).mp (hlegal.1 e he heT))

/-- Root elimination retains a genuinely nonadmissible finite vertex set;
the bound is the finite search-tree bound of Lemma 2.3. -/
theorem bounded_nonadmissible_on (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Word b)) (G : RGraph V (t + (3 * b + 4))) (hbad : ¬ Admits B Ω G) :
    ∃ T : Finset V, T.card ≤ obstructionBound b t B ∧
      ∀ μ : Rooting (Roots b t) V, ¬ AdmissibleOn B Ω G T μ := by
  have hfailed (μ : Rooting (Roots b t) V) : ¬ AdmissibleOn B Ω G Finset.univ μ :=
    fun h => hbad ⟨μ, h⟩
  obtain ⟨T, hcard, hT⟩ := Rooting.bounded_obstruction
    (AdmissibleOn B Ω G) (witnessBound b t B) hfailed
    (failed_rooting_witness B Ω G)
  exact ⟨T, by simpa only [roots_card, obstructionBound] using hcard, hT⟩

end TuranUniversality.Structural.Rooted
