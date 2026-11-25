module

public import TuranUniversality.Stability.Psi

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Degree stability from symmetrization and vertex extendability

This is the full finite Ψ argument for classes with a genuine global
polynomial bound. A homomorphism-closed forbidden class has exactly this
bound at its Lagrangian density. The conclusion concerns every sufficiently
large actual finite graph of the specified minimum degree.
-/

open scoped BigOperators

namespace TuranUniversality.Stability

universe u
variable {r : ℕ} {V : Type u} [DecidableEq V] [Fintype V]

theorem MinimumDegree.mono {G : RGraph V r} {a b : ℝ}
    (h : MinimumDegree G b) (hab : a ≤ b) : MinimumDegree G a :=
  fun v => (mul_le_mul_of_nonneg_right hab
    (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) _)).trans (h v)

theorem VertexExtendable.mono {B C : GraphClass.{u} r} {a b : ℝ} {N : ℕ}
    (h : VertexExtendable B C a N) (hab : a ≤ b) : VertexExtendable B C b N := by
  intro W _ _ G hG hN hmin v hv
  exact h G hG hN (hmin.mono hab) v hv

theorem edge_near_of_minimumDegree (G : RGraph V r) (hr : 1 ≤ r)
    {Λ σ ε : ℝ} (hmin : MinimumDegree G ((r : ℝ) * Λ - σ))
    (hσε : σ ≤ (r : ℝ) * ε) :
    (Λ - ε) * (Fintype.card V : ℝ) ^ r ≤ (G.edges.card : ℝ) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have he : r - 1 + 1 = r := by omega
  have hpow : (Fintype.card V : ℝ) ^ r =
      (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (r - 1) := by
    calc
      (Fintype.card V : ℝ) ^ r = (Fintype.card V : ℝ) ^ (r - 1 + 1) := congrArg _ he.symm
      _ = _ := pow_succ' _ _
  have hsum : ((r : ℝ) * Λ - σ) * (Fintype.card V : ℝ) ^ r ≤
      (r : ℝ) * G.edges.card := by
    calc
      ((r : ℝ) * Λ - σ) * (Fintype.card V : ℝ) ^ r =
          ∑ _v : V, ((r : ℝ) * Λ - σ) * (Fintype.card V : ℝ) ^ (r - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hpow]
        ring
      _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum (fun v _ => hmin v)
      _ = (r : ℝ) * G.edges.card := by
        rw [← Nat.cast_sum, G.sum_degrees, Nat.cast_mul]
  have hm := mul_le_mul_of_nonneg_right hσε
    (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) r)
  nlinarith

theorem goodVertices_eq_univ_of_minimumDegree (G : RGraph V r)
    (hn : 0 < Fintype.card V) {Λ σ δ : ℝ} (hσδ : σ < δ)
    (hmin : MinimumDegree G ((r : ℝ) * Λ - σ)) : goodVertices G Λ δ = Finset.univ := by
  classical
  have hzero : G.lowDegreeSet Λ δ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hlow := (Finset.mem_filter.mp hv).2
    have hhigh := hmin v
    have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    have hp := pow_pos hn' (r - 1)
    have hgap := mul_pos (sub_pos.mpr hσδ) hp
    nlinarith
  simp only [goodVertices, hzero, Finset.sdiff_empty]

/-- **Degree stability via the Ψ trick.** The two local structural inputs
are symmetrized stability and genuine one-vertex extendability. The exact
weighted bound supplies the low-degree deletion estimate. -/
theorem degreeStable_of_symmetrized_vertexExtendable (B C : GraphClass.{u} r)
    (hr : 2 ≤ r) (hB : HomClosed B) (hC : EmbeddingClosed C)
    {Λ : ℝ} (hΛ : 0 < Λ) (hbound : PolynomialBound B Λ)
    (hsym : ∃ εs : ℝ, 0 < εs ∧ ∃ Ns : ℕ, SymmetrizedStable B C Λ εs Ns)
    (hext : ∃ ζ : ℝ, 0 < ζ ∧ ∃ Nv : ℕ,
      VertexExtendable B C ((r : ℝ) * Λ - ζ) Nv) : DegreeStable B C Λ := by
  obtain ⟨εs, hεs, Ns, hsym⟩ := hsym
  obtain ⟨ζ, hζ, Nv, hext⟩ := hext
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let δ : ℝ := min (ζ / 8) (min (((r : ℝ) * Λ) / 8) (1 / 12))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδζ : δ ≤ ζ / 8 := min_le_left _ _
  have hδΛ : δ ≤ ((r : ℝ) * Λ) / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδone : δ ≤ 1 / 12 := (min_le_right _ _).trans (min_le_right _ _)
  have hd : 0 ≤ (r : ℝ) * Λ - 4 * δ := by nlinarith [mul_pos hr0 hΛ]
  have hext' : VertexExtendable B C ((r : ℝ) * Λ - 4 * δ) Nv :=
    hext.mono (by linarith)
  let η : ℝ := min εs (Density.lowDegreeTolerance r δ)
  have hη : 0 < η := lt_min hεs (Density.lowDegreeTolerance_pos r hδ)
  let ε : ℝ := min (δ / 2) ((r : ℝ) * η / 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hεη : ε ≤ (r : ℝ) * η := (min_le_right _ _).trans (by nlinarith [mul_pos hr0 hη])
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  let N := max Ns (max (2 * Nv) (k + 1))
  refine ⟨ε, hε, N, ?_⟩
  intro W _ _ G hG hN hmin
  have hNs : Ns ≤ Fintype.card W := (le_max_left _ _).trans hN
  have hNv : 2 * Nv ≤ Fintype.card W :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hkN : k + 1 ≤ Fintype.card W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hn : 0 < Fintype.card W := by omega
  have hscale : 1 ≤ δ * Fintype.card W := by
    have hk' : (k : ℝ) ≤ Fintype.card W := by exact_mod_cast (show k ≤ Fintype.card W by omega)
    have hmul := mul_le_mul_of_nonneg_left hk' hδ.le
    have hkg := (div_lt_iff₀ hδ).mp hk
    nlinarith
  have hnear := edge_near_of_minimumDegree G (by omega) hmin hεη
  have hgood := good_induced_of_near B C hr hB hC hbound hδ (by linarith) hd
    hsym hext' G hG hn hNs hNv hscale hnear
  rw [goodVertices_eq_univ_of_minimumDegree G hn hεδ hmin] at hgood
  exact hC G.into_full_induced hgood

end TuranUniversality.Stability
