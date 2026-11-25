module

public import TuranUniversality.Structural.ReadbackParameters
public import TuranUniversality.Density.WeightedHom
public import TuranUniversality.Weighted.Symmetric

@[expose] public section

/-! # The exact weighted readback factorization

The equality is obtained by reindexing the sum over actual ordinary
homomorphisms through the verified parameter bijection. The five neutral
assignments give `5! e_5`, and the root assignments give the actual root
group's order. No probability hypothesis is needed for this polynomial
identity.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Readback

open Cube Support TripleClasses Density

variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable {B : Finset (FiniteGraph 3)}

def rootProduct {b t : ℕ} (x : Compiled.Vertex b t V → ℝ) : ℝ :=
  (∏ i : Fin t, x (.inl i)) * ∏ v : Support.Vertex b, x (.inr (.inl v))

theorem parameterMap_weight [Fintype U] {b t : ℕ} (a : RootActions.Parameters b t)
    (d : Fin 5 → V) (g : U → V) (x : Compiled.Vertex b t V → ℝ) :
    productWeight x (parameterMap a d g) =
      rootProduct x * productWeight (fun v => x (dataVertex v)) d *
        productWeight (fun v => x (dataVertex v)) g := by
  have hs : (∏ i : Fin t, x (.inl (a.2.1 i))) = ∏ i : Fin t, x (.inl i) :=
    Fintype.prod_equiv a.2.1 _ _ (fun _ => rfl)
  have hb : (∏ v : Support.Vertex b, x (.inr (.inl
      (blockMap (RootActions.phasePermutation b a.1)
        (fun i => RootActions.localPermutation a.1 (a.2.2 i)) v)))) =
      ∏ v : Support.Vertex b, x (.inr (.inl v)) :=
    Fintype.prod_equiv (RootActions.blockEquiv (RootActions.phasePermutation b a.1)
      (fun i => RootActions.localPermutation a.1 (a.2.2 i))) _ _ (fun _ => rfl)
  rw [parameterMap_eq_extend]
  unfold productWeight
  simp only [Fintype.prod_sum_type, extend, Sum.elim_inl, Sum.elim_inr, Frame.vertexMap]
  rw [hs, hb]
  unfold rootProduct dataVertex
  ring

theorem weighted_readback_raw [Fintype U] [Fintype V]
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (F : RGraph U 3) (hno : Uniformity.NoIsolates F) (O : LegalObject B V) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (x : Compiled.Vertex (CodePools.blockCount q) t V → ℝ) :
    (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).weightedHomDensity
      (Compiled.graph t (CodePools.pool p q hpq) O.records) x =
      (2 * 10 ^ CodePools.blockCount q * t.factorial : ℕ) * rootProduct x *
        (∑ d : NeutralAssignment O, productWeight (fun v => x (dataVertex v)) d.val) *
          F.weightedHomDensity (O.inner phase) (fun v => x (dataVertex v)) := by
  classical
  rw [RGraph.weightedHomDensity_eq_sum_homs]
  calc
    (∑ f : TestHom p q hpq t F O phase Z hZ, productWeight x f.val) =
        ∑ a : Parameters (CodePools.blockCount q) t F O phase,
          productWeight x (parameterMap a.1 a.2.1.val a.2.2.val) := by
      symm
      apply Fintype.sum_equiv (Equiv.ofBijective (intoHoms p q hpq t F O phase Z hZ)
        (intoHoms_bijective p q hpq hq t F hno O phase Z hZ))
      intro a
      rfl
    _ = ∑ a : Parameters (CodePools.blockCount q) t F O phase,
        rootProduct x * productWeight (fun v => x (dataVertex v)) a.2.1.val *
          productWeight (fun v => x (dataVertex v)) a.2.2.val := by
      apply Finset.sum_congr rfl
      intro a _
      exact parameterMap_weight _ _ _ _
    _ = (Fintype.card (RootActions.Parameters (CodePools.blockCount q) t) : ℝ) *
        rootProduct x *
        (∑ d : NeutralAssignment O, productWeight (fun v => x (dataVertex v)) d.val) *
        (∑ g : InnerHom F O phase, productWeight (fun v => x (dataVertex v)) g.val) := by
      simp only [Parameters, Fintype.sum_prod_type]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      simp only [RootActions.Parameters, Fintype.card_prod, Nat.cast_mul]
      ring
    _ = _ := by
      rw [RootActions.parameters_card, RGraph.weightedHomDensity_eq_sum_homs]

def neutralSet [Fintype V] (O : LegalObject B V) : Finset V := Finset.univ \ O.active

def neutralClique [Fintype V] (O : LegalObject B V) : RGraph V 5 where
  edges := (neutralSet O).powersetCard 5
  uniform e he := (Finset.mem_powersetCard.mp he).2

theorem neutralClique_hom_iff [Fintype V] (O : LegalObject B V) (d : Fin 5 → V) :
    (RGraph.oneEdge 5).IsHom (neutralClique O) d ↔
      Function.Injective d ∧ ∀ i, d i ∉ O.active := by
  rw [(neutralClique O).oneEdge_isHom]
  change Finset.univ.image d ∈ (neutralSet O).powersetCard 5 ↔ _
  rw [Finset.mem_powersetCard]
  constructor
  · rintro ⟨hs, hc⟩
    have hi : Function.Injective d := by
      have h := Finset.card_image_iff.mp (show (Finset.univ.image d).card = Finset.univ.card by
        simpa only [Finset.card_univ, Fintype.card_fin] using hc)
      exact fun i j hij => h (Finset.mem_univ _) (Finset.mem_univ _) hij
    refine ⟨hi, fun i => ?_⟩
    have hm := hs (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact (Finset.mem_sdiff.mp hm).2
  · rintro ⟨hd, hn⟩
    refine ⟨?_, by simp [Finset.card_image_of_injective _ hd]⟩
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn i⟩

theorem neutralAssignment_weight [Fintype V] (O : LegalObject B V) (x : V → ℝ) :
    (∑ d : NeutralAssignment O, productWeight x d.val) =
      (Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O) x 5 := by
  classical
  calc
    _ = ∑ d : {d : Fin 5 → V // (RGraph.oneEdge 5).IsHom (neutralClique O) d},
        productWeight x d.val := by
      apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun d => (neutralClique_hom_iff O d).symm))
      intro d
      rfl
    _ = (RGraph.oneEdge 5).weightedHomDensity (neutralClique O) x :=
      (RGraph.weightedHomDensity_eq_sum_homs _ _ _).symm
    _ = _ := RGraph.weightedHomDensity_oneEdge _ _

/-- The unnormalized form of equation `readback`, with the actual root
group and the exact fifth elementary symmetric polynomial of neutral weights. -/
theorem weighted_readback [Fintype U] [Fintype V]
    (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) (t : ℕ)
    (F : RGraph U 3) (hno : Uniformity.NoIsolates F) (O : LegalObject B V) (phase : Bool)
    (Z : Finset (Support.Vertex (CodePools.blockCount q)))
    (hZ : Z ∈ (poolGraph (CodePools.pool p q hpq (.inr phase))).edges)
    (x : Compiled.Vertex (CodePools.blockCount q) t V → ℝ) :
    (test t (CodePools.pool p q hpq CodePools.neutralLabel) Z
      ((poolGraph _).uniform Z hZ) F).weightedHomDensity
      (Compiled.graph t (CodePools.pool p q hpq) O.records) x =
      (Fintype.card (RootActions.group (CodePools.blockCount q) t
        (CodePools.pool p q hpq CodePools.neutralLabel)) : ℝ) * rootProduct x *
        ((Nat.factorial 5 : ℝ) * Weighted.elementary (neutralSet O)
          (fun v => x (dataVertex v)) 5) *
          F.weightedHomDensity (O.inner phase) (fun v => x (dataVertex v)) := by
  rw [weighted_readback_raw p q hpq hq t F hno O phase Z hZ,
    neutralAssignment_weight, RootActions.group_card p q hpq hq t]

end TuranUniversality.Structural.Readback
