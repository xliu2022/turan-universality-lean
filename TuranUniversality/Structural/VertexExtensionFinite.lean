module

public import TuranUniversality.Structural.VertexRoleWitness
public import TuranUniversality.Structural.CommonFrameCondition
public import TuranUniversality.Structural.CanonicalRestriction

@[expose] public section

/-! # Finite vertex extension from actual common replacement frames

The local obstruction uses the exact Section 9 cutoff. The hypotheses
refer to ordinary edges and actual frame homomorphisms, with no assumed
stability conclusion. Every failed role is forced simultaneously inside
one small induced subgraph of the original graph.
-/

open scoped BigOperators

namespace TuranUniversality.Structural.Roles

open Rooted

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem vertex_witness_order_bound (r M R : ℕ) (hr : 4 ≤ r) (hR : 2 ≤ R) :
    r * (M + 1) * (r * R - 1) + (M + 5) + 1 ≤ r ^ 2 * (M + 1) * R + 2 := by
  have hpos : 1 ≤ r * R := by nlinarith
  have heq : r * R - 1 + 1 = r * R := Nat.sub_add_cancel hpos
  have hmul : r * (M + 1) * (r * R - 1) + r * (M + 1) =
      r ^ 2 * (M + 1) * R := by
    calc
      _ = r * (M + 1) * (r * R - 1 + 1) := by ring
      _ = _ := by rw [heq]; ring
  have hsmall : M + 4 ≤ r * (M + 1) := by nlinarith
  omega

theorem canonical_of_replacement_frames
    (F : Finset (FiniteGraph 3)) (p q : ℕ) (hpq : p ≤ q) (hq : 0 < q) {t : ℕ}
    (G G₀ : RGraph V (t + (3 * CodePools.blockCount q + 4)))
    (v : V) (ρ : V → Option (Roots (CodePools.blockCount q) t))
    (hG₀ : G₀.edges = G.edges.filter (fun e => v ∉ e))
    (hρ : Admissible (homomorphicClosure F) (CodePools.pool p q hpq) G₀ ρ)
    (hfree : familyFree (Ordinary.forbidden F (CodePools.pool p q hpq) t) G)
    (hinc : ∀ w : V, w ≠ v → ∃ e ∈ G₀.edges, w ∈ e)
    (hframe : ∀ S : Finset V, v ∉ S → S.card ≤
      (t + (3 * CodePools.blockCount q + 4)) * (t + 5 * CodePools.blockCount q + 1) *
        ((t + (3 * CodePools.blockCount q + 4)) *
          Ordinary.roleWitnessEdges (homomorphicClosure F) - 1) →
      HasReplacementFrame p q hpq G₀ ρ S) :
    Canonical (homomorphicClosure F) (CodePools.pool p q hpq) G := by
  classical
  let b := CodePools.blockCount q
  let Ω := CodePools.pool p q hpq
  let B := homomorphicClosure F
  let r := t + (3 * b + 4)
  let M := t + 5 * b
  let R := Ordinary.roleWitnessEdges B
  have hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k) :=
    fun _ _ h => CodePools.pools_disjoint p q hpq h
  have h₀sub : G₀.edges ⊆ G.edges := by
    intro e he
    rw [hG₀] at he
    exact (Finset.mem_filter.mp he).1
  have h₀avoid : ∀ e ∈ G₀.edges, v ∉ e := by
    intro e he
    rw [hG₀] at he
    exact (Finset.mem_filter.mp he).2
  by_contra hbad
  obtain ⟨E, S₀, hvS₀, hS₀card, hE, hfail⟩ :=
    all_roles_witness B Ω hdis G G₀ v ρ hG₀ hρ hbad
  have hchoose (w : S₀) : ∃ e ∈ G₀.edges, w.val ∈ e :=
    hinc w (fun h => hvS₀ (h ▸ w.property))
  choose e he hw using hchoose
  let S : Finset V := Finset.univ.biUnion e
  have heS (w : S₀) : e w ⊆ S :=
    fun z hz => Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, hz⟩
  have hS₀S : S₀ ⊆ S := fun w hw' => heS ⟨w, hw'⟩ (hw ⟨w, hw'⟩)
  have hvS : v ∉ S := by
    intro hv
    obtain ⟨w, _, hve⟩ := Finset.mem_biUnion.mp hv
    exact h₀avoid _ (he w) hve
  have hScard : S.card ≤ r * (M + 1) * (r * R - 1) := by
    calc
      S.card ≤ ∑ w : S₀, (e w).card := Finset.card_biUnion_le
      _ = S₀.card * r := by
        simp_rw [G₀.uniform _ (he _)]
        simp [r, b]
      _ ≤ ((M + 1) * (r * R - 1)) * r := Nat.mul_le_mul_right r hS₀card
      _ = _ := by ring
  obtain ⟨f, hf, hrepl⟩ := hframe S hvS hScard
  let U : Finset V := Finset.univ.image f
  let T : Finset V := insert v (S ∪ U)
  have hST : S ⊆ T := fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
  have hfT (u) : f u ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨u, Finset.mem_univ _, rfl⟩))
  have hTcard : T.card ≤ Ordinary.orderCutoff F Ω t := by
    have hUcard : U.card ≤ M + 5 := by
      calc
        U.card ≤ Fintype.card (Compiled.Vertex b t (Fin 5)) :=
          (Finset.card_image_le).trans_eq (Finset.card_univ)
        _ = M + 5 := by
          simp [Compiled.Vertex, Support.Vertex, M, Nat.mul_comm, Nat.add_assoc]
    have hbound := vertex_witness_order_bound r M R (by dsimp [r]; omega)
      (le_max_left 2 _)
    have hcut : r ^ 2 * (M + 1) * R + 2 ≤ Ordinary.orderCutoff F Ω t :=
      le_max_right _ _
    apply le_trans (b := r ^ 2 * (M + 1) * R + 2) _ hcut
    calc
      T.card ≤ (S ∪ U).card + 1 := Finset.card_insert_le _ _
      _ ≤ (S.card + U.card) + 1 := Nat.add_le_add_right (Finset.card_union_le _ _) 1
      _ ≤ (r * (M + 1) * (r * R - 1) + (M + 5)) + 1 := by omega
      _ ≤ _ := hbound
  let H := G.within T
  have hH : Canonical B Ω H := Ordinary.small_within_canonical F Ω G hfree T
    ⟨v, Finset.mem_insert_self _ _⟩ hTcard
  have h₀hom : G₀.IsHom G id := by
    intro d hd
    simpa using h₀sub hd
  have hfG : (Frame.graph b t (Ω CodePools.neutralLabel)).IsHom G f := by
    simpa only [Function.id_comp] using h₀hom.comp hf
  have hfH : (Frame.graph b t (Ω CodePools.neutralLabel)).IsHom H f := hfG.within T hfT
  have hreplH : HasReplacementFrame p q hpq H ρ S := by
    refine ⟨f, hfH, ?_⟩
    intro y hy j hj
    have hh : (Frame.graph b t (Ω CodePools.neutralLabel)).IsHom G
        (Function.update f (rootVertex (Fin 5) j) y) := by
      simpa only [Function.id_comp] using h₀hom.comp (hrepl y hy j hj)
    apply hh.within T
    intro u
    by_cases hu : u = rootVertex (Fin 5) j
    · subst u
      simpa using hST hy
    · simpa [Function.update_of_ne hu] using hfT u
  obtain ⟨σ, R', hR', hσ⟩ := hH
  have hσadm : Admissible B Ω H σ := admissible_of_records B Ω H σ R' hR' hσ
  obtain ⟨α, hα, hroots⟩ := hreplH.roles p q hpq hq R' hσ
  have heH (w : S₀) : e w ∈ H.edges :=
    (G.mem_within T _).mpr ⟨h₀sub (he w), (heS w).trans hST⟩
  have hroles : ∀ w ∈ S₀, σ w = (ρ w).map α := by
    intro w hw'
    cases hrw : ρ w with
    | some j => simpa only [hrw, Option.map_some] using hroots w (hS₀S hw') j hrw
    | none =>
      have hd := data_role_forced Ω ρ σ (e ⟨w, hw'⟩)
        (hρ.1 _ (he ⟨w, hw'⟩)) (hσadm.1 _ (heH ⟨w, hw'⟩))
        (fun z hz j hj => ⟨α j, hroots z (heS ⟨w, hw'⟩ hz) j hj⟩)
        w (hw ⟨w, hw'⟩) hrw
      simpa only [hrw, Option.map_none] using hd
  have hαinv : ∀ R : RecordSystem V, (Compiled.graph t Ω R).IsHom
      (Compiled.graph t Ω R) (liftRoot α.symm) := by
    intro R
    rw [liftRoot_symm]
    exact perm_hom_inverse _ _ (hα R)
  let σ' := renameRoles α.symm σ
  have hσ'adm : Admissible B Ω H σ' :=
    admissible_rename B Ω hdis α.symm hαinv H σ hσadm
  have hagree : ∀ w ∈ S₀, σ' w = ρ w := by
    intro w hw'
    dsimp [σ', renameRoles]
    rw [hroles w hw']
    cases ρ w <;> simp
  let a := σ' v
  have hEH : E a ⊆ H.edges := by
    intro d hd
    apply (G.mem_within T _).mpr
    refine ⟨(hE a).1 hd, ?_⟩
    intro w hw'
    rcases Finset.mem_insert.mp ((hE a).2.2 d hd hw') with rfl | hmem
    · exact Finset.mem_insert_self _ _
    · exact hST (hS₀S hmem)
  apply hfail a H σ' hEH _ hσ'adm
  intro d hd w hw'
  rcases Finset.mem_insert.mp ((hE a).2.2 d hd hw') with rfl | hmem
  · simp [a]
  · rw [Function.update_of_ne (fun (h : w = v) => hvS₀ (h ▸ hmem))]
    exact hagree w hmem

end TuranUniversality.Structural.Roles
