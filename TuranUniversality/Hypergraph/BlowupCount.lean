module

public import TuranUniversality.Hypergraph.Blowup
public import TuranUniversality.Hypergraph.Polynomial

@[expose] public section

/-! # Exact edge counts and integer-weight polynomials of finite blowups -/

open scoped BigOperators

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {r : ℕ}

/-- An original edge together with one clone choice at each of its vertices. -/
abbrev EdgeChoices (G : RGraph V r) (sizes : V → ℕ) :=
  Σ e : G.edges, ∀ v : e.val, Fin (sizes v.val)

def cloneEdge (G : RGraph V r) (sizes : V → ℕ) (p : EdgeChoices G sizes) :
    Finset (BlowupVertex sizes) :=
  p.1.val.attach.image (fun v => ⟨v.val, p.2 v⟩)

omit [Fintype V] in
theorem cloneEdge_projection (G : RGraph V r) (sizes : V → ℕ) (p : EdgeChoices G sizes) :
    (G.cloneEdge sizes p).image Sigma.fst = p.1.val := by
  simp [cloneEdge, Finset.image_image, Function.comp_def]

theorem cloneEdge_mem (G : RGraph V r) (sizes : V → ℕ) (p : EdgeChoices G sizes) :
    G.cloneEdge sizes p ∈ (G.blowup sizes).edges := by
  apply (G.mem_blowup sizes _).mpr
  constructor
  · have hi : Function.Injective (fun v : p.1.val =>
        (⟨v.val, p.2 v⟩ : BlowupVertex sizes)) := by
      intro a b h
      exact Subtype.ext (congrArg Sigma.fst h)
    rw [cloneEdge, Finset.card_image_of_injective _ hi, Finset.card_attach]
    exact G.uniform _ p.1.property
  · rw [G.cloneEdge_projection sizes p]
    exact p.1.property

def edgeChoicesMap (G : RGraph V r) (sizes : V → ℕ) (p : EdgeChoices G sizes) :
    (G.blowup sizes).edges := ⟨G.cloneEdge sizes p, G.cloneEdge_mem sizes p⟩

theorem edgeChoicesMap_bijective (G : RGraph V r) (sizes : V → ℕ) :
    Function.Bijective (G.edgeChoicesMap sizes) := by
  classical
  constructor
  · intro p q hpq
    have heq : G.cloneEdge sizes p = G.cloneEdge sizes q := congrArg Subtype.val hpq
    have he : p.1 = q.1 := Subtype.ext (by
      rw [← G.cloneEdge_projection sizes p, ← G.cloneEdge_projection sizes q, heq])
    cases p with
    | mk e c =>
      cases q with
      | mk e' d =>
        dsimp only at he
        subst e'
        congr 1
        funext v
        have hm : (⟨v.val, c v⟩ : BlowupVertex sizes) ∈ G.cloneEdge sizes ⟨e, c⟩ :=
          Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, rfl⟩
        rw [heq] at hm
        obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hm
        have hwv : w = v := Subtype.ext (congrArg Sigma.fst hw)
        subst w
        exact (eq_of_heq (Sigma.mk.inj_iff.mp hw).2).symm
  · intro d
    let e : G.edges := ⟨d.val.image Sigma.fst, ((G.mem_blowup sizes _).mp d.property).2⟩
    have hex (v : e.val) : ∃ j : Fin (sizes v.val),
        (⟨v.val, j⟩ : BlowupVertex sizes) ∈ d.val := by
      obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp v.property
      rcases p with ⟨w, j⟩
      dsimp only at hpv
      subst w
      exact ⟨j, hp⟩
    let c (v : e.val) := Classical.choose (hex v)
    have hc (v : e.val) : (⟨v.val, c v⟩ : BlowupVertex sizes) ∈ d.val :=
      Classical.choose_spec (hex v)
    have hinj := (G.blowup_projection sizes).injOn_edge d.property
    refine ⟨⟨e, c⟩, ?_⟩
    apply Subtype.ext
    ext p
    constructor
    · intro hp
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
      exact hc v
    · intro hp
      let v : e.val := ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, hinj (hc v) hp rfl⟩

/-- Every original edge gives exactly the product of its clone class sizes
many blowup edges; the proof is an explicit finite bijection. -/
theorem blowup_edges_card (G : RGraph V r) (sizes : V → ℕ) :
    (G.blowup sizes).edges.card = ∑ e ∈ G.edges, ∏ v ∈ e, sizes v := by
  classical
  calc
    (G.blowup sizes).edges.card = Fintype.card (G.blowup sizes).edges :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (EdgeChoices G sizes) :=
      (Fintype.card_congr (Equiv.ofBijective (G.edgeChoicesMap sizes)
        (G.edgeChoicesMap_bijective sizes))).symm
    _ = ∑ e : G.edges, ∏ v : e.val, sizes v.val := by
      simp only [Fintype.card_sigma, Fintype.card_pi, Fintype.card_fin]
    _ = _ := by
      simp only [Finset.prod_coe_sort]
      exact Finset.sum_coe_sort G.edges (fun e : Finset V => ∏ v ∈ e, sizes v)

omit [DecidableEq V] in
theorem blowup_vertex_card (sizes : V → ℕ) :
    Fintype.card (BlowupVertex sizes) = ∑ v, sizes v := by
  simp [BlowupVertex, Fintype.card_sigma]

/-- Dividing integer clone counts by their total gives exactly the normalized
uniform polynomial of the blowup. No approximation of weights is needed. -/
theorem blowup_polynomial (G : RGraph V r) (sizes : V → ℕ) :
    (G.blowup sizes).edgePolynomial
      (fun _ => (Fintype.card (BlowupVertex sizes) : ℝ)⁻¹) =
    G.edgePolynomial (fun v => (sizes v : ℝ) / (∑ w, sizes w : ℕ)) := by
  classical
  rw [edgePolynomial_uniform, G.blowup_edges_card, blowup_vertex_card]
  unfold edgePolynomial
  simp only [Nat.cast_sum, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const]
  have h (e : Finset V) (he : e ∈ G.edges) :
      (∏ v ∈ e, (sizes v : ℝ)) / (∑ w, (sizes w : ℝ)) ^ e.card =
        (∏ v ∈ e, (sizes v : ℝ)) / (∑ w, (sizes w : ℝ)) ^ r := by rw [G.uniform e he]
  rw [Finset.sum_congr rfl h, ← Finset.sum_div]
  simp [div_eq_mul_inv]

end TuranUniversality.RGraph
