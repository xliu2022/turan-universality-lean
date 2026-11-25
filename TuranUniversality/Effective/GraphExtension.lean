module

public import TuranUniversality.Effective.GraphEncoding
public import TuranUniversality.Hypergraph.Extension

/-! # A primitive-recursive code for the private pair extension

The list algorithm reserves one vertex for every ordered pair.  The two
orientations give interchangeable private vertices, and the diagonal vertices
are isolated.  Its decoded graph has homomorphisms in both directions with the
unordered private-pair extension used by the graph-theoretic proof.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace TuranUniversality.Effective

open RGraph

def extensionOrder (n : ℕ) : ℕ := n + n * n

def tripleInRange (n : ℕ) (t : Triple) : Prop :=
  t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n

instance (n : ℕ) (t : Triple) : Decidable (tripleInRange n t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem tripleInRange_primrec : PrimrecRel tripleInRange :=
  ((Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).and
    ((Primrec.nat_lt.comp ((Primrec.fst.comp Primrec.snd).comp Primrec.snd) Primrec.fst).and
      (Primrec.nat_lt.comp ((Primrec.snd.comp Primrec.snd).comp Primrec.snd) Primrec.fst)))

abbrev pairExtensionCode (g : GraphCode) : GraphCode :=
  (extensionOrder g.1,
    g.2.filter (tripleInRange g.1) ++
      (cartesian (List.range g.1) (List.range g.1)).map
        (fun p => (p.1, p.2, g.1 + Nat.pair p.1 p.2)))

theorem pairExtensionCode_primrec : Primrec pairExtensionCode := by
  have horder : Primrec (fun g : GraphCode => extensionOrder g.1) :=
    Primrec.nat_add.comp Primrec.fst (Primrec.nat_mul.comp Primrec.fst Primrec.fst)
  have hcore : Primrec (fun g : GraphCode => g.2.filter (tripleInRange g.1)) :=
    (filter_primrec tripleInRange_primrec).comp Primrec.fst Primrec.snd
  have hpairs : Primrec (fun g : GraphCode => cartesian (List.range g.1) (List.range g.1)) :=
    cartesian_primrec.comp (Primrec.list_range.comp Primrec.fst)
      (Primrec.list_range.comp Primrec.fst)
  have hprivate : Primrec (fun g : GraphCode =>
      (cartesian (List.range g.1) (List.range g.1)).map
        (fun p => (p.1, p.2, g.1 + Nat.pair p.1 p.2))) :=
    Primrec.list_map hpairs
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.snd.comp Primrec.snd)
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst)
            (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
              (Primrec.snd.comp Primrec.snd))))).to₂
  exact Primrec.pair horder (Primrec.list_append.comp hcore hprivate)

theorem pair_lt_square {n a b : ℕ} (ha : a < n) (hb : b < n) : Nat.pair a b < n * n := by
  have hp := Nat.pair_lt_max_add_one_sq a b
  have hm : max a b + 1 ≤ n := by omega
  have hs := Nat.mul_self_le_mul_self hm
  nlinarith

def extensionCore (n : ℕ) (a : Fin n) : Fin (extensionOrder n) :=
  ⟨a, by unfold extensionOrder; have := a.isLt; omega⟩

def extensionPrivate (n : ℕ) (a b : Fin n) : Fin (extensionOrder n) :=
  ⟨n + Nat.pair a b, Nat.add_lt_add_left (pair_lt_square a.isLt b.isLt) n⟩

theorem extensionCore_injective (n : ℕ) : Function.Injective (extensionCore n) := by
  intro a b h
  have hv : (extensionCore n a).val = (extensionCore n b).val := congrArg Fin.val h
  exact Fin.ext hv

theorem extensionCore_ne_private (n : ℕ) (a b c : Fin n) :
    extensionCore n a ≠ extensionPrivate n b c := by
  intro h
  have hv := congrArg Fin.val h
  change a.val = n + Nat.pair b.val c.val at hv
  have := a.isLt
  omega

theorem extension_private_edge (g : GraphCode) (a b : Fin g.1) (hab : a ≠ b) :
    {extensionCore g.1 a, extensionCore g.1 b, extensionPrivate g.1 a b} ∈
      (decodeGraph (pairExtensionCode g)).edges := by
  rw [mem_decodeGraph]
  refine ⟨by simp [(extensionCore_injective g.1).ne hab,
    extensionCore_ne_private g.1 a a b, extensionCore_ne_private g.1 b a b], ?_⟩
  refine ⟨(a.val, b.val, g.1 + Nat.pair a.val b.val), ?_, ?_⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨(a.val, b.val),
      mem_cartesian.mpr ⟨List.mem_range.mpr a.isLt, List.mem_range.mpr b.isLt⟩, rfl⟩
  · simp [tripleSet, extensionCore, extensionPrivate]

theorem extension_core_hom (g : GraphCode) :
    (decodeGraph g).IsHom (decodeGraph (pairExtensionCode g)) (extensionCore g.1) := by
  intro e he
  obtain ⟨hc, t, ht, het⟩ := (mem_decodeGraph g e).mp he
  have hrange : tripleInRange g.1 t := by
    have h (a : ℕ) (ha : a ∈ tripleSet t) : a < g.1 := by
      rw [← het] at ha
      obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
      exact a'.isLt
    exact ⟨h _ (by simp [tripleSet]), h _ (by simp [tripleSet]), h _ (by simp [tripleSet])⟩
  rw [mem_decodeGraph]
  refine ⟨by rw [Finset.card_image_of_injective _ (extensionCore_injective _), hc], t, ?_, ?_⟩
  · exact List.mem_append_left _ (List.mem_filter.mpr ⟨ht, decide_eq_true hrange⟩)
  · simpa only [Finset.image_image, Function.comp_def, extensionCore] using het

theorem extension_edge_cases (g : GraphCode) (e : Finset (Fin (extensionOrder g.1)))
    (he : e ∈ (decodeGraph (pairExtensionCode g)).edges) :
    (∃ d ∈ (decodeGraph g).edges, e = d.image (extensionCore g.1)) ∨
      ∃ a b : Fin g.1, a ≠ b ∧
        e = {extensionCore g.1 a, extensionCore g.1 b, extensionPrivate g.1 a b} := by
  obtain ⟨hc, t, ht, het⟩ := (mem_decodeGraph (pairExtensionCode g) e).mp he
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨ht, hr⟩ := List.mem_filter.mp ht
    have hr := of_decide_eq_true hr
    let a : Fin g.1 := ⟨t.1, hr.1⟩
    let b : Fin g.1 := ⟨t.2.1, hr.2.1⟩
    let c : Fin g.1 := ⟨t.2.2, hr.2.2⟩
    have heq : e = ({a, b, c} : Finset (Fin g.1)).image (extensionCore g.1) := by
      apply Finset.image_injective Fin.val_injective
      simpa [a, b, c, tripleSet, extensionCore] using het
    left
    refine ⟨{a, b, c}, ?_, heq⟩
    rw [mem_decodeGraph]
    refine ⟨?_, t, ht, by simp [a, b, c, tripleSet]⟩
    rw [heq, Finset.card_image_of_injective _ (extensionCore_injective _)] at hc
    exact hc
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp ht
    have hr := mem_cartesian.mp hab
    let a' : Fin g.1 := ⟨a, List.mem_range.mp hr.1⟩
    let b' : Fin g.1 := ⟨b, List.mem_range.mp hr.2⟩
    have heq : e = {extensionCore g.1 a', extensionCore g.1 b', extensionPrivate g.1 a' b'} := by
      apply Finset.image_injective Fin.val_injective
      simpa [a', b', tripleSet, extensionCore, extensionPrivate] using het
    right
    refine ⟨a', b', ?_, heq⟩
    intro hequal
    rw [heq, hequal] at hc
    simp [extensionCore_ne_private g.1 b' b' b'] at hc

theorem extension_has_core {n : ℕ} (v : Fin (extensionOrder n)) : 0 < n := by
  by_contra hn
  have hn : n = 0 := by omega
  have hv := v.isLt
  simp [extensionOrder, hn] at hv

/-- Collapse the two orientations to the same private unordered pair. -/
def extensionCollapse (n : ℕ) (v : Fin (extensionOrder n)) : ExtensionVertex (Fin n) :=
  if hcore : v.val < n then .inl ⟨v.val, hcore⟩
  else if hp : (v.val - n).unpair.1 < n ∧ (v.val - n).unpair.2 < n ∧
      (v.val - n).unpair.1 ≠ (v.val - n).unpair.2 then
    .inr ⟨{⟨(v.val - n).unpair.1, hp.1⟩, ⟨(v.val - n).unpair.2, hp.2.1⟩},
      by simp [Fin.ext_iff, hp.2.2]⟩
  else .inl ⟨0, extension_has_core v⟩

@[simp] theorem extensionCollapse_core (n : ℕ) (a : Fin n) :
    extensionCollapse n (extensionCore n a) = Sum.inl a := by
  simp [extensionCollapse, extensionCore, a.isLt]

@[simp] theorem extensionCollapse_private (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    extensionCollapse n (extensionPrivate n a b) =
      Sum.inr (⟨{a, b}, by simp [hab]⟩ : VertexPair (Fin n)) := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp [extensionCollapse, extensionPrivate, a.isLt, b.isLt, hab']

theorem extensionCollapse_hom (g : GraphCode) :
    (decodeGraph (pairExtensionCode g)).IsHom (decodeGraph g).pairExtension
      (extensionCollapse g.1) := by
  intro e he
  rcases extension_edge_cases g e he with ⟨d, hd, rfl⟩ | ⟨a, b, hab, rfl⟩
  · simpa only [Finset.image_image, Function.comp_def, extensionCollapse_core] using
      (decodeGraph g).core_isHom d hd
  · have h := (decodeGraph g).privateEdge_mem (⟨{a, b}, by simp [hab]⟩ : VertexPair (Fin g.1))
    convert h using 1
    ext v
    simp [privateEdge, extensionCollapse_private g.1 a b hab,
      or_assoc, or_comm]

theorem extension_lift_exists (g : GraphCode) (p : VertexPair (Fin g.1)) :
    ∃ v : Fin (extensionOrder g.1),
      insert v (p.val.image (extensionCore g.1)) ∈ (decodeGraph (pairExtensionCode g)).edges := by
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp p.property
  refine ⟨extensionPrivate g.1 a b, ?_⟩
  convert extension_private_edge g a b hab using 1
  ext v
  simp [hp, or_assoc, or_comm]

/-- The reverse homomorphism chooses one orientation of each unordered pair. -/
noncomputable def extensionLift (g : GraphCode) :
    ExtensionVertex (Fin g.1) → Fin (extensionOrder g.1) :=
  Sum.elim (extensionCore g.1) (fun p => Classical.choose (extension_lift_exists g p))

theorem extensionLift_hom (g : GraphCode) :
    (decodeGraph g).pairExtension.IsHom (decodeGraph (pairExtensionCode g)) (extensionLift g) := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    simpa [extensionLift, Finset.image_image, Function.comp_def] using extension_core_hom g d hd
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    simpa [privateEdge, extensionLift, Finset.image_image, Function.comp_def] using
      Classical.choose_spec (extension_lift_exists g p)

/-- The executable graph compiler represents exactly the pair-extension
homomorphism class required by the singleton construction. -/
theorem pairExtensionCode_mutual_hom (g : GraphCode) :
    (∃ f, (decodeGraph (pairExtensionCode g)).IsHom (decodeGraph g).pairExtension f) ∧
      (∃ f, (decodeGraph g).pairExtension.IsHom (decodeGraph (pairExtensionCode g)) f) :=
  ⟨⟨extensionCollapse g.1, extensionCollapse_hom g⟩, ⟨extensionLift g, extensionLift_hom g⟩⟩

end TuranUniversality.Effective
