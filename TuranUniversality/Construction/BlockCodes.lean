module

public import TuranUniversality.Weighted.Codes

/-! # Explicit block codes from cyclic bipartite matchings

Each block has two equal sides. Translation on the cyclic group on either side
gives edge-disjoint perfect matchings. Blocks have fewer than `4*C` vertices;
the selector uses `8*C` profiles, leaving ample room for Hall's transversal.
-/

@[expose] public section

namespace TuranUniversality.Construction

open TuranUniversality.Weighted
open scoped BigOperators

universe u v w

section Bipartite

variable {A : Type u} [Fintype A] [DecidableEq A]

def bipartitePair (σ : A ≃ A) (a : A) : Finset (A ⊕ A) :=
  {Sum.inl a, Sum.inr (σ a)}

@[simp] theorem bipartitePair_left (σ : A ≃ A) (a : A) :
    (bipartitePair σ a).toLeft = {a} := by
  ext x
  simp [bipartitePair]

@[simp] theorem bipartitePair_right (σ : A ≃ A) (a : A) :
    (bipartitePair σ a).toRight = {σ a} := by
  ext x
  simp [bipartitePair]

theorem bipartitePair_eq_iff (σ τ : A ≃ A) (a b : A) :
    bipartitePair σ a = bipartitePair τ b ↔ a = b ∧ σ a = τ b := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg Finset.toLeft h,
      by simpa using congrArg Finset.toRight h⟩
  · rintro ⟨rfl, h⟩
    simp [bipartitePair, h]

def bipartitePairing (σ : A ≃ A) : PerfectPairing (Finset.univ : Finset (A ⊕ A)) where
  pairs := Finset.univ.image (bipartitePair σ)
  pair_card := by
    intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    simp [bipartitePair]
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hab : a = b := by
      simp only [id, bipartitePair, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Sum.inl.inj (hx.symm.trans hy)
      · have h := hx.symm.trans hy; cases h
      · have h := hx.symm.trans hy; cases h
      · exact σ.injective (Sum.inr.inj (hx.symm.trans hy))
    exact hpq (congrArg (bipartitePair σ) hab)
  cover := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    cases x with
    | inl a =>
      exact Finset.mem_biUnion.mpr ⟨bipartitePair σ a,
        Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, by simp [bipartitePair]⟩
    | inr a =>
      exact Finset.mem_biUnion.mpr ⟨bipartitePair σ (σ.symm a),
        Finset.mem_image.mpr ⟨σ.symm a, Finset.mem_univ _, rfl⟩, by simp [bipartitePair]⟩

theorem bipartitePairing_disjoint (σ τ : A ≃ A) (h : ∀ a, σ a ≠ τ a) :
    Disjoint (bipartitePairing σ).pairs (bipartitePairing τ).pairs := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, _, heq⟩ := Finset.mem_image.mp hq
  obtain ⟨rfl, hab⟩ := (bipartitePair_eq_iff τ σ b a).mp heq
  exact h b hab.symm

end Bipartite

section Blocks

variable {B : Type u} {Code : Type v} [Fintype B] [DecidableEq B]
variable (n : B → ℕ) [∀ b, NeZero (n b)]

abbrev BlockSide := (b : B) × Fin (n b)
abbrev BlockRoots := BlockSide n ⊕ BlockSide n

def blockLabel : BlockRoots n → B := Sum.elim Sigma.fst Sigma.fst

def blockShift (code : (b : B) → Code ↪ Fin (n b)) (c : Code) : BlockSide n ≃ BlockSide n :=
  Equiv.sigmaCongrRight fun b => Equiv.addRight (code b c)

def blockCodeSystem (code : (b : B) → Code ↪ Fin (n b)) : CodeSystem (BlockRoots n) Code where
  missing c := bipartitePairing (blockShift n code c)
  disjoint := by
    intro c d hcd
    apply bipartitePairing_disjoint
    rintro ⟨b, a⟩ heq
    have h : a + code b c = a + code b d := by
      simpa [blockShift] using heq
    exact hcd ((code b).injective (add_left_cancel h))

theorem blockCodeSystem_inside (code : (b : B) → Code ↪ Fin (n b))
    (c : Code) (p : Finset (BlockRoots n)) (hp : p ∈ ((blockCodeSystem n code).missing c).pairs)
    {x y : BlockRoots n} (hx : x ∈ p) (hy : y ∈ p) :
    blockLabel n x = blockLabel n y := by
  obtain ⟨⟨b, a⟩, _, rfl⟩ := Finset.mem_image.mp hp
  simp only [bipartitePair, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl

theorem card_blockRoots : Fintype.card (BlockRoots n) = 2 * ∑ b, n b := by
  simp [BlockRoots, BlockSide, Fintype.card_sum, Fintype.card_sigma, two_mul]

def blockFiberEquiv (b : B) : {x : BlockRoots n // blockLabel n x = b} ≃
    (Fin (n b) ⊕ Fin (n b)) where
  toFun x := match x with
    | ⟨Sum.inl ⟨b', a⟩, h⟩ => Sum.inl (h ▸ a)
    | ⟨Sum.inr ⟨b', a⟩, h⟩ => Sum.inr (h ▸ a)
  invFun x := match x with
    | Sum.inl a => ⟨Sum.inl ⟨b, a⟩, rfl⟩
    | Sum.inr a => ⟨Sum.inr ⟨b, a⟩, rfl⟩
  left_inv := by
    rintro ⟨x, h⟩
    cases x with
    | inl x => cases x; dsimp [blockLabel] at h; subst h; rfl
    | inr x => cases x; dsimp [blockLabel] at h; subst h; rfl
  right_inv := by intro x; cases x <;> rfl

theorem blockFiber_card (b : B) :
    (Finset.univ.filter fun x : BlockRoots n => blockLabel n x = b).card = 2 * n b := by
  classical
  rw [← Fintype.card_subtype]
  simpa [Fintype.card_sum, two_mul] using Fintype.card_congr (blockFiberEquiv n b)

end Blocks

/-- A finite, explicitly bounded partition of `q` roots into bipartite blocks. -/
structure BlockParameters (C q : ℕ) where
  blocks : ℕ
  half : Fin (blocks + 1) → ℕ
  lower : ∀ b, C ≤ half b
  upper : ∀ b, half b < 2 * C
  total : 2 * ∑ b, half b = q

def makeBlockParameters (C q : ℕ) (hC : 0 < C) (hq : 2 * C ≤ q)
    (heven : 2 ∣ q) : BlockParameters C q where
  blocks := q / 2 / C - 1
  half := Fin.cases (C + q / 2 % C) (fun _ => C)
  lower := by
    intro b
    refine Fin.cases ?_ (fun _ => ?_) b
    · simp
    · simp
  upper := by
    intro b
    have hr := Nat.mod_lt (q / 2) hC
    refine Fin.cases ?_ (fun _ => ?_) b
    · simp; omega
    · simp; omega
  total := by
    have hhalf : C ≤ q / 2 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hquot : 1 ≤ q / 2 / C := (Nat.le_div_iff_mul_le hC).mpr (by simpa)
    have hdiv : 2 * (q / 2) = q := Nat.mul_div_cancel' heven
    have hmod := Nat.mod_add_div (q / 2) C
    simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hqeq : q / 2 / C = (q / 2 / C - 1) + 1 := by omega
    rw [hqeq, Nat.mul_add, Nat.mul_one] at hmod
    nlinarith

namespace BlockParameters

variable {C q : ℕ} (P : BlockParameters C q) [NeZero C]

instance half_neZero (b : Fin (P.blocks + 1)) : NeZero (P.half b) :=
  ⟨Nat.ne_of_gt ((NeZero.pos C).trans_le (P.lower b))⟩

def codes : CodeSystem (BlockRoots P.half) (Fin C) :=
  blockCodeSystem P.half fun b => Fin.castLEEmb (P.lower b)

theorem roots_card : Fintype.card (BlockRoots P.half) = q :=
  (card_blockRoots P.half).trans P.total

theorem block_size (b : Fin (P.blocks + 1)) :
    (Finset.univ.filter fun x : BlockRoots P.half => blockLabel P.half x = b).card < 4 * C := by
  rw [blockFiber_card]
  have := P.upper b
  omega

theorem pair_inside (c : Fin C) (p : Finset (BlockRoots P.half))
    (hp : p ∈ (P.codes.missing c).pairs)
    {x y : BlockRoots P.half} (hx : x ∈ p) (hy : y ∈ p) :
    blockLabel P.half x = blockLabel P.half y :=
  blockCodeSystem_inside P.half _ c p hp hx hy

end BlockParameters

end TuranUniversality.Construction
