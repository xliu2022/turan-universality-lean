module

public import TuranUniversality.Effective.GraphProduct

@[expose] public section

/-! # Total list product algorithms and their categorical property -/

namespace TuranUniversality.Effective

set_option backward.isDefEq.respectTransparency false

def productStep (g : GraphCode) (acc : Option GraphCode) : Option GraphCode :=
  some (acc.elim g (binaryProductCode g))

def productOption (xs : List GraphCode) : Option GraphCode :=
  xs.foldr productStep none

/-- The empty list is assigned the empty graph. For every nonempty list,
this is a labeled categorical product, with repeated factors permitted. -/
def productCode (xs : List GraphCode) : GraphCode :=
  (productOption xs).getD (0, [])

theorem productStep_primrec : Primrec₂ productStep := by
  have hs : Primrec (fun p : GraphCode × Option GraphCode => p.2) := Primrec.snd
  have hf : Primrec (fun p : GraphCode × Option GraphCode => p.1) := Primrec.fst
  have hg : Primrec₂ (fun (p : GraphCode × Option GraphCode) h => binaryProductCode p.1 h) :=
    (binaryProductCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hc := Primrec.option_casesOn hs hf hg
  have hc' : Primrec (fun p : GraphCode × Option GraphCode =>
      p.2.elim p.1 (binaryProductCode p.1)) :=
    hc.of_eq (fun p => by rcases p with ⟨g, acc⟩; cases acc <;> rfl)
  exact (Primrec.option_some.comp hc').to₂

theorem productOption_primrec : Primrec productOption :=
  Primrec.list_foldr Primrec.id (Primrec.const none)
    (productStep_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem productCode_primrec : Primrec productCode :=
  Primrec.option_getD.comp productOption_primrec (Primrec.const (0, []))

theorem productOption_eq_some {xs : List GraphCode} (hxs : xs ≠ []) :
    productOption xs = some (productCode xs) := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons g xs => simp [productOption, productStep, productCode]

@[simp] theorem productCode_singleton (g : GraphCode) : productCode [g] = g := by
  simp [productCode, productOption, productStep]

theorem productCode_cons (g : GraphCode) {xs : List GraphCode} (hxs : xs ≠ []) :
    productCode (g :: xs) = binaryProductCode g (productCode xs) := by
  change (productStep g (productOption xs)).getD (0, []) = _
  rw [productOption_eq_some hxs]
  rfl

theorem productCode_projection (xs : List GraphCode) (g : GraphCode) (hg : g ∈ xs) :
    ∃ f, (decodeGraph (productCode xs)).IsHom (decodeGraph g) f := by
  induction xs with
  | nil => simp at hg
  | cons a xs ih =>
      by_cases hxs : xs = []
      · subst xs
        have hga : g = a := by simpa using hg
        subst g
        rw [productCode_singleton]
        exact ⟨id, RGraph.isHom_id _⟩
      · rw [productCode_cons a hxs]
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨_, binaryProductCode_left _ _⟩
        · obtain ⟨f, hf⟩ := ih hg
          exact ⟨_, hf.comp (binaryProductCode_right _ _)⟩

theorem productCode_lift {V : Type*} [DecidableEq V]
    (K : RGraph V 3) (xs : List GraphCode) (hxs : xs ≠ [])
    (hfactors : ∀ g ∈ xs, ∃ f, K.IsHom (decodeGraph g) f) :
    ∃ f, K.IsHom (decodeGraph (productCode xs)) f := by
  induction xs with
  | nil => exact False.elim (hxs rfl)
  | cons g xs ih =>
      by_cases ht : xs = []
      · subst xs
        rw [productCode_singleton]
        exact hfactors g (by simp)
      · rw [productCode_cons g ht]
        obtain ⟨f, hf⟩ := hfactors g (by simp)
        obtain ⟨j, hj⟩ := ih ht (fun h hh => hfactors h (List.mem_cons_of_mem _ hh))
        exact ⟨_, binaryProductCode_lift K g (productCode xs) f j hf hj⟩

theorem productCode_hom_iff {V : Type*} [DecidableEq V]
    (K : RGraph V 3) (xs : List GraphCode) (hxs : xs ≠ []) :
    (∃ f, K.IsHom (decodeGraph (productCode xs)) f) ↔
      ∀ g ∈ xs, ∃ f, K.IsHom (decodeGraph g) f := by
  constructor
  · rintro ⟨f, hf⟩ g hg
    obtain ⟨j, hj⟩ := productCode_projection xs g hg
    exact ⟨_, hj.comp hf⟩
  · exact productCode_lift K xs hxs

end TuranUniversality.Effective

namespace TuranUniversality.RGraph

universe u v w

theorem product_lift {I : Type u} {V : I → Type v} {W : Type w}
    [Fintype I] [Nonempty I] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    [DecidableEq W] (G : ∀ i, RGraph (V i) 3) (K : RGraph W 3)
    (f : ∀ i, W → V i) (hf : ∀ i, K.IsHom (G i) (f i)) :
    K.IsHom (product G) (fun w i => f i w) := by
  classical
  apply isHom_of_triples
  intro a b c he
  apply Selector.triple_product_mem
  intro i
  simpa using hf i _ he

end TuranUniversality.RGraph
