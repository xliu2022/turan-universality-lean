module

public import TuranUniversality.Effective.UniformPrimrec
public import TuranUniversality.Hypergraph.Blowup
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # Explicit numeric projections for mixed clone classes

Core vertices have `n` clones and data vertices have three clones. Their
numbering is an explicit equivalence, not a choice of a finite labeling.
-/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

/-- Keep precisely the rows whose image under a finite numeric table is an
edge of the given code. -/
def numericPullback (r n : ℕ) (g : Code) (xs : List ℕ) : Code :=
  (n, (allRows r n).filter fun w => Edge r g (imageRow xs w))

theorem numericPullback_primrec :
    Primrec (fun p : ℕ × ℕ × Code × List ℕ => numericPullback p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : ℕ × ℕ × Code × List ℕ => p.1) := Primrec.fst
  have hn : Primrec (fun p : ℕ × ℕ × Code × List ℕ => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun p : ℕ × ℕ × Code × List ℕ => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec (fun p : ℕ × ℕ × Code × List ℕ => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp : PrimrecRel (fun (p : ℕ × ℕ × Code × List ℕ) (w : List ℕ) =>
      Edge p.1 p.2.2.1 (imageRow p.2.2.2 w)) :=
    edge_primrec.comp ((hr.pair hg).comp Primrec.fst)
      (imageRow_primrec.comp (hx.comp Primrec.fst) Primrec.snd)
  exact hn.pair ((filter_primrec hp).comp Primrec.id (allRows_primrec.comp hr hn))

theorem mem_decode_numericPullback (r n : ℕ) (g : Code) (xs : List ℕ)
    (f : Fin n → Fin g.1) (hf : ∀ v, (f v).val = xs.getD v.val 0)
    (e : Finset (Fin n)) :
    e ∈ (decode r (numericPullback r n g xs)).edges ↔
      e.card = r ∧ e.image f ∈ (decode r g).edges := by
  have himage (w : List ℕ) (he : e.image Fin.val = w.toFinset) :
      (e.image f).image Fin.val = (imageRow xs w).toFinset := by
    rw [imageRow, list_map_toFinset, ← he, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro a _
    exact hf a
  rw [mem_decode]
  constructor
  · rintro ⟨hc, w, hw, hlen, he⟩
    have hw' : Edge r g (imageRow xs w) := by
      exact of_decide_eq_true (List.mem_filter.mp hw).2
    exact ⟨hc, (edge_iff_of_image r g _ _ (by simpa [imageRow] using hlen)
      (himage w he)).mp hw'⟩
  · rintro ⟨hc, he⟩
    let w := e.toList.map Fin.val
    have hlen : w.length = r := by simp [w, hc]
    have hwset : e.image Fin.val = w.toFinset := by
      simp [w, list_map_toFinset]
    have hrows : w ∈ allRows r n := by
      apply (mem_allRows r n w).mpr
      refine ⟨hlen, ?_⟩
      intro a ha
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
      exact v.isLt
    refine ⟨hc, w, List.mem_filter.mpr ⟨hrows, ?_⟩, hlen, hwset⟩
    apply decide_eq_true
    exact (edge_iff_of_image r g _ _ (by simpa [imageRow] using hlen)
      (himage w hwset)).mpr he

def mixedOrder (s n : ℕ) : ℕ := s * n + n * 3

def mixedSizes (s n : ℕ) : Fin s ⊕ Fin n → ℕ :=
  Sum.elim (fun _ => n) (fun _ => 3)

def mixedSplit (s n : ℕ) : RGraph.BlowupVertex (mixedSizes s n) ≃
    (Fin s × Fin n) ⊕ (Fin n × Fin 3) where
  toFun v := match v with
    | ⟨Sum.inl i, j⟩ => Sum.inl (i, j)
    | ⟨Sum.inr i, j⟩ => Sum.inr (i, j)
  invFun v := match v with
    | Sum.inl (i, j) => ⟨Sum.inl i, j⟩
    | Sum.inr (i, j) => ⟨Sum.inr i, j⟩
  left_inv v := by rcases v with ⟨i | i, j⟩ <;> rfl
  right_inv v := by rcases v with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl

def mixedEquiv (s n : ℕ) : RGraph.BlowupVertex (mixedSizes s n) ≃ Fin (mixedOrder s n) :=
  (mixedSplit s n).trans ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)

def mixedProjection (s n k : ℕ) : ℕ :=
  if k < s * n then k / n else s + (k - s * n) / 3

theorem mixedProjection_equiv (s n : ℕ) (v : RGraph.BlowupVertex (mixedSizes s n)) :
    mixedProjection s n (mixedEquiv s n v).val = (finSumFinEquiv v.1).val := by
  rcases v with ⟨i | i, j⟩
  · have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    have hj : j.val < n := j.isLt
    have hb : j.val + n * i.val < s * n := (finProdFinEquiv (i, j)).isLt
    change (if j.val + n * i.val < s * n then (j.val + n * i.val) / n
      else s + (j.val + n * i.val - s * n) / 3) = i.val
    rw [ite_eq_left hb, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hj]
    omega
  · have hj : j.val < 3 := j.isLt
    change (if s * n + (j.val + 3 * i.val) < s * n
      then (s * n + (j.val + 3 * i.val)) / n
      else s + (s * n + (j.val + 3 * i.val) - s * n) / 3) = s + i.val
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
      Nat.add_mul_div_left _ _ (by omega : 0 < 3), Nat.div_eq_of_lt hj]
    omega

def mixedMap (s n : ℕ) (v : Fin (mixedOrder s n)) : Fin (s + n) :=
  finSumFinEquiv ((mixedEquiv s n).symm v).1

@[simp] theorem mixedMap_val (s n : ℕ) (v : Fin (mixedOrder s n)) :
    (mixedMap s n v).val = mixedProjection s n v.val := by
  have h := mixedProjection_equiv s n ((mixedEquiv s n).symm v)
  simpa only [Equiv.apply_symm_apply, mixedMap] using h.symm

def mixedTable (s n : ℕ) : List ℕ :=
  (List.range (mixedOrder s n)).map (mixedProjection s n)

theorem mixedTable_get (s n : ℕ) (v : Fin (mixedOrder s n)) :
    (mixedTable s n).getD v.val 0 = (mixedMap s n v).val := by
  rw [mixedMap_val, List.getD_eq_getElem _ _ (by simpa [mixedTable] using v.isLt)]
  simp [mixedTable]

theorem mixedOrder_primrec : Primrec₂ mixedOrder :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.fst Primrec.snd)
    (Primrec.nat_mul.comp Primrec.snd (Primrec.const 3))

theorem mixedProjection_primrec : Primrec₂ (fun p : ℕ × ℕ => mixedProjection p.1 p.2) := by
  have hs : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2) := Primrec.snd
  have hsn := Primrec.nat_mul.comp hs hn
  exact Primrec.ite (Primrec.nat_lt.comp hk hsn) (Primrec.nat_div.comp hk hn)
    (Primrec.nat_add.comp hs (Primrec.nat_div.comp (Primrec.nat_sub.comp hk hsn)
      (Primrec.const 3)))

theorem mixedTable_primrec : Primrec₂ mixedTable :=
  Primrec.list_map (Primrec.list_range.comp mixedOrder_primrec) mixedProjection_primrec

end TuranUniversality.Effective.Uniform
