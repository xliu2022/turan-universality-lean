module

public import TuranUniversality.Effective.GraphEncoding
public import TuranUniversality.Effective.WordEnumeration

@[expose] public section

/-! # One finite code type for every uniformity

The rank is an external natural-number parameter. A row contributes an edge
only when its length and the cardinality of its represented vertex set equal
the rank. Thus repetitions, out-of-range vertices, and malformed rows are
discarded. Every operation below varies primitively recursively with the rank.
-/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

abbrev Code := ℕ × List (List ℕ)

def decode (r : ℕ) (g : Code) : RGraph (Fin g.1) r where
  edges := (Finset.univ.powersetCard r).filter fun e =>
    ∃ w ∈ g.2, w.length = r ∧ e.image Fin.val = w.toFinset
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_decode (r : ℕ) (g : Code) (e : Finset (Fin g.1)) :
    e ∈ (decode r g).edges ↔
      e.card = r ∧ ∃ w ∈ g.2, w.length = r ∧ e.image Fin.val = w.toFinset := by
  simp [decode, Finset.mem_powersetCard]

def decodeFinite (r : ℕ) (g : Code) : FiniteGraph r := ⟨g.1, decode r g⟩

def allRows (r n : ℕ) : List (List ℕ) := allWords (List.range n) r

theorem allRows_primrec : Primrec₂ allRows :=
  allWords_primrec.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst

@[simp] theorem mem_allRows (r n : ℕ) (w : List ℕ) :
    w ∈ allRows r n ↔ w.length = r ∧ ∀ a ∈ w, a < n := by
  simp [allRows, mem_allWords]

def encode {r n : ℕ} (G : RGraph (Fin n) r) : Code :=
  (n, (allRows r n).filter fun w => ∃ e ∈ G.edges, e.image Fin.val = w.toFinset)

set_option backward.isDefEq.respectTransparency false in
theorem decode_encode {r n : ℕ} (G : RGraph (Fin n) r) :
    decode r (encode G) = G := by
  apply RGraph.ext
  ext e
  rw [mem_decode]
  constructor
  · rintro ⟨_, w, hw, _, he⟩
    simp only [encode, List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨_, d, hd, hdt⟩ := hw
    have hed : e = d := Finset.image_injective Fin.val_injective (he.trans hdt.symm)
    simpa only [hed] using hd
  · intro he
    let w := e.toList.map Fin.val
    have hwlen : w.length = r := by simp [w, G.uniform e he]
    have hwset : w.toFinset = e.image Fin.val := by
      ext a
      simp [w]
    refine ⟨G.uniform e he, w, ?_, hwlen, hwset.symm⟩
    apply List.mem_filter.mpr
    refine ⟨(mem_allRows r n w).mpr ⟨hwlen, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
      exact v.isLt
    · exact decide_eq_true (show ∃ d ∈ G.edges, d.image Fin.val = w.toFinset from
        ⟨e, he, hwset.symm⟩)

def encodeFinite {r : ℕ} (G : FiniteGraph r) : Code := encode G.2

@[simp] theorem decode_encodeFinite {r : ℕ} (G : FiniteGraph r) :
    decodeFinite r (encodeFinite G) = G := by
  rcases G with ⟨n, G⟩
  change (⟨n, decode r (encode G)⟩ : FiniteGraph r) = ⟨n, G⟩
  rw [decode_encode]

def graphCodes (r n : ℕ) : List Code :=
  (allRows r n).sublists'.map fun es => (n, es)

theorem graphCodes_primrec : Primrec₂ graphCodes :=
  Primrec.list_map (sublists_primrec.comp allRows_primrec)
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

@[simp] theorem mem_graphCodes (r n : ℕ) (g : Code) :
    g ∈ graphCodes r n ↔ g.1 = n ∧ g.2.Sublist (allRows r n) := by
  rcases g with ⟨m, es⟩
  simp only [graphCodes, List.mem_map, List.mem_sublists', Prod.mk.injEq]
  constructor
  · rintro ⟨l, hl, hnm, hle⟩
    exact ⟨hnm.symm, hle ▸ hl⟩
  · rintro ⟨rfl, hs⟩
    exact ⟨es, hs, rfl, rfl⟩

theorem encode_mem_graphCodes {r : ℕ} (G : FiniteGraph r) :
    encodeFinite G ∈ graphCodes r G.1 := by
  rw [mem_graphCodes]
  exact ⟨rfl, List.filter_sublist⟩

def boundedCodes (r B : ℕ) : List Code :=
  (List.range (B + 1)).flatMap (graphCodes r)

theorem boundedCodes_primrec : Primrec₂ boundedCodes :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    (graphCodes_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem mem_boundedCodes_size {r B : ℕ} {g : Code}
    (h : g ∈ boundedCodes r B) : g.1 ≤ B := by
  obtain ⟨n, hn, hg⟩ := List.mem_flatMap.mp h
  have hgn := (mem_graphCodes r n g).mp hg
  have hnb := List.mem_range.mp hn
  omega

theorem encode_mem_boundedCodes {r B : ℕ} (G : FiniteGraph r) (h : G.1 ≤ B) :
    encodeFinite G ∈ boundedCodes r B :=
  List.mem_flatMap.mpr ⟨G.1, List.mem_range.mpr (by omega), encode_mem_graphCodes G⟩

theorem boundedCodes_decode (r B : ℕ) :
    ((boundedCodes r B).map (decodeFinite r)).toFinset = FiniteGraph.bounded r B := by
  ext G
  simp only [List.mem_toFinset, List.mem_map, FiniteGraph.mem_bounded]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_boundedCodes_size hg
  · intro hG
    exact ⟨encodeFinite G, encode_mem_boundedCodes G hG, decode_encodeFinite G⟩

def tripleRow (t : Effective.Triple) : List ℕ := [t.1, t.2.1, t.2.2]

def liftThree (g : Effective.GraphCode) : Code := (g.1, g.2.map tripleRow)

theorem tripleRow_primrec : Primrec tripleRow :=
  Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))

theorem liftThree_primrec : Primrec liftThree :=
  Primrec.pair Primrec.fst
    (Primrec.list_map Primrec.snd (tripleRow_primrec.comp Primrec.snd).to₂)

@[simp] theorem decode_liftThree (g : Effective.GraphCode) :
    decode 3 (liftThree g) = Effective.decodeGraph g := by
  apply RGraph.ext
  ext e
  rw [mem_decode, Effective.mem_decodeGraph]
  simp [liftThree, tripleRow, Effective.tripleSet]

@[simp] theorem decodeFinite_liftThree (g : Effective.GraphCode) :
    decodeFinite 3 (liftThree g) = Effective.decodeGraphCode g := by
  change (⟨g.1, decode 3 (liftThree g)⟩ : FiniteGraph 3) = ⟨g.1, Effective.decodeGraph g⟩
  rw [decode_liftThree]

end TuranUniversality.Effective.Uniform
