module

public import TuranUniversality.Effective.ListOperations
public import TuranUniversality.Hypergraph.FiniteBasis

/-!
# Concrete primitive-recursive codes for finite three-uniform hypergraphs

A code is a vertex count and a finite list of ordered triples of natural
numbers.  Decoding forgets order and duplicates and ignores triples which do
not give three vertices in range.  This total convention permits direct list
algorithms without dependent finite-carrier encodings.  Every actual finite
three-graph is represented, and the bounded enumeration is proved complete.
-/

@[expose] public section

namespace TuranUniversality.Effective

abbrev Triple := ℕ × ℕ × ℕ
abbrev GraphCode := ℕ × List Triple

def tripleSet (t : Triple) : Finset ℕ := {t.1, t.2.1, t.2.2}

def allTriples (n : ℕ) : List Triple :=
  cartesian (List.range n) (cartesian (List.range n) (List.range n))

theorem allTriples_primrec : Primrec allTriples :=
  cartesian_primrec.comp Primrec.list_range
    (cartesian_primrec.comp Primrec.list_range Primrec.list_range)

@[simp] theorem mem_allTriples (n : ℕ) (t : Triple) :
    t ∈ allTriples n ↔ t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n := by
  simp [allTriples]

def decodeGraph (g : GraphCode) : RGraph (Fin g.1) 3 where
  edges := (Finset.univ.powersetCard 3).filter fun e =>
    ∃ t ∈ g.2, e.image Fin.val = tripleSet t
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_decodeGraph (g : GraphCode) (e : Finset (Fin g.1)) :
    e ∈ (decodeGraph g).edges ↔ e.card = 3 ∧ ∃ t ∈ g.2, e.image Fin.val = tripleSet t := by
  simp [decodeGraph, Finset.mem_powersetCard]

def decodeGraphCode (g : GraphCode) : FiniteGraph 3 := ⟨g.1, decodeGraph g⟩

def encodeGraph (n : ℕ) (G : RGraph (Fin n) 3) : GraphCode :=
  (n, (allTriples n).filter fun t => ∃ e ∈ G.edges, e.image Fin.val = tripleSet t)

set_option backward.isDefEq.respectTransparency false in
theorem decode_encode_graph (n : ℕ) (G : RGraph (Fin n) 3) :
    decodeGraph (encodeGraph n G) = G := by
  apply RGraph.ext
  ext e
  rw [mem_decodeGraph]
  constructor
  · rintro ⟨_, t, ht, he⟩
    simp only [encodeGraph, List.mem_filter, decide_eq_true_eq] at ht
    obtain ⟨_, d, hd, hdt⟩ := ht
    have hed : e = d := Finset.image_injective Fin.val_injective (he.trans hdt.symm)
    simpa only [hed] using hd
  · intro he
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (G.uniform e he)
    refine ⟨by simp [hab, hac, hbc], (a.val, b.val, c.val), ?_, ?_⟩
    · simp only [encodeGraph, List.mem_filter, decide_eq_true_eq]
      refine ⟨(mem_allTriples n _).mpr ⟨a.isLt, b.isLt, c.isLt⟩, ?_⟩
      exact ⟨{a, b, c}, he, by simp [tripleSet]⟩
    · simp [tripleSet]

def encodeFiniteGraph (G : FiniteGraph 3) : GraphCode := encodeGraph G.1 G.2

@[simp] theorem decode_encode_finiteGraph (G : FiniteGraph 3) :
    decodeGraphCode (encodeFiniteGraph G) = G := by
  rcases G with ⟨n, G⟩
  change (⟨n, decodeGraph (encodeGraph n G)⟩ : FiniteGraph 3) = ⟨n, G⟩
  rw [decode_encode_graph]

/-- Explicit finite enumeration; several codes may decode to the same graph. -/
def graphCodes (n : ℕ) : List GraphCode :=
  (allTriples n).sublists'.map fun es => (n, es)

theorem graphCodes_primrec : Primrec graphCodes :=
  Primrec.list_map (sublists_primrec.comp allTriples_primrec)
    (Primrec.pair Primrec.fst Primrec.snd).to₂

@[simp] theorem mem_graphCodes (n : ℕ) (g : GraphCode) :
    g ∈ graphCodes n ↔ g.1 = n ∧ g.2.Sublist (allTriples n) := by
  rcases g with ⟨m, es⟩
  simp only [graphCodes, List.mem_map, List.mem_sublists', Prod.mk.injEq]
  constructor
  · rintro ⟨l, hl, hnm, hle⟩
    exact ⟨hnm.symm, hle ▸ hl⟩
  · rintro ⟨rfl, hs⟩
    exact ⟨es, hs, rfl, rfl⟩

theorem encode_mem_graphCodes (G : FiniteGraph 3) : encodeFiniteGraph G ∈ graphCodes G.1 := by
  rw [mem_graphCodes]
  exact ⟨rfl, List.filter_sublist⟩

def boundedGraphCodes (B : ℕ) : List GraphCode :=
  (List.range (B + 1)).flatMap graphCodes

theorem boundedGraphCodes_primrec : Primrec boundedGraphCodes :=
  Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
    (graphCodes_primrec.comp Primrec.snd).to₂

theorem mem_boundedGraphCodes_size {B : ℕ} {g : GraphCode}
    (h : g ∈ boundedGraphCodes B) : g.1 ≤ B := by
  obtain ⟨n, hn, hg⟩ := List.mem_flatMap.mp h
  have hgn := (mem_graphCodes n g).mp hg
  have hnb : n < B + 1 := List.mem_range.mp hn
  omega

theorem encode_mem_boundedGraphCodes {B : ℕ} (G : FiniteGraph 3) (h : G.1 ≤ B) :
    encodeFiniteGraph G ∈ boundedGraphCodes B :=
  List.mem_flatMap.mpr ⟨G.1, List.mem_range.mpr (by omega), encode_mem_graphCodes G⟩

/-- The list algorithm enumerates exactly the previously defined actual
finite hypergraphs of bounded order. -/
theorem boundedGraphCodes_decode (B : ℕ) :
    ((boundedGraphCodes B).map decodeGraphCode).toFinset = FiniteGraph.bounded 3 B := by
  ext G
  simp only [List.mem_toFinset, List.mem_map, FiniteGraph.mem_bounded]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_boundedGraphCodes_size hg
  · intro hG
    exact ⟨encodeFiniteGraph G, encode_mem_boundedGraphCodes G hG, decode_encode_finiteGraph G⟩

end TuranUniversality.Effective
