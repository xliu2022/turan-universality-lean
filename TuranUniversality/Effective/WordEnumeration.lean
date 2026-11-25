module

public import TuranUniversality.Effective.ListOperations

/-! # Primitive-recursive enumeration of all finite assignments -/

@[expose] public section

namespace TuranUniversality.Effective

variable {A : Type*} [Primcodable A]

def prependLetters (alphabet : List A) (words : List (List A)) : List (List A) :=
  (cartesian alphabet words).map fun p => p.1 :: p.2

theorem prependLetters_primrec : Primrec₂ (prependLetters (A := A)) :=
  (Primrec.list_map cartesian_primrec (Primrec.list_cons.comp₂
    (Primrec.fst.comp Primrec.snd).to₂ (Primrec.snd.comp Primrec.snd).to₂)).to₂

theorem mem_prependLetters (alphabet : List A) (words : List (List A)) (w : List A) :
    w ∈ prependLetters alphabet words ↔ ∃ a ∈ alphabet, ∃ v ∈ words, a :: v = w := by
  simp only [prependLetters, List.mem_map, mem_cartesian]
  constructor
  · rintro ⟨⟨a, v⟩, ⟨ha, hv⟩, heq⟩
    exact ⟨a, ha, v, hv, heq⟩
  · rintro ⟨a, ha, v, hv, heq⟩
    exact ⟨(a, v), ⟨ha, hv⟩, heq⟩

def allWords (alphabet : List A) (n : ℕ) : List (List A) :=
  (prependLetters alphabet)^[n] [[]]

theorem allWords_primrec : Primrec₂ (allWords (A := A)) :=
  (Primrec.nat_iterate Primrec.snd (Primrec.const [[]])
    (prependLetters_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem mem_allWords (alphabet : List A) (n : ℕ) (w : List A) :
    w ∈ allWords alphabet n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero =>
    simp [allWords]
    rintro rfl a ha
    cases ha
  | succ n ih =>
    rw [allWords, Function.iterate_succ_apply', mem_prependLetters]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩
      obtain ⟨hlen, hall⟩ := (ih v).mp hv
      exact ⟨by simp [hlen], by intro b hb; rcases List.mem_cons.mp hb with rfl | hb; exact ha; exact hall b hb⟩
    · rintro ⟨hlen, hall⟩
      cases w with
      | nil => simp at hlen
      | cons a v =>
        refine ⟨a, hall a (by simp), v, (ih v).mpr ⟨?_, ?_⟩, rfl⟩
        · simpa using hlen
        · intro b hb
          exact hall b (by simp [hb])

end TuranUniversality.Effective
