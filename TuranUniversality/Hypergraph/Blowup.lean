module

public import TuranUniversality.Hypergraph.Hom

@[expose] public section

/-! # Finite blowups and ordinary subgraph avoidance -/

namespace TuranUniversality.RGraph

universe u v

/-- Vertices of a blowup, allowing clone classes of size zero. -/
abbrev BlowupVertex {V : Type u} (sizes : V → ℕ) := Σ v, Fin (sizes v)

/-- A blowup has precisely those r-sets whose core projection is an edge. -/
noncomputable def blowup {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (sizes : V → ℕ) : RGraph (BlowupVertex sizes) r := by
  classical
  exact ⟨(Finset.univ.powersetCard r).filter
    (fun e => e.image Sigma.fst ∈ G.edges),
    fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

theorem mem_blowup {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (sizes : V → ℕ) (e : Finset (BlowupVertex sizes)) :
    e ∈ (G.blowup sizes).edges ↔ e.card = r ∧ e.image Sigma.fst ∈ G.edges := by
  classical
  simp [blowup, Finset.mem_powersetCard]

theorem blowup_projection {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (sizes : V → ℕ) :
    (G.blowup sizes).IsHom G Sigma.fst := by
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem blowup_homFree {V : Type u} [DecidableEq V] [Fintype V]
    {W : Type v} [DecidableEq W] {r : ℕ}
    (F : RGraph W r) (G : RGraph V r) (h : F.HomFree G) (sizes : V → ℕ) :
    F.HomFree (G.blowup sizes) := by
  rintro ⟨f, hf⟩
  exact h ⟨Sigma.fst ∘ f, (blowup_projection G sizes).comp hf⟩

theorem blowup_free {V : Type u} [DecidableEq V] [Fintype V]
    {W : Type v} [DecidableEq W] {r : ℕ}
    (F : RGraph W r) (G : RGraph V r) (h : F.HomFree G) (sizes : V → ℕ) :
    ¬ ∃ f, F.IsEmbedding (G.blowup sizes) f :=
  (blowup_homFree F G h sizes).free

/-- Every choice of one clone per original vertex is an embedded copy. -/
theorem blowup_section {V : Type u} [DecidableEq V] [Fintype V]
    {r : ℕ} (G : RGraph V r) (sizes : V → ℕ) (c : ∀ v, Fin (sizes v)) :
    G.IsEmbedding (G.blowup sizes) (fun v => ⟨v, c v⟩) := by
  classical
  have hi : Function.Injective (fun v : V => (⟨v, c v⟩ : BlowupVertex sizes)) :=
    fun _ _ h => congrArg Sigma.fst h
  refine ⟨hi, ?_⟩
  intro e he
  apply (G.mem_blowup sizes _).mpr
  constructor
  · rw [Finset.card_image_of_injective _ hi]
    exact G.uniform e he
  · simpa [Finset.image_image, Function.comp_def] using he

/-- A homomorphism into a template lifts to an ordinary embedding into a
large enough balanced blowup. Clone labels remember all source vertices. -/
theorem embedding_blowup_of_hom {V : Type u} [DecidableEq V] [Fintype V]
    {W : Type v} [DecidableEq W] [Fintype W] {r : ℕ}
    (F : RGraph V r) (G : RGraph W r) {f : V → W} (hf : F.IsHom G f)
    (s : ℕ) (hs : Fintype.card V ≤ s) :
    ∃ g, F.IsEmbedding (G.blowup (fun _ => s)) g := by
  classical
  let j : V ↪ Fin s :=
    (Fintype.equivFin V).toEmbedding.trans ⟨Fin.castLE hs, Fin.castLE_injective hs⟩
  let g (v : V) : BlowupVertex (fun _ : W => s) := ⟨f v, j v⟩
  have hg : Function.Injective g := by
    intro a b hab
    exact j.injective (congrArg (fun z : BlowupVertex (fun _ : W => s) => z.2) hab)
  refine ⟨g, hg, ?_⟩
  intro e he
  apply (G.mem_blowup _ _).mpr
  constructor
  · rw [Finset.card_image_of_injective _ hg]
    exact F.uniform e he
  · simpa [g, Finset.image_image, Function.comp_def] using hf e he

/-- A map out of a balanced blowup is a homomorphism precisely when every
choice of one clone from each class gives a homomorphism from the template. -/
theorem hom_blowup_iff_sections {V : Type u} [DecidableEq V] [Fintype V]
    {W : Type v} [DecidableEq W] {r : ℕ}
    (F : RGraph V r) (G : RGraph W r) (s : ℕ) (hs : 0 < s)
    (g : BlowupVertex (fun _ : V => s) → W) :
    (F.blowup (fun _ => s)).IsHom G g ↔
      ∀ c : V → Fin s, F.IsHom G (fun v => g ⟨v, c v⟩) := by
  classical
  constructor
  · intro h c
    exact h.comp (F.blowup_section (fun _ => s) c).isHom
  · intro h e he
    let c (v : V) : Fin s := if hp : ∃ j : Fin s, (⟨v, j⟩ : BlowupVertex (fun _ : V => s)) ∈ e
      then Classical.choose hp else ⟨0, hs⟩
    have hinj := (F.blowup_projection (fun _ => s)).injOn_edge he
    have hchoice (p : BlowupVertex (fun _ : V => s)) (hp : p ∈ e) : c p.1 = p.2 := by
      have hex : ∃ j : Fin s, (⟨p.1, j⟩ : BlowupVertex (fun _ : V => s)) ∈ e := ⟨p.2, hp⟩
      have hm : (⟨p.1, c p.1⟩ : BlowupVertex (fun _ : V => s)) ∈ e := by
        simpa only [c, dite_eq_left hex] using Classical.choose_spec hex
      exact congrArg (fun z : BlowupVertex (fun _ : V => s) => z.2)
        (hinj hm hp rfl)
    have hm := h c (e.image Sigma.fst) ((F.mem_blowup _ e).mp he).2
    rw [Finset.image_image] at hm
    have him : e.image ((fun v => g ⟨v, c v⟩) ∘ Sigma.fst) = e.image g := by
      apply Finset.image_congr
      intro p hp
      simp only [Function.comp_apply, hchoice p hp]
    rwa [him] at hm

end TuranUniversality.RGraph
