module

public import TuranUniversality.Effective.UniformMaps
public import TuranUniversality.Uniformity.Admissible

@[expose] public section

/-! # A finite numeric test for the actual suspension class -/

namespace TuranUniversality.Effective.Uniform

set_option backward.isDefEq.respectTransparency false

def Edgeless (r : ℕ) (g : Code) : Prop :=
  ∀ w ∈ allRows r g.1, ¬ Edge r g w

instance (r : ℕ) (g : Code) : Decidable (Edgeless r g) := by
  unfold Edgeless
  infer_instance

theorem edgeless_iff (r : ℕ) (g : Code) : Edgeless r g ↔ (decode r g).edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hw := edge_canonical r g e he
    exact h _ ((mem_allRows r g.1 _).mpr ⟨hw.1.1, hw.1.2.2⟩) hw
  · intro h w _ hw
    have he := edge_rowSet r g w hw
    rw [h] at he
    exact Finset.notMem_empty _ he

def Core (r : ℕ) (g : Code) (s : List ℕ) : Prop :=
  Good (r - 3) g.1 s ∧ s.length + 3 = r ∧
    ∀ w ∈ allRows r g.1, Edge r g w → ∀ a ∈ s, a ∈ w

instance (r : ℕ) (g : Code) (s : List ℕ) : Decidable (Core r g s) := by
  unfold Core
  infer_instance

theorem rowSet_card {k n : ℕ} {s : List ℕ} (h : Good k n s) :
    (rowSet n s).card = s.length := by
  rw [← Finset.card_image_of_injective _ Fin.val_injective, rowSet_image n s h.2.2]
  exact List.toFinset_card_of_nodup ((distinct_iff s).mp h.2.1)

theorem rowSet_subset_iff {n : ℕ} (s : List ℕ) (hs : ∀ a ∈ s, a < n)
    (e : Finset (Fin n)) (w : List ℕ) (he : e.image Fin.val = w.toFinset) :
    rowSet n s ⊆ e ↔ ∀ a ∈ s, a ∈ w := by
  constructor
  · intro h a ha
    have hm : (⟨a, hs a ha⟩ : Fin n) ∈ e := h ((mem_rowSet n s _).mpr ha)
    exact List.mem_toFinset.mp (he ▸ Finset.mem_image.mpr ⟨_, hm, rfl⟩)
  · intro h v hv
    have hm : v.val ∈ e.image Fin.val :=
      he.symm ▸ List.mem_toFinset.mpr (h v.val ((mem_rowSet n s v).mp hv))
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hm
    exact Fin.val_injective hav ▸ ha

theorem core_iff (r : ℕ) (g : Code) (s : List ℕ) :
    Core r g s ↔ Good (r - 3) g.1 s ∧ (decode r g).IsCore (rowSet g.1 s) := by
  constructor
  · rintro ⟨hs, hcard, hedge⟩
    refine ⟨hs, ⟨by rwa [rowSet_card hs], ?_⟩⟩
    intro e he
    have hw := edge_canonical r g e he
    have him : e.image Fin.val = (e.toList.map Fin.val).toFinset := by
      rw [list_map_toFinset]
      simp
    apply (rowSet_subset_iff s hs.2.2 e _ him).mpr
    exact hedge _ ((mem_allRows r g.1 _).mpr ⟨hw.1.1, hw.1.2.2⟩) hw
  · rintro ⟨hs, hcore⟩
    refine ⟨hs, by simpa only [rowSet_card hs] using hcore.card, ?_⟩
    intro w _ hw
    exact (rowSet_subset_iff s hs.2.2 _ w (rowSet_image g.1 w hw.1.2.2)).mp
      (hcore.subset _ (edge_rowSet r g w hw))

def Outside (n : ℕ) (s xs : List ℕ) : Prop :=
  ∀ a < n, xs.getD a 0 ∉ s

instance (n : ℕ) (s xs : List ℕ) : Decidable (Outside n s xs) := by
  unfold Outside
  infer_instance

def LinkHomAssignment (r : ℕ) (p g : Code) (s xs : List ℕ) : Prop :=
  Outside p.1 s xs ∧
    ∀ w ∈ allRows 3 p.1, Edge 3 p w → Edge r g (s ++ imageRow xs w)

instance (r : ℕ) (p g : Code) (s xs : List ℕ) :
    Decidable (LinkHomAssignment r p g s xs) := by
  unfold LinkHomAssignment
  infer_instance

def LinkHasHom (r : ℕ) (p g : Code) (s : List ℕ) : Prop :=
  ∃ xs ∈ assignments p g, LinkHomAssignment r p g s xs

instance (r : ℕ) (p g : Code) (s : List ℕ) : Decidable (LinkHasHom r p g s) := by
  unfold LinkHasHom
  infer_instance

theorem coreLink_mem_of_card {n r : ℕ} (G : RGraph (Fin n) r)
    (S : Finset (Fin n)) (hS : S.card + 3 = r)
    (e : Finset {v // v ∉ S}) (he : S ∪ e.image Subtype.val ∈ G.edges) :
    e ∈ (G.coreLink S).edges := by
  apply (G.mem_coreLink S e).mpr
  refine ⟨?_, he⟩
  have hd : Disjoint S (e.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro v hv hm
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hm
    exact w.property hv
  have hc := G.uniform _ he
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ Subtype.val_injective] at hc
  omega

theorem core_union_image {n m : ℕ} (s : List ℕ) (hs : ∀ a ∈ s, a < n)
    (f : Fin m → {v : Fin n // v ∉ rowSet n s}) (xs : List ℕ)
    (hf : ∀ a, (f a).val.val = xs.getD a.val 0)
    (e : Finset (Fin m)) (w : List ℕ) (he : e.image Fin.val = w.toFinset) :
    ((rowSet n s) ∪ (e.image f).image Subtype.val).image Fin.val =
      (s ++ imageRow xs w).toFinset := by
  rw [Finset.image_union, rowSet_image n s hs]
  have hmap : ((e.image f).image Subtype.val).image Fin.val = (imageRow xs w).toFinset := by
    rw [imageRow, list_map_toFinset, ← he]
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro a _
    exact hf a
  rw [hmap]
  ext a
  simp

def linkAssignmentMap (p g : Code) (s xs : List ℕ) (hx : xs ∈ assignments p g)
    (ho : Outside p.1 s xs) : Fin p.1 → {v : Fin g.1 // v ∉ rowSet g.1 s} :=
  fun a => ⟨assignmentMap p g xs hx a, by
    rw [mem_rowSet]
    change xs.getD a.val 0 ∉ s
    exact ho a.val a.isLt⟩

theorem linkHasHom_iff (r : ℕ) (p g : Code) (s : List ℕ) (hcore : Core r g s) :
    LinkHasHom r p g s ↔
      ∃ f, (decode 3 p).IsHom ((decode r g).coreLink (rowSet g.1 s)) f := by
  constructor
  · rintro ⟨xs, hx, ho, hh⟩
    let f := linkAssignmentMap p g s xs hx ho
    refine ⟨f, ?_⟩
    intro e he
    have hw := edge_canonical 3 p e he
    have hrows : e.toList.map Fin.val ∈ allRows 3 p.1 :=
      (mem_allRows 3 p.1 _).mpr ⟨hw.1.1, hw.1.2.2⟩
    have him : e.image Fin.val = (e.toList.map Fin.val).toFinset := by
      rw [list_map_toFinset]
      simp
    have hraw := hh _ hrows hw
    have hlength : (s ++ imageRow xs (e.toList.map Fin.val)).length = r := by
      simp only [List.length_append, imageRow, List.length_map, hw.1.1]
      exact hcore.2.1
    have hedge := (edge_iff_of_image r g _ _ hlength
      (core_union_image s hcore.1.2.2 f xs (fun _ => rfl) e _ him)).mp hraw
    exact coreLink_mem_of_card _ _ ((core_iff r g s).mp hcore).2.card _ hedge
  · rintro ⟨f, hf⟩
    obtain ⟨xs, hx, hxs⟩ := map_assignment p g (fun a => (f a).val)
    have hget (a : Fin p.1) : (f a).val.val = xs.getD a.val 0 := by
      exact (congrArg (fun k : Fin p.1 → Fin g.1 => (k a).val) hxs).symm
    have ho : Outside p.1 s xs := by
      intro a ha hm
      apply (f ⟨a, ha⟩).property
      apply (mem_rowSet g.1 s _).mpr
      simpa only [hget] using hm
    refine ⟨xs, hx, ho, ?_⟩
    intro w _ hw
    let e := rowSet p.1 w
    have he : e ∈ (decode 3 p).edges := edge_rowSet 3 p w hw
    have hlength : (s ++ imageRow xs w).length = r := by
      simp only [List.length_append, imageRow, List.length_map, hw.1.1]
      exact hcore.2.1
    apply (edge_iff_of_image r g _ _ hlength
      (core_union_image s hcore.1.2.2 f xs hget e w (rowSet_image p.1 w hw.1.2.2))).mpr
    exact ((decode r g).mem_coreLink _ _).mp (hf e he) |>.2

def Admissible (r : ℕ) (p g : Code) : Prop :=
  Edgeless r g ∨ ∃ s ∈ allRows (r - 3) g.1, Core r g s ∧ ¬ LinkHasHom r p g s

instance (r : ℕ) (p g : Code) : Decidable (Admissible r p g) := by
  unfold Admissible
  infer_instance

theorem admissible_iff (r : ℕ) (p g : Code) :
    Admissible r p g ↔ Uniformity.Admissible (decode 3 p) (decode r g) := by
  constructor
  · rintro (he | ⟨s, _, hc, hf⟩)
    · exact Or.inl ((edgeless_iff r g).mp he)
    · exact Or.inr ⟨rowSet g.1 s, ((core_iff r g s).mp hc).2,
        fun h => hf ((linkHasHom_iff r p g s hc).mpr h)⟩
  · rintro (he | ⟨S, hS, hf⟩)
    · exact Or.inl ((edgeless_iff r g).mpr he)
    · let s := S.toList.map Fin.val
      have hslen : s.length = r - 3 := by
        have := hS.card
        simp only [s, List.length_map, Finset.length_toList]
        omega
      have hsbound : ∀ a ∈ s, a < g.1 := by
        intro a ha
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
        exact v.isLt
      have hsset : rowSet g.1 s = S := by
        ext v
        simp [s, Fin.val_inj]
      have hgood : Good (r - 3) g.1 s :=
        ⟨hslen, (distinct_iff s).mpr (S.nodup_toList.map Fin.val_injective), hsbound⟩
      have hcore : Core r g s := (core_iff r g s).mpr ⟨hgood, hsset.symm ▸ hS⟩
      refine Or.inr ⟨s, (mem_allRows _ _ _).mpr ⟨hslen, hsbound⟩, hcore, ?_⟩
      intro hh
      exact hf (hsset ▸ (linkHasHom_iff r p g s hcore).mp hh)

end TuranUniversality.Effective.Uniform
