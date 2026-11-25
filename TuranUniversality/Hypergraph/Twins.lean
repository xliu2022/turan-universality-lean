module

public import TuranUniversality.Hypergraph.Restriction
public import TuranUniversality.Hypergraph.FiniteBasis
public import Mathlib.Data.Quot

@[expose] public section

/-! # Actual links, twins, and the pair-covered quotient

Vertices are twins precisely when their finite links are equal. The quotient
is realized on a subset of the original vertices; both its embedding and the
homomorphism from the original graph are constructed. Isolated vertices are
retained as a single class when present.
-/

namespace TuranUniversality.RGraph

universe u
variable {V : Type u} [DecidableEq V] {r : ℕ}

def link (G : RGraph V r) (v : V) : Finset (Finset V) :=
  (G.edges.filter (fun e => v ∈ e)).image (fun e => e.erase v)

@[simp] theorem mem_link (G : RGraph V r) (v : V) (s : Finset V) :
    s ∈ G.link v ↔ v ∉ s ∧ insert v s ∈ G.edges := by
  constructor
  · intro hs
    obtain ⟨e, he, hes⟩ := Finset.mem_image.mp hs
    obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
    subst s
    exact ⟨Finset.notMem_erase _ _, by simpa [Finset.insert_erase hv] using he⟩
  · rintro ⟨hv, he⟩
    exact Finset.mem_image.mpr ⟨insert v s,
      Finset.mem_filter.mpr ⟨he, Finset.mem_insert_self _ _⟩,
      Finset.erase_insert hv⟩

theorem erase_mem_link (G : RGraph V r) {e : Finset V} (he : e ∈ G.edges)
    {v : V} (hv : v ∈ e) : e.erase v ∈ G.link v :=
  (G.mem_link v _).mpr ⟨Finset.notMem_erase _ _, by simpa [Finset.insert_erase hv] using he⟩

theorem twins_not_cooccur (G : RGraph V r) {u v : V} (huv : u ≠ v)
    (ht : G.link u = G.link v) {e : Finset V} (he : e ∈ G.edges)
    (hu : u ∈ e) : v ∉ e := by
  intro hv
  have h := G.erase_mem_link he hu
  rw [ht] at h
  exact ((G.mem_link v _).mp h).1 (Finset.mem_erase.mpr ⟨huv.symm, hv⟩)

theorem replace_twin (G : RGraph V r) {u v : V} (ht : G.link u = G.link v)
    {e : Finset V} (he : e ∈ G.edges) (hu : u ∈ e) :
    insert v (e.erase u) ∈ G.edges := by
  have h := G.erase_mem_link he hu
  rw [ht] at h
  exact ((G.mem_link v _).mp h).2

def Symmetrized (G : RGraph V r) : Prop :=
  ∀ u v, (¬ ∃ e ∈ G.edges, u ∈ e ∧ v ∈ e) → G.link u = G.link v

def twinSetoid (G : RGraph V r) : Setoid V := Setoid.ker G.link

noncomputable def twinRepresentative (G : RGraph V r) (v : V) : V :=
  (Quotient.mk (G.twinSetoid) v).out

theorem link_twinRepresentative (G : RGraph V r) (v : V) :
    G.link (G.twinRepresentative v) = G.link v := by
  exact Quotient.mk_out (s := G.twinSetoid) v

theorem twinRepresentative_eq_iff (G : RGraph V r) (u v : V) :
    G.twinRepresentative u = G.twinRepresentative v ↔ G.link u = G.link v := by
  change (Quotient.mk G.twinSetoid u).out = (Quotient.mk G.twinSetoid v).out ↔ _
  rw [Quotient.out_inj, Quotient.eq]
  rfl

theorem twinRepresentative_idempotent (G : RGraph V r) :
    ∀ v, G.twinRepresentative (G.twinRepresentative v) = G.twinRepresentative v := by
  intro v
  exact (G.twinRepresentative_eq_iff _ _).mpr (G.link_twinRepresentative v)

theorem isHom_of_idempotent_twins (G : RGraph V r) (f : V → V)
    (hf : ∀ v, f (f v) = f v) (ht : ∀ v, G.link (f v) = G.link v) :
    G.IsHom G f := by
  classical
  intro e he
  generalize hn : (e.filter (fun v => f v ≠ v)).card = n
  induction n using Nat.strong_induction_on generalizing e with
  | h n ih =>
    by_cases hall : ∀ v ∈ e, f v = v
    · have hm : e.image f = e := by
        calc
          e.image f = e.image id := Finset.image_congr hall
          _ = e := Finset.image_id
      rw [hm]
      exact he
    · push_neg at hall
      obtain ⟨v, hv, hfv⟩ := hall
      let d := insert (f v) (e.erase v)
      have hd : d ∈ G.edges := G.replace_twin (ht v).symm he hv
      have hbad : d.filter (fun w => f w ≠ w) =
          (e.filter (fun w => f w ≠ w)).erase v := by
        ext w
        by_cases hw : w = f v
        · subst w
          simp [hf v]
        · simp [d, hw, and_left_comm, and_assoc]
      have hc : (d.filter (fun w => f w ≠ w)).card < n := by
        rw [hbad, ← hn]
        exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨hv, hfv⟩)
      have hm : d.image f = e.image f := by
        calc
          d.image f = insert (f (f v)) ((e.erase v).image f) := Finset.image_insert _ _ _
          _ = insert (f v) ((e.erase v).image f) := by rw [hf v]
          _ = (insert v (e.erase v)).image f := (Finset.image_insert _ _ _).symm
          _ = e.image f := by rw [Finset.insert_erase hv]
      rw [← hm]
      exact ih _ hc d hd rfl

theorem twinRepresentative_isHom (G : RGraph V r) :
    G.IsHom G G.twinRepresentative :=
  G.isHom_of_idempotent_twins _ G.twinRepresentative_idempotent G.link_twinRepresentative

abbrev TwinRepresentatives (G : RGraph V r) := {v : V // G.twinRepresentative v = v}

noncomputable def twinProjection (G : RGraph V r) (v : V) : G.TwinRepresentatives :=
  ⟨G.twinRepresentative v, G.twinRepresentative_idempotent v⟩

def twinInclusion (G : RGraph V r) : G.TwinRepresentatives ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

noncomputable def twinQuotient [Fintype V] (G : RGraph V r) :
    RGraph G.TwinRepresentatives r := by
  classical
  exact G.pullback G.twinInclusion

theorem twinQuotient_embedding [Fintype V] (G : RGraph V r) :
    G.twinQuotient.IsEmbedding G G.twinInclusion := by
  classical
  exact ⟨Subtype.val_injective, G.pullback_isHom G.twinInclusion⟩

theorem twinProjection_isHom [Fintype V] (G : RGraph V r) :
    G.IsHom G.twinQuotient G.twinProjection := by
  classical
  intro e he
  apply (G.mem_pullback G.twinInclusion _).mpr
  have hm : (e.image G.twinProjection).map G.twinInclusion = e.image G.twinRepresentative := by
    rw [Finset.map_eq_image, Finset.image_image]
    rfl
  refine ⟨?_, ?_⟩
  · have hc := G.uniform _ (G.twinRepresentative_isHom e he)
    rw [← hm, Finset.card_map] at hc
    exact hc
  · rw [hm]
    exact G.twinRepresentative_isHom e he

theorem Symmetrized.twinQuotient_coversPairs [Fintype V] {G : RGraph V r}
    (hG : G.Symmetrized) : G.twinQuotient.CoversPairs := by
  classical
  intro u v huv
  have hne : G.link u.val ≠ G.link v.val := by
    intro h
    apply huv
    apply Subtype.ext
    simpa [u.property, v.property] using (G.twinRepresentative_eq_iff u v).mpr h
  have hex : ∃ e ∈ G.edges, u.val ∈ e ∧ v.val ∈ e := by
    by_contra h
    exact hne (hG _ _ h)
  obtain ⟨e, he, hu, hv⟩ := hex
  refine ⟨e.image G.twinProjection, G.twinProjection_isHom e he, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨u.val, hu, Subtype.ext u.property⟩
  · exact Finset.mem_image.mpr ⟨v.val, hv, Subtype.ext v.property⟩

end TuranUniversality.RGraph
