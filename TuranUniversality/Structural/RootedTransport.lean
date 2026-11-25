module

public import TuranUniversality.Structural.RootedRecords
public import TuranUniversality.Structural.RootedWitness
public import TuranUniversality.Structural.CompiledTransport
public import TuranUniversality.Weighted.IncidenceWitness

@[expose] public section

/-! # Ordinary embedding heredity and retained-vertex transport -/

namespace TuranUniversality.Structural.Rooted

universe u v

open Cube Support

variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] {b t : ℕ}

theorem place_comp (ρ : W → Option (Roots b t)) (f : V → W) (v : V) :
    Compiled.mapData f (place (ρ ∘ f) v) = place ρ (f v) := by
  cases h : ρ (f v) with
  | none => simp [place, Selector.rootedVertex, Function.comp_def, h, Compiled.mapData]
  | some r => cases r <;>
      simp [place, Selector.rootedVertex, Function.comp_def, h, Compiled.mapData]

noncomputable def pullbackRooting (μ : Rooting (Roots b t) W) (f : V ↪ W) : Rooting (Roots b t) V :=
  (μ.inverse.precompose f).inverse

@[simp] theorem pullbackRooting_inverse (μ : Rooting (Roots b t) W) (f : V ↪ W) :
    (pullbackRooting μ f).inverse.val = μ.inverse.val ∘ f := by
  simp [pullbackRooting, Rooting.precompose]

theorem mapped_inverse (μ : Rooting (Roots b t) V) (f : V ↪ W) (v : V) :
    (μ.map f).inverse.val (f v) = μ.inverse.val v := by
  have hiff (r : Roots b t) :
      (μ.map f).inverse.val (f v) = some r ↔ μ.inverse.val v = some r := by
    rw [Rooting.inverse_some_iff, Rooting.map_some_iff, Rooting.inverse_some_iff]
  cases h : μ.inverse.val v with
  | some r => exact (hiff r).mpr h
  | none =>
    cases hm : (μ.map f).inverse.val (f v) with
    | none => rfl
    | some r =>
      have he := (hiff r).mp hm
      rw [h] at he
      cases he

theorem mapped_place (μ : Rooting (Roots b t) V) (f : V ↪ W) (v : V) :
    Compiled.mapData f (place μ.inverse.val v) = place (μ.map f).inverse.val (f v) := by
  have h := place_comp (μ.map f).inverse.val f v
  have heq : (μ.map f).inverse.val ∘ f = μ.inverse.val := funext (mapped_inverse μ f)
  rw [heq] at h
  exact h

theorem Admits.of_embedding (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    {F : RGraph V (t + (3 * b + 4))} {G : RGraph W (t + (3 * b + 4))}
    {f : V → W} (hf : F.IsEmbedding G f) (hG : Admits B Ω G) : Admits B Ω F := by
  classical
  obtain ⟨μ, hμ⟩ := hG
  obtain ⟨R, hR, hlegal, hcomp⟩ := extract_records B Ω hdis G μ hμ
  let emb : V ↪ W := ⟨f, hf.1⟩
  let ν := pullbackRooting μ emb
  refine ⟨ν, admissible_of_records B Ω F ν (R.pullback emb) (hlegal.pullback emb) ?_⟩
  intro e he
  apply (Compiled.mem_graph_pullback Ω R emb _).mpr
  have himage : (e.image (place ν.inverse.val)).image (Compiled.mapData emb) =
      (e.image f).image (place μ.inverse.val) := by
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro v hv
    dsimp [ν]
    rw [pullbackRooting_inverse]
    exact place_comp μ.inverse.val emb v
  rw [himage]
  exact hcomp.2 _ (hf.2 e he)

/-- An admissible induced subgraph supplies a rooting of the original
carrier admissible on exactly its retained vertices. -/
theorem admissibleOn_of_induced (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (T : Finset V)
    (hT : Admits B Ω (G.pullback (Function.Embedding.subtype (· ∈ T)))) :
    ∃ μ : Rooting (Roots b t) V, AdmissibleOn B Ω G T μ := by
  classical
  let incl : T ↪ V := Function.Embedding.subtype (· ∈ T)
  obtain ⟨ν, hν⟩ := hT
  obtain ⟨R, hR, hlegal, hcomp⟩ := extract_records B Ω hdis (G.pullback incl) ν hν
  let μ := ν.map incl
  refine ⟨μ, admissibleOn_of_records B Ω G T μ (R.map incl) (hlegal.map incl) ?_⟩
  intro e he heT
  let d := TuranUniversality.Weighted.liftDataSet T e
  have hdimage : d.image (Subtype.val : T → V) = e := TuranUniversality.Weighted.liftDataSet_image T e heT
  have hd : d ∈ (G.pullback incl).edges := by
    apply (G.mem_pullback incl d).mpr
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_image_of_injective d Subtype.val_injective, hdimage, G.uniform e he]
    · rw [Finset.map_eq_image]
      change d.image (Subtype.val : T → V) ∈ G.edges
      rw [hdimage]
      exact he
  have h := (Compiled.records_map_isHom Ω R incl) _ (hcomp.2 d hd)
  have himage : (d.image (place ν.inverse.val)).image (Compiled.mapData incl) =
      e.image (place μ.inverse.val) := by
    rw [← hdimage, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro v hv
    exact mapped_place ν incl v
  rwa [himage] at h

/-- The bounded failure is an actual induced ordinary subgraph, not only
an ambient predicate about retained vertices. -/
theorem bounded_nonadmissible_subgraph (B : Finset (FiniteGraph 3))
    (Ω : Label → Finset (Word b)) (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (hbad : ¬ Admits B Ω G) :
    ∃ T : Finset V, T.card ≤ obstructionBound b t B ∧
      ¬ Admits B Ω (G.pullback (Function.Embedding.subtype (· ∈ T))) := by
  obtain ⟨T, hcard, hT⟩ := bounded_nonadmissible_on B Ω G hbad
  refine ⟨T, hcard, ?_⟩
  intro h
  obtain ⟨μ, hμ⟩ := admissibleOn_of_induced B Ω hdis G T h
  exact hT μ hμ

end TuranUniversality.Structural.Rooted
