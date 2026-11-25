module

public import TuranUniversality.Structural.FiniteBasis
public import TuranUniversality.Structural.CompiledCloning

@[expose] public section

/-! # Canonical presentations of ordinary hypergraphs

The role map partitions the original vertex set into data vertices and root
classes. Data vertices remain distinct in `place`; root classes may have
arbitrary size, including zero. An ordinary homomorphism into the actual
compiled records enforces every edge profile and forbids repetitions of a
root role inside an edge. This is the root-support-completed presentation.
-/

namespace TuranUniversality.Structural

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] {b t : ℕ}

def Canonical (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (G : RGraph V (t + (3 * b + 4))) : Prop :=
  ∃ (ρ : V → Option (Rooted.Roots b t)) (R : RecordSystem V),
    R.LocallyLegal B ∧ G.IsHom (Compiled.graph t Ω R) (Rooted.place ρ)

namespace Canonical

theorem of_admits (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    {G : RGraph V (t + (3 * b + 4))} (hG : Rooted.Admits B Ω G) : Canonical B Ω G := by
  obtain ⟨μ, hμ⟩ := hG
  obtain ⟨R, hR, hlegal, hcomp⟩ := Rooted.extract_records B Ω hdis G μ hμ
  exact ⟨μ.inverse.val, R, hlegal, hcomp.2⟩

theorem of_hom (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    {G : RGraph V (t + (3 * b + 4))} {H : RGraph W (t + (3 * b + 4))}
    {f : V → W} (hf : G.IsHom H f) (hH : Canonical (homomorphicClosure F) Ω H) :
    Canonical (homomorphicClosure F) Ω G := by
  classical
  obtain ⟨ρ, R, hR, hhom⟩ := hH
  refine ⟨ρ ∘ f, R.clone f, hR.clone f, ?_⟩
  intro e he
  apply (Compiled.mem_graph_clone Ω R f _).mpr
  have hi : (e.image (Rooted.place (ρ ∘ f))).image (Compiled.mapData f) =
      (e.image f).image (Rooted.place ρ) := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun v _ => Rooted.place_comp ρ f v)
  have ht : (e.image (Rooted.place (ρ ∘ f))).image (Compiled.mapData f) ∈
      (Compiled.graph t Ω R).edges := by
    rw [hi]
    exact hhom _ (hf e he)
  refine ⟨?_, ht⟩
  have hc := (Compiled.graph t Ω R).uniform _ ht
  exact le_antisymm (Finset.card_image_le.trans_eq (G.uniform e he))
    (hc ▸ Finset.card_image_le)

theorem of_embedding (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    {G : RGraph V (t + (3 * b + 4))} {H : RGraph W (t + (3 * b + 4))}
    {f : V → W} (hf : G.IsEmbedding H f) (hH : Canonical (homomorphicClosure F) Ω H) :
    Canonical (homomorphicClosure F) Ω G := of_hom F Ω hf.2 hH

theorem blowup (F : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    {G : RGraph V (t + (3 * b + 4))} (hG : Canonical (homomorphicClosure F) Ω G)
    (sizes : V → ℕ) : Canonical (homomorphicClosure F) Ω (G.blowup sizes) :=
  of_hom F Ω (G.blowup_projection sizes) hG

end Canonical

namespace Compiled

def dataEmbedding : V ↪ Vertex b t V :=
  ⟨fun v => Sum.inr (Sum.inr v), Sum.inr_injective.comp Sum.inr_injective⟩

def standardLabels : Vertex b t V → Option (Rooted.Roots b t)
  | .inl i => some (.inl i)
  | .inr (.inl v) => some (.inr v)
  | .inr (.inr _) => none

theorem standardLabels_injective : ∀ x y r,
    (standardLabels (b := b) (t := t) x : Option (Rooted.Roots b t)) = some r →
      standardLabels y = some r → (x : Vertex b t V) = y := by
  intro x y r hx hy
  rcases x with i | (v | v) <;> rcases y with j | (w | w) <;>
    simp_all [standardLabels] <;> simpa using hx.trans hy.symm

noncomputable def standardRooting : Rooting (Rooted.Roots b t) (Vertex b t V) :=
  Rooting.inverse ⟨standardLabels, standardLabels_injective⟩

@[simp] theorem standardRooting_inverse :
    (standardRooting (V := V) (b := b) (t := t)).inverse.val = standardLabels := by
  simp [standardRooting]

theorem standard_place (v : Vertex b t V) :
    Rooted.place standardLabels v = mapData (dataEmbedding (V := V) (b := b) (t := t)) v := by
  rcases v with i | (v | v) <;>
    simp [Rooted.place, Selector.rootedVertex, standardLabels, mapData, dataEmbedding]

theorem admits (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (hR : R.LocallyLegal B) : Rooted.Admits B Ω (graph t Ω R) := by
  refine ⟨standardRooting, Rooted.admissible_of_records B Ω (graph t Ω R) standardRooting
    (R.map dataEmbedding) (hR.map dataEmbedding) ?_⟩
  rw [standardRooting_inverse]
  have heq : Rooted.place (standardLabels (V := V) (b := b) (t := t)) = mapData dataEmbedding :=
    funext standard_place
  rw [heq]
  exact records_map_isHom Ω R dataEmbedding

theorem canonical (B : Finset (FiniteGraph 3)) (Ω : Label → Finset (Cube.Word b))
    (R : RecordSystem V) (hR : R.LocallyLegal B) : Canonical B Ω (graph t Ω R) := by
  refine ⟨standardLabels, R.map dataEmbedding, hR.map dataEmbedding, ?_⟩
  have heq : Rooted.place (standardLabels (V := V) (b := b) (t := t)) = mapData dataEmbedding :=
    funext standard_place
  rw [heq]
  exact records_map_isHom Ω R dataEmbedding

end Compiled

end TuranUniversality.Structural
