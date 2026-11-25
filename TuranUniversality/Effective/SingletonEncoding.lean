module

public import TuranUniversality.Effective.GraphExtension
public import TuranUniversality.Effective.GraphListProduct
public import TuranUniversality.Hypergraph.Labeled
public import TuranUniversality.Density.HomInvariance

@[expose] public section

/-! # An actual primitive-recursive code for the singleton forbidden graph -/

namespace TuranUniversality.Effective

set_option backward.isDefEq.respectTransparency false

def singletonCode (cores : List GraphCode) : GraphCode :=
  productCode (cores.map pairExtensionCode)

theorem singletonCode_primrec : Primrec singletonCode :=
  productCode_primrec.comp (Primrec.list_map Primrec.id
    (pairExtensionCode_primrec.comp Primrec.snd).to₂)

theorem cores_ne_nil {cores : List GraphCode} {F : Finset (FiniteGraph 3)}
    (hdecode : (cores.map decodeGraphCode).toFinset = F) (hF : F.Nonempty) : cores ≠ [] := by
  intro h
  subst cores
  simp only [List.map_nil, List.toFinset_nil] at hdecode
  rw [← hdecode] at hF
  exact Finset.not_nonempty_empty hF

/-- Duplicate codes and different labels are harmless: the explicit code and
the mathematical product of the represented forbidden family have genuine
homomorphisms in both directions. -/
theorem singletonCode_mutual_hom (cores : List GraphCode) (F : Finset (FiniteGraph 3))
    (hdecode : (cores.map decodeGraphCode).toFinset = F) (hF : F.Nonempty) :
    (∃ f, (decodeGraph (singletonCode cores)).IsHom (FiniteGraph.singletonProduct F).2 f) ∧
      (∃ f, (FiniteGraph.singletonProduct F).2.IsHom (decodeGraph (singletonCode cores)) f) := by
  classical
  letI : Nonempty F := ⟨⟨hF.choose, hF.choose_spec⟩⟩
  let G := RGraph.product fun A : F => A.val.2.pairExtension
  have hcores := cores_ne_nil hdecode hF
  have hlist : cores.map pairExtensionCode ≠ [] := by simpa using hcores
  have hforward : ∀ A : F, ∃ f,
      (decodeGraph (singletonCode cores)).IsHom A.val.2.pairExtension f := by
    intro A
    have hm : A.val ∈ (cores.map decodeGraphCode).toFinset := hdecode.symm ▸ A.property
    obtain ⟨g, hg, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    obtain ⟨j, hj⟩ := productCode_projection (cores.map pairExtensionCode)
      (pairExtensionCode g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    have hc : ∃ f, (decodeGraph (singletonCode cores)).IsHom
        (decodeGraphCode g).2.pairExtension f :=
      ⟨_, (extensionCollapse_hom g).comp hj⟩
    exact heq ▸ hc
  choose f hf using hforward
  have htoG : (decodeGraph (singletonCode cores)).IsHom G (fun v A => f A v) :=
    RGraph.product_lift _ _ f hf
  have hfromG : ∃ j, G.IsHom (decodeGraph (singletonCode cores)) j := by
    apply productCode_lift G (cores.map pairExtensionCode) hlist
    intro a ha
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    have hm : decodeGraphCode g ∈ F := by
      rw [← hdecode]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨g, hg, rfl⟩)
    let A : F := ⟨decodeGraphCode g, hm⟩
    exact ⟨_, (extensionLift_hom g).comp (RGraph.product_projection _ A)⟩
  obtain ⟨j, hj⟩ := hfromG
  constructor
  · exact ⟨_, (FiniteGraph.embedding_ofRGraph G).isHom.comp htoG⟩
  · exact ⟨_, hj.comp (FiniteGraph.ofRGraph_embedding G).isHom⟩

theorem singletonCode_edges_nonempty (cores : List GraphCode) (F : Finset (FiniteGraph 3))
    (hdecode : (cores.map decodeGraphCode).toFinset = F) (hF : F.Nonempty)
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    (decodeGraph (singletonCode cores)).edges.Nonempty := by
  obtain ⟨f, hf⟩ := (singletonCode_mutual_hom cores F hdecode hF).2
  obtain ⟨e, he⟩ := FiniteGraph.singletonProduct_edges_nonempty F hF hedges
  exact ⟨_, hf e he⟩

theorem singletonCode_density (cores : List GraphCode) (F : Finset (FiniteGraph 3))
    (hdecode : (cores.map decodeGraphCode).toFinset = F) (hF : F.Nonempty)
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) :
    turanDensity (decodeGraph (singletonCode cores)) =
      turanDensity (FiniteGraph.singletonProduct F).2 := by
  obtain ⟨hforward, hbackward⟩ := singletonCode_mutual_hom cores F hdecode hF
  exact turanDensity_eq_of_mutualHom _ _
    (singletonCode_edges_nonempty cores F hdecode hF hedges)
    (FiniteGraph.singletonProduct_edges_nonempty F hF hedges) hforward hbackward

end TuranUniversality.Effective
