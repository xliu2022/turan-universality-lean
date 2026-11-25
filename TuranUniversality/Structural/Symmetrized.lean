module

public import TuranUniversality.Structural.OrdinaryFamily
public import TuranUniversality.Hypergraph.Twins

@[expose] public section

/-! # Every symmetrized free graph is canonical

The twin quotient is an actual induced subgraph on representatives. Its
pair coverage excludes the rooted obstruction basis by the concrete
pair-covering extensions. The projection then supplies the canonical
presentation of the original graph, with all isolated vertices included.
-/

namespace TuranUniversality.Structural.Ordinary

variable {V : Type*} [DecidableEq V] [Fintype V] {b t : ℕ}

theorem symmetrized_canonical (F : Finset (FiniteGraph 3))
    (hedges : ∀ A ∈ F, A.2.edges.Nonempty) (Ω : Label → Finset (Cube.Word b))
    (hdis : ∀ l k, l ≠ k → Disjoint (Ω l) (Ω k))
    (G : RGraph V (t + (3 * b + 4))) (hfree : familyFree (forbidden F Ω t) G)
    (hsymm : G.Symmetrized) : Canonical (homomorphicClosure F) Ω G := by
  classical
  have hQ : familyFree (forbidden F Ω t) G.twinQuotient :=
    familyFree_of_embedding _ _ G G.twinQuotient_embedding hfree
  have hext : familyFree
      (PairTransfer.extensionFamily (Rooted.basis (homomorphicClosure F) Ω t))
      G.twinQuotient := fun A hA => hQ A (extensionFamily_subset F Ω hdis t hA)
  have hbase : familyFree (Rooted.basis (homomorphicClosure F) Ω t) G.twinQuotient :=
    PairTransfer.free_of_pairCovered _ (by omega)
      (fun A hA => Rooted.basis_has_edges (homomorphicClosure F)
        (homomorphicClosure_has_edges F hedges) Ω t hA)
      G.twinQuotient hext hsymm.twinQuotient_coversPairs
  have hadmits : Rooted.Admits (homomorphicClosure F) Ω G.twinQuotient :=
    (Rooted.basis_spec_finite _ Ω hdis G.twinQuotient).mpr hbase
  exact Canonical.of_hom F Ω G.twinProjection_isHom
    (Canonical.of_admits _ Ω hdis hadmits)

end TuranUniversality.Structural.Ordinary
