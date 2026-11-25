module

public import TuranUniversality.Density.Box
public import TuranUniversality.Density.HomDensity
public import TuranUniversality.Hypergraph.Blowup

@[expose] public section

/-! # Quantitative homomorphism-density bounds for finite blowups -/

namespace TuranUniversality.RGraph

open Selector Density

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable {r d : ℕ}

/-- Cloning every source vertex s times raises the original homomorphism
density to at most the power s^d. This is a proved finite inequality. -/
theorem homDensity_blowup_ge [Fintype W] [Nonempty W]
    (F : RGraph (Fin d) r) (G : RGraph W r) (s : ℕ) (hs : 0 < s) :
    F.homDensity G ^ (s ^ d) ≤ (F.blowup (fun _ => s)).homDensity G := by
  classical
  have h := box_power_function s d (fun f => F.IsHom G f)
  have heq : (F.blowup (fun _ => s)).homDensity G =
      mean (fun x : Fin d → Fin s → W => truth
        (∀ c : Fin d → Fin s, F.IsHom G (fun i => x i (c i)))) := by
    apply Fintype.expect_equiv (Equiv.piCurry (fun _ : Fin d => fun _ : Fin s => W))
    intro f
    unfold homIndicator truth
    congr 1
    exact propext (F.hom_blowup_iff_sections G s hs f)
  rw [heq]
  have hh : mean (fun f : Fin d → W => truth (F.IsHom G f)) = F.homDensity G := by
    apply mean_congr
    intro f
    by_cases hf : F.IsHom G f <;> simp [truth, homIndicator, hf]
  rwa [hh] at h

/-- If F maps to Q, a sufficiently large blowup of Q contains F as an ordinary
subgraph. Consequently small F-density forces small Q-density quantitatively. -/
theorem homDensity_power_le_of_hom [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (Q : RGraph (Fin d) r) (G : RGraph W r)
    {f : V → Fin d} (hf : F.IsHom Q f) (s : ℕ)
    (hs : Fintype.card V ≤ s) (hpos : 0 < s) :
    Q.homDensity G ^ (s ^ d) ≤ F.homDensity G := by
  obtain ⟨g, hg⟩ := F.embedding_blowup_of_hom Q hf s hs
  exact (Q.homDensity_blowup_ge G s hpos).trans
    (F.homDensity_le_of_embedding (Q.blowup (fun _ => s)) G hg)

/-- Uniform quantitative control of homomorphic-image density in every
ordinary F-free host. -/
theorem homImage_density_bound [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (Q : RGraph (Fin d) r) (G : RGraph W r)
    (hfree : ¬ ∃ f, F.IsEmbedding G f) {f : V → Fin d} (hf : F.IsHom Q f)
    (s : ℕ) (hs : Fintype.card V ≤ s) (hpos : 0 < s) :
    Q.homDensity G ^ (s ^ d) ≤
      (Fintype.card V : ℝ) ^ 2 / Fintype.card W :=
  (F.homDensity_power_le_of_hom Q G hf s hs hpos).trans
    (F.homDensity_le_collision_bound G hfree)

end TuranUniversality.RGraph
