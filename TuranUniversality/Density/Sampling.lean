module

public import TuranUniversality.Density.Cloning

@[expose] public section

/-!
# Sampling hom-free templates from ordinary forbidden-free graphs

Sampling is with replacement. The probability that the sampled template admits
a forbidden homomorphism tends uniformly to zero in ordinary forbidden-free
hosts, by an explicit power bound proved below.
-/

open scoped BigOperators

namespace TuranUniversality.RGraph

open Selector Density

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W] {r : ℕ}

/-- Sample a hypergraph at a specified list of vertices, with replacement. -/
def sample (G : RGraph W r) (m : ℕ) (f : Fin m → W) : RGraph (Fin m) r where
  edges := (Finset.univ.powersetCard r).filter (fun e => e.image f ∈ G.edges)
  uniform _e he := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_sample (G : RGraph W r) (m : ℕ) (f : Fin m → W)
    (e : Finset (Fin m)) :
    e ∈ (G.sample m f).edges ↔ e.card = r ∧ e.image f ∈ G.edges := by
  simp [sample, Finset.mem_powersetCard]

theorem sample_projection (G : RGraph W r) (m : ℕ) (f : Fin m → W) :
    (G.sample m f).IsHom G f := by
  intro e he
  exact ((G.mem_sample m f e).mp he).2

theorem sample_homFree (F : RGraph V r) (G : RGraph W r)
    (h : F.HomFree G) (m : ℕ) (f : Fin m → W) : F.HomFree (G.sample m f) := by
  rintro ⟨g, hg⟩
  exact h ⟨_, (G.sample_projection m f).comp hg⟩

def Noncollapsing (F : RGraph V r) {m : ℕ} (g : V → Fin m) : Prop :=
  ∀ e ∈ F.edges, (e.image g).card = r

/-- The actual simple homomorphic image, for an edge-injective vertex map. -/
def imageGraph (F : RGraph V r) {m : ℕ} (g : V → Fin m) (hg : F.Noncollapsing g) :
    RGraph (Fin m) r where
  edges := F.edges.image (fun e => e.image g)
  uniform e he := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact hg d hd

theorem imageGraph_hom (F : RGraph V r) {m : ℕ} (g : V → Fin m)
    (hg : F.Noncollapsing g) : F.IsHom (F.imageGraph g hg) g := by
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem noncollapsing_of_sample_hom (F : RGraph V r) (G : RGraph W r)
    {m : ℕ} {f : Fin m → W} {g : V → Fin m} (h : F.IsHom (G.sample m f) g) :
    F.Noncollapsing g := fun e he => (G.mem_sample m f _).mp (h e he) |>.1

theorem hom_sample_iff_image (F : RGraph V r) (G : RGraph W r)
    {m : ℕ} (g : V → Fin m) (hg : F.Noncollapsing g) (f : Fin m → W) :
    F.IsHom (G.sample m f) g ↔ (F.imageGraph g hg).IsHom G f := by
  constructor
  · intro h e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact ((G.mem_sample m f _).mp (h d hd)).2
  · intro h e he
    exact (G.mem_sample m f _).mpr ⟨hg e he,
      h _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩

noncomputable def badSampleProbability [Fintype W] (F : RGraph V r)
    (G : RGraph W r) (m : ℕ) : ℝ :=
  mean (fun f : Fin m → W => truth (∃ g : V → Fin m, F.IsHom (G.sample m f) g))

theorem badSampleProbability_nonneg [Fintype W] (F : RGraph V r)
    (G : RGraph W r) (m : ℕ) : 0 ≤ F.badSampleProbability G m :=
  mean_nonneg fun _ => truth_nonneg _

/-- An explicit uniform bound for the probability that a sampled template is
not F-hom-free. Its right-hand side tends to zero with host order. -/
theorem badSampleProbability_power_bound [Fintype V] [Fintype W] [Nonempty W]
    (F : RGraph V r) (G : RGraph W r) (m : ℕ) (hm : 0 < m)
    (hfree : ¬ ∃ f, F.IsEmbedding G f) :
    F.badSampleProbability G m ^ ((Fintype.card V + 1) ^ m) ≤
      (Fintype.card (V → Fin m) : ℝ) ^ ((Fintype.card V + 1) ^ m) *
        ((Fintype.card V : ℝ) ^ 2 / Fintype.card W) := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let k := (Fintype.card V + 1) ^ m
  have hk : 0 < k := Nat.pow_pos (by omega)
  let a (g : V → Fin m) : ℝ :=
    mean (fun f : Fin m → W => truth (F.IsHom (G.sample m f) g))
  have ha (g : V → Fin m) : 0 ≤ a g := mean_nonneg fun _ => truth_nonneg _
  have hpow (g : V → Fin m) : a g ^ k ≤
      (Fintype.card V : ℝ) ^ 2 / Fintype.card W := by
    by_cases hg : F.Noncollapsing g
    · have heq : a g = (F.imageGraph g hg).homDensity G := by
        apply mean_congr
        intro f
        unfold truth homIndicator
        rw [F.hom_sample_iff_image G g hg f]
        split <;> simp_all
      rw [heq]
      exact F.homImage_density_bound (F.imageGraph g hg) G hfree
        (F.imageGraph_hom g hg) (Fintype.card V + 1) (by omega) (by omega)
    · have heq : a g = 0 := by
        apply Eq.trans _ (mean_zero (α := Fin m → W))
        apply mean_congr
        intro f
        have hn : ¬ F.IsHom (G.sample m f) g := fun h =>
          hg (F.noncollapsing_of_sample_hom G h)
        simp [truth, hn]
      rw [heq, zero_pow (Nat.ne_of_gt hk)]
      positivity
  have hb : F.badSampleProbability G m ≤ (Fintype.card (V → Fin m) : ℝ) * mean a := by
    calc
      F.badSampleProbability G m ≤ mean (fun f : Fin m → W =>
          ∑ g : V → Fin m, truth (F.IsHom (G.sample m f) g)) := by
        apply mean_mono
        intro f
        by_cases hex : ∃ g, F.IsHom (G.sample m f) g
        · obtain ⟨g, hg⟩ := hex
          have he : truth (∃ g, F.IsHom (G.sample m f) g) =
              truth (F.IsHom (G.sample m f) g) := by
            simp [truth, hg, show ∃ g, F.IsHom (G.sample m f) g from ⟨g, hg⟩]
          rw [he]
          exact Finset.single_le_sum (fun h _ => truth_nonneg _) (Finset.mem_univ g)
        · simp only [truth]
          simp only [hex, ite_false]
          exact Finset.sum_nonneg fun g _ => by split <;> norm_num
      _ = ∑ g : V → Fin m, a g := Finset.expect_sum_comm _ _ _
      _ = (Fintype.card (V → Fin m) : ℝ) * mean a :=
        (Fintype.card_mul_expect a).symm
  have hpavg : mean a ^ k ≤ (Fintype.card V : ℝ) ^ 2 / Fintype.card W := by
    calc
      mean a ^ k ≤ mean (fun g => a g ^ k) := mean_pow_le a ha k
      _ ≤ mean (fun _g : V → Fin m =>
          (Fintype.card V : ℝ) ^ 2 / Fintype.card W) := mean_mono hpow
      _ = _ := mean_const _
  calc
    F.badSampleProbability G m ^ k ≤
        ((Fintype.card (V → Fin m) : ℝ) * mean a) ^ k :=
      pow_le_pow_left₀ (F.badSampleProbability_nonneg G m) hb k
    _ = (Fintype.card (V → Fin m) : ℝ) ^ k * mean a ^ k := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hpavg (by positivity)

end TuranUniversality.RGraph
