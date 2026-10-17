module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SmoothSquaredPartition
public import Mathlib.MeasureTheory.Measure.Restrict

@[expose] public section

/-!
# Gluing local classical representatives on the original smooth carrier

A finite smooth square partition combines local representatives into one
global representative of the same measurable function. The proof works at
every finite differentiability order as well as at smooth order, and needs
no prior equality of local representatives on chart overlaps.
-/

open Set Filter Manifold MeasureTheory
open scoped ContDiff Topology

namespace SystolicGrowth

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℝ, ℂ) ∞ M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Math.** Local classical representatives of the same measured
function glue to a global representative by a constructed finite smooth
partition. Every overlap and almost-everywhere identity is handled in the
original carrier and measure. -/
theorem exists_contMDiff_ae_eq_of_local_representatives
    (μ : Measure M) (u : M → ℝ) (r : ℕ∞ω) (hr : r ≤ ∞)
    (U : M → Set M) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (f : M → M → ℝ)
    (hf : ∀ x, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) r (f x) (U x))
    (hfae : ∀ x, f x =ᵐ[μ.restrict (U x)] u) :
    ∃ v : M → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) r v ∧ v =ᵐ[μ] u := by
  classical
  obtain ⟨N, c, τ, hτs, _, hsum⟩ := exists_smoothSquareCover_subordinate U
    (fun x => (hU x).mem_nhds (hxU x))
  let F (i : Fin N) (x : M) : ℝ := (τ i x) ^ 2 * f (c i) x
  have hFs (i : Fin N) : tsupport (F i) ⊆ tsupport (τ i) := by
    apply closure_mono
    intro x hx
    change τ i x ≠ 0
    intro hz
    exact hx (by simp [F, hz])
  have hF (i : Fin N) : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) r (F i) := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU' : x ∈ U (c i) := hτs i (hFs i hx)
    exact (((τ i).contMDiff.of_le hr x).pow 2).mul
      ((hf (c i)).contMDiffAt ((hU (c i)).mem_nhds hxU'))
  have hFae (i : Fin N) : F i =ᵐ[μ] fun x => (τ i x) ^ 2 * u x := by
    have hae := (ae_restrict_iff' (hU (c i)).measurableSet).mp (hfae (c i))
    filter_upwards [hae] with x hx
    by_cases hxU' : x ∈ U (c i)
    · exact congrArg (fun y => (τ i x) ^ 2 * y) (hx hxU')
    · have hτzero : τ i x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro ht
        exact hxU' (hτs i ht)
      simp [F, hτzero]
  refine ⟨fun x => ∑ i, F i x, contMDiff_finsetSum (fun i _ => hF i), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ i : Fin N, F i x = (τ i x) ^ 2 * u x :=
    ae_all_iff.mpr hFae
  filter_upwards [hall] with x hx
  calc
    (∑ i, F i x) = ∑ i, (τ i x) ^ 2 * u x := Finset.sum_congr rfl (fun i _ => hx i)
    _ = u x := by rw [← Finset.sum_mul, hsum, one_mul]

#print axioms exists_contMDiff_ae_eq_of_local_representatives

end

end SystolicGrowth
