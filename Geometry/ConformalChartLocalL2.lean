module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalChartIntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Local coordinate `L²` from the actual conformal area law

An `L²` function for the original surface measure pulls back to ordinary
Euclidean `L²` on every compact subset of a genuine conformal chart.
The proof uses the exact area measure, followed by the strictly positive
minimum of its smooth density. No local-integrability premise is added.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology ENNReal

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Math.** The original area law transports actual `Lᵖ` functions to
the chart with its literal conformal density. -/
theorem conformalChart_memLp_weighted
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hUs : U ⊆ e.source) (a : ℂ → ℝ)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    {F : M → ℝ} {p : ℝ≥0∞} (hF : MemLp F p μ)
    (s : Set ℂ) (hs : MeasurableSet s) (hsU : s ⊆ e '' U) :
    MemLp (fun z => F (e.symm z)) p
      ((volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2))).restrict s) := by
  have hst : s ⊆ e.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hsU hz
    exact e.map_source (hUs hx)
  let q : s → M := fun z => e.symm z.1
  have hq : MeasurableEmbedding q :=
    (e.symm.continuousOn.mono hst).measurableEmbedding hs (e.symm.injOn.mono hst)
  have hv : MeasurableEmbedding (Subtype.val : s → ℂ) :=
    MeasurableEmbedding.subtype_coe hs
  let ν : Measure ℂ := volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2))
  have hmeasure : μ.comap q = ν.comap (Subtype.val : s → ℂ) := by
    ext t ht
    rw [hq.comap_apply, hv.comap_apply]
    have himage : q '' t = e.symm '' ((Subtype.val : s → ℂ) '' t) := by
      rw [image_image]
    rw [himage, harea _ (hv.measurableSet_image.2 ht)
      ((Subtype.coe_image_subset s t).trans hsU)]
    exact (withDensity_apply _ (hv.measurableSet_image.2 ht)).symm
  have hFq : MemLp (fun z : s => F (q z)) p (μ.comap q) := by
    apply hq.memLp_map_measure_iff.mp
    rw [hq.map_comap]
    exact hF.restrict _
  rw [hmeasure] at hFq
  have hvrange : range (Subtype.val : s → ℂ) = s := by
    ext z
    simp
  change MemLp (fun z => F (e.symm z)) p (ν.restrict s)
  rw [← hvrange, ← hv.map_comap ν]
  exact hv.memLp_map_measure_iff.mpr hFq

/-- **Math.** On compact coordinate subsets, the positive metric density
has a positive minimum, so a surface `L²` function is Euclidean `L²`. -/
theorem conformalChart_memLp_on_isCompact
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    {F : M → ℝ} (hF : MemLp F 2 μ)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ e '' U) :
    MemLp (fun z => F (e.symm z)) 2 (volume.restrict K) := by
  by_cases hKn : K.Nonempty
  swap
  · simp [Set.not_nonempty_iff_eq_empty.mp hKn]
  have hKt : K ⊆ e.target := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hKU hz
    exact e.map_source (hUs hx)
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKn ((ha.mono hKt).pow 2)
  have hden : a z₀ ^ 2 ≠ 0 := pow_ne_zero _ (hapos z₀ (hKt hz₀)).ne'
  let c : ℝ := (a z₀ ^ 2)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (sq_nonneg _)
  have hlower : ∀ z ∈ K, 1 ≤ c * a z ^ 2 := by
    intro z hz
    calc
      1 = c * a z₀ ^ 2 := by simp [c, hden]
      _ ≤ c * a z ^ 2 := mul_le_mul_of_nonneg_left (hmin hz) hc
  have hdensity : (volume.restrict K).withDensity (fun _ => (1 : ℝ≥0∞)) ≤
      (volume.restrict K).withDensity
        (fun z => ENNReal.ofReal c * ENNReal.ofReal (a z ^ 2)) := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    rw [← ENNReal.ofReal_mul hc]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hlower z hz)
  have hmeasure : volume.restrict K ≤ ENNReal.ofReal c •
      ((volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2))).restrict K) := by
    rw [restrict_withDensity hK.measurableSet]
    convert hdensity using 1
    · simp
    · exact (withDensity_smul' (ENNReal.ofReal c)
        (fun z => ENNReal.ofReal (a z ^ 2)) ENNReal.ofReal_ne_top).symm
  exact MemLp.of_measure_le_smul ENNReal.ofReal_ne_top hmeasure
    (conformalChart_memLp_weighted μ e U hUs a harea hF K hK.measurableSet hKU)

/-- **Math.** Continuous coordinate multipliers preserve the local `L²`
space, in particular the factor `a / τ` wherever `τ` is nonzero. -/
theorem conformalChart_memLp_on_isCompact_mul
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    {F : M → ℝ} (hF : MemLp F 2 μ)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ e '' U)
    (b : ℂ → ℝ) (hb : ContinuousOn b K) :
    MemLp (fun z => b z * F (e.symm z)) 2 (volume.restrict K) := by
  have hf := conformalChart_memLp_on_isCompact μ e U hUs a ha hapos harea hF K hK hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hb
  have hbtop : MemLp b ∞ (volume.restrict K) :=
    memLp_top_of_bound (hb.aestronglyMeasurable hK.measurableSet) C
      ((ae_restrict_mem hK.measurableSet).mono fun z hz => hC z hz)
  exact hbtop.fun_mul hf

#print axioms conformalChart_memLp_weighted
#print axioms conformalChart_memLp_on_isCompact
#print axioms conformalChart_memLp_on_isCompact_mul

end

end SystolicGrowth
