module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingEssentialLoopCompactness
public import Geometry.MetricLoopArclength

@[expose] public section

/-!
# Actual arclength-normalized essential-loop minima

The compact essential common-speed family has a positive finite minimum.
Arclength normalization preserves its essentiality and variation while
reducing its speed bound to its actual length. Saturation of the total
variation then fixes the variation on every subinterval. Local shortening,
including at the closing join, is still needed to prove local geodesicity.
-/

open Set
open scoped Topology unitInterval NNReal ENNReal

namespace SystolicGrowth

/-- Saturating the unit-time Lipschitz variation bound fixes variation on
every subinterval, including for rebased normalized minima. -/
theorem subinterval_variation_eq_of_saturated_lipschitz
    {M : Type*} [MetricSpace M] (f : C(unitInterval, M)) {K : ℝ≥0}
    (hf : LipschitzWith K f) (htotal : eVariationOn f univ = (K : ℝ≥0∞))
    {s t : unitInterval} (hst : s ≤ t) :
    eVariationOn f (Icc s t) = ENNReal.ofReal ((K : ℝ) * ((t : ℝ) - s)) := by
  let V := metricVariationCoordinate f
  have hVlip : LipschitzWith K V := metricVariationCoordinate_lipschitz f hf
  have hVmono : Monotone V := metricVariationCoordinate_monotone f hf
  have hV0 : V 0 = 0 := metricVariationCoordinate_zero f
  have hV1 : V 1 = (K : ℝ) := by
    rw [show V 1 = (eVariationOn f univ).toReal from metricVariationCoordinate_one f,
      htotal, ENNReal.coe_toReal]
  have hV (u : unitInterval) : V u = (K : ℝ) * u := by
    have hu0 : 0 ≤ (u : ℝ) := u.property.1
    have hu1 : (u : ℝ) ≤ 1 := u.property.2
    have hnonneg : 0 ≤ V u := by
      simpa only [hV0] using hVmono (show (0 : unitInterval) ≤ u from u.property.1)
    have hleK : V u ≤ (K : ℝ) := by
      simpa only [hV1] using hVmono (show u ≤ (1 : unitInterval) from u.property.2)
    have hupper : V u ≤ (K : ℝ) * u := by
      simpa only [Real.dist_eq, hV0, sub_zero, abs_of_nonneg hnonneg,
        Subtype.dist_eq, Set.Icc.coe_zero, abs_of_nonneg hu0] using
        hVlip.dist_le_mul u 0
    have hlower : (K : ℝ) - V u ≤ (K : ℝ) * (1 - u) := by
      simpa only [Real.dist_eq, hV1, abs_of_nonneg (sub_nonneg.mpr hleK),
        Subtype.dist_eq, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.mpr hu1)] using
        hVlip.dist_le_mul 1 u
    linarith
  have hfinite : eVariationOn f (Icc s t) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [htotal]; simp)
      (eVariationOn.mono f (subset_univ _))
  rw [← ENNReal.ofReal_toReal hfinite, ← metricVariationCoordinate_sub_eq f hf hst]
  change ENNReal.ofReal (V t - V s) = _
  rw [hV t, hV s]
  congr 1
  ring

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A nonempty common-Lipschitz essential-loop family has an essential
arclength-normalized minimum, at any native basepoint, with actual positive
length and exact subinterval variation. This does not assert geodesicity. -/
theorem exists_arclength_minimizing_essential_loop
    (P : ExerciseGluingPreparation C g n genera X) (K : ℝ≥0)
    (f₀ : closedLoopMapSet P.GluedCarrier)
    (hLip : letI := P.gluedCarrierIntrinsicMetricSpace; LipschitzWith K f₀.1)
    (hessential : ¬(closedLoopPath f₀).Homotopic (Path.refl (f₀.1 0))) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ l : ℝ, ∃ hl : 0 < l, ∃ f : closedLoopMapSet P.GluedCarrier,
      l ≤ K ∧ LipschitzWith ⟨l, hl.le⟩ f.1 ∧
      ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0)) ∧
      eVariationOn f.1 univ = ENNReal.ofReal l ∧
      (∀ s t : unitInterval, s ≤ t →
        eVariationOn f.1 (Icc s t) = ENNReal.ofReal (l * ((t : ℝ) - s))) ∧
      ∀ h : closedLoopMapSet P.GluedCarrier, LipschitzWith K h.1 →
        ¬(closedLoopPath h).Homotopic (Path.refl (h.1 0)) →
        ENNReal.ofReal l ≤ eVariationOn h.1 univ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨f, hfLip, hfEss, hfPos, hfBound, hfMin⟩ :=
    P.exists_minimizing_essential_lipschitz_loop K f₀ hLip hessential
  have hfFinite : eVariationOn f.1 univ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hfBound
  let l := (eVariationOn f.1 univ).toReal
  have hl : 0 < l := ENNReal.toReal_pos hfPos.ne' hfFinite
  have hlK : l ≤ (K : ℝ) := by
    simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono (by simp) hfBound
  obtain ⟨a, hbase, haLip, haVariation, hhomotopic⟩ :=
    exists_lipschitz_arclength_closedLoop f hfLip hl
  have haEss : ¬(closedLoopPath a).Homotopic (Path.refl (a.1 0)) := by
    intro haNull
    have hcast := haNull.pathCast hbase hbase
    have hrefl : (Path.refl (a.1 0)).cast hbase hbase = Path.refl (f.1 0) := by
      apply Path.ext
      funext t
      exact hbase.symm
    rw [hrefl] at hcast
    exact hfEss (hhomotopic.trans hcast)
  have haLength : eVariationOn a.1 univ = ENNReal.ofReal l :=
    haVariation.trans (ENNReal.ofReal_toReal hfFinite).symm
  have haTotal : eVariationOn a.1 univ = ENNReal.ofNNReal (NNReal.mk l hl.le) := by
    rw [haLength, ENNReal.ofReal_eq_coe_nnreal hl.le]
  refine ⟨l, hl, a, hlK, haLip, haEss, haLength, ?_, ?_⟩
  · exact fun s t hst => subinterval_variation_eq_of_saturated_lipschitz a.1 haLip haTotal hst
  · intro h hL hE
    exact (ENNReal.ofReal_toReal hfFinite).le.trans (hfMin h hL hE)

end ExerciseGluingPreparation

end SystolicGrowth
