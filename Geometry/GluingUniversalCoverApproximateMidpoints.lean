module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverPathMetric
public import Geometry.MetricLoopArclength

@[expose] public section

/-!
# Approximate midpoints in the native glued universal cover

Finite-length paths in the native cover admit continuous cumulative-length
coordinates. Applying the intermediate value theorem to this coordinate gives
approximate midpoints for the actual path metric, without assuming geodesics or
properness.
-/

open Set
open scoped unitInterval ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual native glued universal cover has approximate midpoints: choose
a path whose variation is nearly the intrinsic distance, then take the point
at half its cumulative variation. -/
theorem exists_gluedUniversalCover_approximate_midpoint
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) (ε : ℝ) (hε : 0 < ε) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    ∃ z : P.basedTopologicalUniversalCover x,
      dist e z ≤ dist e f / 2 + ε ∧ dist z f ≤ dist e f / 2 + ε := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  have hεne : ENNReal.ofReal ε ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hε
  have hedne : edist e f ≠ ∞ := edist_ne_top e f
  have hlt : edist e f < edist e f + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hedne hεne
  have hInf : (⨅ Γ : Path e f, eVariationOn Γ univ) <
      edist e f + ENNReal.ofReal ε := by
    rw [← P.gluedUniversalCoverPathMetric_edist_eq_iInf_variation x e f]
    exact hlt
  obtain ⟨Γ, hΓ⟩ := (iInf_lt_iff).mp hInf
  have hsumTop : edist e f + ENNReal.ofReal ε < ∞ := by
    finiteness
  have hvarTop : eVariationOn Γ univ < ∞ := hΓ.trans hsumTop
  have hfin : BoundedVariationOn Γ univ := ne_of_lt hvarTop
  let L : ℝ := (eVariationOn Γ univ).toReal
  let V : unitInterval → ℝ := metricVariationCoordinate Γ.toContinuousMap
  have hVcont : Continuous V :=
    metricVariationCoordinate_continuous_of_boundedVariation Γ.toContinuousMap hfin
  have hVzero : V 0 = 0 := metricVariationCoordinate_zero Γ.toContinuousMap
  have hVone : V 1 = L := metricVariationCoordinate_one Γ.toContinuousMap
  have hLnonneg : 0 ≤ L := ENNReal.toReal_nonneg
  have hhalfRange : L / 2 ∈ Icc (0 : ℝ) L := by
    constructor <;> linarith
  have hVrange : Icc (0 : ℝ) L ⊆ Set.range V := by
    simpa only [hVzero, hVone] using
      (intermediate_value_univ (0 : unitInterval) 1 (f := V) hVcont)
  obtain ⟨t, ht⟩ := hVrange hhalfRange
  let z : P.basedTopologicalUniversalCover x := Γ t
  have hleft := dist_le_metricVariationCoordinate_sub_of_boundedVariation
    Γ.toContinuousMap hfin (0 : unitInterval) t
  have hVt : metricVariationCoordinate Γ.toContinuousMap t = L / 2 := by
    simpa [V] using ht
  have hleft' : dist e z ≤ L / 2 := by
    change dist (Γ 0) (Γ t) ≤ |V 0 - V t| at hleft
    rw [Γ.source, hVzero, ht] at hleft
    have hhalfNonneg : 0 ≤ L / 2 := by linarith
    have habs : |(0 : ℝ) - L / 2| = L / 2 := by
      rw [zero_sub, abs_neg, abs_of_nonneg hhalfNonneg]
    rw [habs] at hleft
    simpa [z] using hleft
  have hright := dist_le_metricVariationCoordinate_sub_of_boundedVariation
    Γ.toContinuousMap hfin t (1 : unitInterval)
  have hright' : dist z f ≤ L / 2 := by
    change dist (Γ t) (Γ 1) ≤ |V t - V 1| at hright
    rw [ht, hVone, Γ.target] at hright
    have habs : |L / 2 - L| = L / 2 := by
      rw [abs_of_nonpos (show L / 2 - L ≤ 0 by linarith)]
      ring
    rw [habs] at hright
    simpa [z] using hright
  have hrealStrict : L < (edist e f + ENNReal.ofReal ε).toReal :=
    (ENNReal.toReal_lt_toReal (ne_of_lt hvarTop) (ne_of_lt hsumTop)).2 hΓ
  have hLbound : L < dist e f + ε := by
    rw [ENNReal.toReal_add hedne ENNReal.ofReal_ne_top] at hrealStrict
    simpa [L, edist_dist, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist e f),
      ENNReal.toReal_ofReal hε.le] using hrealStrict
  refine ⟨z, ?_, ?_⟩ <;> linarith

#print axioms exists_gluedUniversalCover_approximate_midpoint

end SystolicGrowth.ExerciseGluingPreparation
