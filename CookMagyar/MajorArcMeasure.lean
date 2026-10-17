module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.ArcGeometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.CookMagyarArcs

/-! # Measure bounds for cubic major arcs

The circle projection handles arcs that wrap around the endpoints of the
chosen fundamental interval. Counting reduced centers coarsely by `(Q+1)^2`
then gives the expected cubic-scale volume bound.
-/

/-- One clipped circle arc has volume at most twice its radius. -/
theorem volume_majorArcAt_le_two_radius (N Q a q : ℕ) :
    volume (majorArcAt N Q a q) ≤
      ENNReal.ofReal (2 * cubicArcRadius N Q) := by
  let c : UnitAddCircle := rationalCenter a q
  let s : Set ℝ := (fun alpha : ℝ => (alpha : UnitAddCircle)) ⁻¹'
    Metric.closedBall c (cubicArcRadius N Q)
  have hs : MeasurableSet (Metric.closedBall c (cubicArcRadius N Q)) :=
    measurableSet_closedBall
  have hcircle :
      volume (Metric.closedBall c (cubicArcRadius N Q)) =
        volume (s ∩ Set.Ioc (0 : ℝ) 1) := by
    simpa [s] using AddCircle.add_projection_respects_measure 1 0 hs
  have hinterval : volume (s ∩ Set.Ioc (0 : ℝ) 1) =
      volume (s ∩ Set.Icc (0 : ℝ) 1) := by
    have hres := restrict_Ioc_eq_restrict_Icc
      (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
    simpa [Measure.restrict_apply measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Icc, Set.inter_comm] using
      congrArg (fun μ : Measure ℝ => μ s) hres
  have hsub : majorArcAt N Q a q ⊆ s ∩ Set.Icc (0 : ℝ) 1 := by
    intro alpha halpha
    refine ⟨?_, halpha.1⟩
    change dist (alpha : UnitAddCircle) c ≤ cubicArcRadius N Q
    exact le_of_lt halpha.2
  calc
    volume (majorArcAt N Q a q) ≤
        volume (s ∩ Set.Icc (0 : ℝ) 1) := measure_mono hsub
    _ = volume (Metric.closedBall c (cubicArcRadius N Q)) :=
      hinterval.symm.trans hcircle.symm
    _ = ENNReal.ofReal (min (1 : ℝ) (2 * cubicArcRadius N Q)) := by
      simpa [c] using AddCircle.volume_closedBall 1 (cubicArcRadius N Q)
    _ ≤ ENNReal.ofReal (2 * cubicArcRadius N Q) :=
      ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- Real-valued measure version of the individual clipped-arc bound. -/
theorem volume_real_majorArcAt_le_two_radius (N Q a q : ℕ) :
    volume.real (majorArcAt N Q a q) ≤ 2 * cubicArcRadius N Q := by
  have htop : ENNReal.ofReal (2 * cubicArcRadius N Q) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop
    (volume_majorArcAt_le_two_radius N Q a q)
  have hradius : 0 ≤ 2 * cubicArcRadius N Q := by
    unfold cubicArcRadius
    positivity
  rw [ENNReal.toReal_ofReal hradius] at hreal
  simpa only [Measure.real] using hreal

/-- The reduced centers are bounded by the square of the denominator range. -/
theorem majorArcCenters_card_le_square (Q : ℕ) :
    (majorArcCenters_finite Q).toFinset.card ≤ (Q + 1) ^ 2 := by
  classical
  have hsub : (majorArcCenters_finite Q).toFinset ⊆
      Finset.range (Q + 1) ×ˢ Finset.range (Q + 1) := by
    intro aq haq
    have hcenter : aq ∈ majorArcCenters Q := by simpa using haq
    rcases aq with ⟨a, q⟩
    rcases hcenter with ⟨hqQ, _hq0, haq, _hcop⟩
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  calc
    (majorArcCenters_finite Q).toFinset.card ≤
        (Finset.range (Q + 1) ×ˢ Finset.range (Q + 1)).card :=
      Finset.card_le_card hsub
    _ = (Q + 1) ^ 2 := by simp [Finset.card_product, pow_two]

/-- Total major-arc volume has the correct `Q³/N³` scale. -/
theorem volume_majorArcs_le_center_count_mul_radius (N Q : ℕ) :
    volume (majorArcs N Q) ≤
      ((Q + 1) ^ 2 : ℕ) * ENNReal.ofReal (2 * cubicArcRadius N Q) := by
  classical
  let F := (majorArcCenters_finite Q).toFinset
  have hF : ∀ aq, aq ∈ F ↔ aq ∈ majorArcCenters Q := by
    intro aq
    simp [F]
  have hset : majorArcs N Q =
      ⋃ aq ∈ F, majorArcAt N Q aq.1 aq.2 := by
    rw [majorArcs_eq_iUnion_majorArcAt]
    simp only [← hF]
  rw [hset]
  calc
    volume (⋃ aq ∈ F, majorArcAt N Q aq.1 aq.2) ≤
        ∑ aq ∈ F, volume (majorArcAt N Q aq.1 aq.2) :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _aq ∈ F, ENNReal.ofReal (2 * cubicArcRadius N Q) := by
      apply Finset.sum_le_sum
      intro aq _haq
      exact volume_majorArcAt_le_two_radius N Q aq.1 aq.2
    _ = (F.card : ℕ) * ENNReal.ofReal (2 * cubicArcRadius N Q) := by
      simp
    _ ≤ ((Q + 1) ^ 2 : ℕ) * ENNReal.ofReal (2 * cubicArcRadius N Q) := by
      gcongr
      exact majorArcCenters_card_le_square Q

/-- Real-valued major-arc volume bound for integral estimates. -/
theorem volume_real_majorArcs_le_center_count_mul_radius (N Q : ℕ) :
    volume.real (majorArcs N Q) ≤
      ((Q + 1 : ℕ) ^ 2 : ℝ) * (2 * cubicArcRadius N Q) := by
  have hr : 0 ≤ cubicArcRadius N Q := by
    unfold cubicArcRadius
    positivity
  have hbound := volume_majorArcs_le_center_count_mul_radius N Q
  have htop :
      ((Q + 1) ^ 2 : ℕ) * ENNReal.ofReal (2 * cubicArcRadius N Q) ≠ ∞ := by
    finiteness
  have hreal := ENNReal.toReal_mono htop hbound
  have hr2 : 0 ≤ 2 * cubicArcRadius N Q := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hr2] at hreal
  simpa only [Measure.real, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    using hreal

end SystolicGrowth.CookMagyarArcs
