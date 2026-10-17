module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingEssentialLoopShortening
public import Geometry.ClosedLoopRebase
public import Geometry.GluingClosedLocalGeodesicCost

@[expose] public section

/-!
# Periodic essential-loop minima and the native systole bound

Every rotation of the actual normalized minimum satisfies the same local
shortening argument. Testing its middle parameter supplies a real local
metric law at any point of the fixed periodic extension, including every
closing join. The proved periodic geodesic estimate then pays the target.
-/

open Set
open scoped Topology unitInterval NNReal ENNReal

namespace SystolicGrowth

private theorem closedLoopPeriodicExtension_locally_metric_of_rebased_midpoint_laws
    {M : Type*} [MetricSpace M] (f : closedLoopMapSet M) (l : ℝ)
    (hlocal : ∀ s : unitInterval, ∃ δ > 0, ∀ u v : unitInterval,
      |(u : ℝ) - 1 / 2| < δ → |(v : ℝ) - 1 / 2| < δ →
        dist ((closedLoopRebase f s).1 u) ((closedLoopRebase f s).1 v) =
          l * |(u : ℝ) - v|) :
    ∀ t : ℝ, ∃ η > 0, ∀ u v : ℝ, dist u t < η → dist v t < η →
      dist (closedLoopPeriodicExtension f u) (closedLoopPeriodicExtension f v) =
        l * |u - v| := by
  intro t
  let n : ℤ := ⌊t - 1 / 2⌋
  let s : unitInterval :=
    ⟨Int.fract (t - 1 / 2), Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨δ, hδ, hmetric⟩ := hlocal s
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), ?_⟩
  intro u v hut hvt
  have hu : |u - t| < min δ (1 / 2) := by simpa only [Real.dist_eq] using hut
  have hv : |v - t| < min δ (1 / 2) := by simpa only [Real.dist_eq] using hvt
  have hU : u - t + 1 / 2 ∈ Icc (0 : ℝ) 1 := by
    have h := abs_lt.mp (hu.trans_le (min_le_right _ _))
    constructor <;> linarith [h.1, h.2]
  have hV : v - t + 1 / 2 ∈ Icc (0 : ℝ) 1 := by
    have h := abs_lt.mp (hv.trans_le (min_le_right _ _))
    constructor <;> linarith [h.1, h.2]
  let U : unitInterval := ⟨u - t + 1 / 2, hU⟩
  let V : unitInterval := ⟨v - t + 1 / 2, hV⟩
  have hnearU : |(U : ℝ) - 1 / 2| < δ := by
    change |(u - t + 1 / 2) - 1 / 2| < δ
    simpa only [add_sub_cancel_right] using hu.trans_le (min_le_left _ _)
  have hnearV : |(V : ℝ) - 1 / 2| < δ := by
    change |(v - t + 1 / 2) - 1 / 2| < δ
    simpa only [add_sub_cancel_right] using hv.trans_le (min_le_left _ _)
  have hUeval : (closedLoopRebase f s).1 U = closedLoopPeriodicExtension f u := by
    rw [closedLoopRebase_apply]
    have hparam : (s : ℝ) + (U : ℝ) = u - (n : ℝ) := by
      change Int.fract (t - 1 / 2) + (u - t + 1 / 2) = u - (⌊t - 1 / 2⌋ : ℝ)
      rw [Int.fract]
      ring
    rw [hparam]
    simpa only [mul_one] using
      (closedLoopPeriodicExtension_periodic f).sub_int_mul_eq (x := u) n
  have hVeval : (closedLoopRebase f s).1 V = closedLoopPeriodicExtension f v := by
    rw [closedLoopRebase_apply]
    have hparam : (s : ℝ) + (V : ℝ) = v - (n : ℝ) := by
      change Int.fract (t - 1 / 2) + (v - t + 1 / 2) = v - (⌊t - 1 / 2⌋ : ℝ)
      rw [Int.fract]
      ring
    rw [hparam]
    simpa only [mul_one] using
      (closedLoopPeriodicExtension_periodic f).sub_int_mul_eq (x := v) n
  have h := hmetric U V hnearU hnearV
  rw [hUeval, hVeval] at h
  have hdiff : (U : ℝ) - (V : ℝ) = u - v := by
    change (u - t + 1 / 2) - (v - t + 1 / 2) = u - v
    ring
  simpa only [hdiff] using h

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every actual essential Lipschitz closed loop pays the target systole.
The normalized minimum has a genuine real periodic local law across every
join, constructed by applying shortening to its actual rotations. -/
theorem targetSystole_le_variation_of_essential_lipschitz_loop
    (P : ExerciseGluingPreparation C g n genera X) (K : ℝ≥0)
    (f₀ : closedLoopMapSet P.GluedCarrier)
    (hLip : letI := P.gluedCarrierIntrinsicMetricSpace; LipschitzWith K f₀.1)
    (hessential : ¬(closedLoopPath f₀).Homotopic (Path.refl (f₀.1 0))) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn f₀.1 univ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨l, hl, f, hlK, hfLip, hfEssential, hfLength, _hfVariation, hmin⟩ :=
    P.exists_arclength_minimizing_essential_loop K f₀ hLip hessential
  have hmidlocal : ∀ s : unitInterval, ∃ δ > 0, ∀ u v : unitInterval,
      |(u : ℝ) - 1 / 2| < δ → |(v : ℝ) - 1 / 2| < δ →
        dist ((closedLoopRebase f s).1 u) ((closedLoopRebase f s).1 v) =
          l * |(u : ℝ) - v| := by
    intro s
    let R := closedLoopRebase f s
    have hRLip : LipschitzWith ⟨l, hl.le⟩ R.1 := closedLoopRebase_lipschitz f s hfLip
    have hREssential : ¬(closedLoopPath R).Homotopic (Path.refl (R.1 0)) := by
      intro hnull
      exact hfEssential ((closedLoopRebase_nullhomotopic_iff f s).mp hnull)
    have hRTotal : eVariationOn R.1 univ = ENNReal.ofNNReal (NNReal.mk l hl.le) :=
      (closedLoopRebase_eVariationOn f s).trans
        (hfLength.trans (ENNReal.ofReal_eq_coe_nnreal hl.le))
    have hRVariation (a b : unitInterval) (hab : a ≤ b) :
        eVariationOn R.1 (Icc a b) = ENNReal.ofReal (l * ((b : ℝ) - a)) :=
      subinterval_variation_eq_of_saturated_lipschitz R.1 hRLip hRTotal hab
    let c : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
    exact P.arclength_minimizing_essential_loop_locally_metric
      K l hl hlK R hRLip hREssential hRVariation hmin c
      (by norm_num [c]) (by norm_num [c])
  have hlocal := closedLoopPeriodicExtension_locally_metric_of_rebased_midpoint_laws f l hmidlocal
  have hpay := P.targetSystole_le_variation_of_periodic_local_metric_geodesic
    (show (0 : ℝ) < 1 by norm_num) hl (closedLoopPeriodicExtension f)
    (closedLoopPeriodicExtension_continuous f) (closedLoopPeriodicExtension_periodic f) hlocal
  have hperiodLength := (closedLoopPeriodicExtension_eVariationOn f).trans hfLength
  exact hpay.trans (hperiodLength.le.trans (hmin f₀ hLip hessential))

#print axioms targetSystole_le_variation_of_essential_lipschitz_loop

end ExerciseGluingPreparation

end SystolicGrowth
