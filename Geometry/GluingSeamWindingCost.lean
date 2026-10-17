module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamAngularLift
public import Geometry.RealLocalGeodesicNonclosure

@[expose] public section

/-!
# Systolic cost of actual seam-confined local metric loops

The actual continuous angular lift preserves metric variation. Positive
local speed rules out a closed real lift, while equality of the native loop
endpoints forces an integer angular period. Its nonzero period pays at least
the seam circumference, which is exactly the original target systole.
-/

open Set Metric
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem two_pi_le_abs_sub_of_exp_eq {x y : ℝ}
    (he : Circle.exp x = Circle.exp y) (hne : x ≠ y) :
    2 * Real.pi ≤ |x - y| := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
  have hmne : m ≠ 0 := by
    intro h
    exact hne (by simpa only [h, Int.cast_zero, zero_mul, add_zero] using hm)
  have hcast : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hmne
  have hsub : x - y = (m : ℝ) * (2 * Real.pi) := by linarith [hm]
  rw [hsub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcast
    (show 0 ≤ 2 * Real.pi by positivity)

/-- Every closed positive-speed local metric segment confined to an actual
seam pays the full target systole. The angular lift and its nonzero integer
period are constructed internally, not supplied as winding assumptions. -/
theorem targetSystole_le_variation_of_closed_local_metric_segment_in_seam
    (P : ExerciseGluingPreparation C g n genera X) {a b speed : ℝ}
    (hab : a < b) (hs : 0 < speed) (k : Fin (n - 1))
    (β : Icc a b → P.GluedCarrier) (hβ : Continuous β)
    (hclosed : β ⟨a, le_rfl, hab.le⟩ = β ⟨b, hab.le, le_rfl⟩)
    (hseam : ∀ t, β t ∈ P.gluedSeamCircle k)
    (hlocal :
      letI := P.gluedCarrierIntrinsicMetricSpace
      ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
        ∀ u v : Icc a b, dist u t < η → dist v t < η →
          dist (β u) (β v) = speed * |(u : ℝ) - (v : ℝ)|) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤ eVariationOn β univ := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨α, hα, hmetric, hvariation, hexp⟩ :=
    P.exists_continuous_seam_angular_lift k hab β hβ hseam
  let w : Icc a b → ℝ := fun t => Real.sinh (gluingRadius C g) * α t
  have hw : Continuous w := continuous_const.mul hα
  have hwarp : 0 < Real.sinh (gluingRadius C g) := Real.sinh_pos_iff.mpr P.radius_pos
  have hwdist (u v : Icc a b) :
      dist (w u) (w v) = Real.sinh (gluingRadius C g) * |α u - α v| := by
    rw [Real.dist_eq]
    change |Real.sinh (gluingRadius C g) * α u - Real.sinh (gluingRadius C g) * α v| = _
    rw [← mul_sub, abs_mul, abs_of_pos hwarp]
  have hwlocal : ∀ t : Icc a b, a < t.1 → t.1 < b → ∃ η > 0,
      ∀ u v : Icc a b, dist u t < η → dist v t < η →
        dist (w u) (w v) = speed * |(u : ℝ) - (v : ℝ)| := by
    intro t hta htb
    obtain ⟨η₁, hη₁, hm⟩ := hmetric t hta htb
    obtain ⟨η₂, hη₂, hl⟩ := hlocal t hta htb
    refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
    intro u v hu hv
    rw [hwdist u v, ← hm u v (hu.trans_le (min_le_left _ _))
      (hv.trans_le (min_le_left _ _))]
    exact hl u v (hu.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))
  let s : Icc a b := ⟨a, le_rfl, hab.le⟩
  let t : Icc a b := ⟨b, hab.le, le_rfl⟩
  have hwne : w s ≠ w t := real_locally_metric_segment_endpoints_ne hab hs w hw hwlocal
  have hαne : α s ≠ α t := fun h => hwne (congrArg (fun q => Real.sinh (gluingRadius C g) * q) h)
  have hperiod := two_pi_le_abs_sub_of_exp_eq (hexp s t hclosed) hαne
  have hcircum : Real.sinh (gluingRadius C g) * (2 * Real.pi) = targetSystole C g := by
    rw [gluingRadius, Real.sinh_arsinh]
    exact div_mul_cancel₀ _ (by positivity)
  calc
    ENNReal.ofReal (targetSystole C g) ≤ edist (w s) (w t) := by
      rw [edist_dist, hwdist s t]
      apply ENNReal.ofReal_le_ofReal
      rw [← hcircum]
      exact mul_le_mul_of_nonneg_left hperiod hwarp.le
    _ ≤ eVariationOn w univ := eVariationOn.edist_le w (mem_univ s) (mem_univ t)
    _ = eVariationOn β univ := hvariation.symm

#print axioms targetSystole_le_variation_of_closed_local_metric_segment_in_seam

end SystolicGrowth.ExerciseGluingPreparation
