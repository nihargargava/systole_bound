module

public import Geometry.HyperbolicParameters

@[expose] public section

open Filter Set UpperHalfPlane
open scoped MatrixGroups Pointwise Topology UpperHalfPlane

namespace SystolicGrowth

/-! ## Separation parameters for chain gluing

An internal component of a chain needs two centers.  Their outer gluing
collars need not be disjoint: it suffices that the inner disk at either center
miss the other center's outer collar.  This file isolates the corresponding
radius and its asymptotic scale.
-/

/-- The center separation needed to keep an inner gluing disk out of the
other center's outer collar. -/
noncomputable def gluingSeparationRadius (C : ℝ) (g : ℕ) : ℝ :=
  2 * gluingRadius C g + gluingDepth C g

/-- The separation radius is one inner radius plus one outer collar radius. -/
theorem gluingSeparationRadius_eq_radius_add_embeddedRadius (C : ℝ) (g : ℕ) :
    gluingSeparationRadius C g =
      gluingRadius C g + gluingEmbeddedRadius C g := by
  simp only [gluingSeparationRadius, gluingEmbeddedRadius]
  ring

/-- The scale hypothesis already used for one embedded collar also bounds the
radius of its inner disk by `log (log g)`. -/
theorem gluingRadius_le_log_log_of_scale
    {C : ℝ} {g : ℕ}
    (hL : 0 ≤ targetSystole C g)
    (hscale :
      2 * (targetSystole C g / (2 * Real.pi)) + 1 ≤ Real.log g) :
    gluingRadius C g ≤ Real.log (Real.log g) := by
  have hx : 0 ≤ targetSystole C g / (2 * Real.pi) := by positivity
  calc
    gluingRadius C g ≤
        Real.log (2 * (targetSystole C g / (2 * Real.pi)) + 1) := by
      exact arsinh_le_log_two_mul_add_one hx
    _ ≤ Real.log (Real.log g) := by
      apply Real.log_le_log
      · linarith
      · exact hscale

/-- The exact `2 log log g` loss makes the separation scale
`(2 / 3) log g + log (log g) - C / 2`. -/
theorem gluingSeparationRadius_le_of_scale
    {C : ℝ} {g : ℕ}
    (hL : 0 ≤ targetSystole C g)
    (hscale :
      2 * (targetSystole C g / (2 * Real.pi)) + 1 ≤ Real.log g) :
    gluingSeparationRadius C g ≤
      (2 / 3 : ℝ) * Real.log g + Real.log (Real.log g) - C / 2 := by
  have hr := gluingRadius_le_log_log_of_scale hL hscale
  dsimp [gluingSeparationRadius, gluingDepth, targetSystole]
  linarith

/-- The preceding separation estimate holds uniformly for all sufficiently
large genera. -/
theorem eventually_gluingSeparationRadius_le
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ g : ℕ in atTop,
      gluingSeparationRadius C g ≤
        (2 / 3 : ℝ) * Real.log g + Real.log (Real.log g) - C / 2 := by
  filter_upwards [eventually_targetSystole_nonneg_and_scale hC] with g hg
  exact gluingSeparationRadius_le_of_scale hg.1 hg.2

/-- The inner radius is negligible on the logarithmic genus scale. -/
theorem tendsto_gluingRadius_div_log
    {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun g : ℕ ↦ gluingRadius C g / Real.log g)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog_div :
      Tendsto (fun g : ℕ ↦ Real.log (Real.log g) / Real.log g)
        atTop (𝓝 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using h
  apply squeeze_zero'
  · filter_upwards [eventually_targetSystole_nonneg_and_scale hC] with g hg
    have hx : 0 ≤ targetSystole C g / (2 * Real.pi) :=
      div_nonneg hg.1 (by positivity)
    have hr : 0 ≤ gluingRadius C g := by
      rw [gluingRadius, Real.arsinh_nonneg_iff]
      exact hx
    have hlog_pos : 0 < Real.log g := by
      have : 1 ≤ Real.log g := by linarith [hg.2, hx]
      linarith
    exact div_nonneg hr hlog_pos.le
  · filter_upwards [eventually_targetSystole_nonneg_and_scale hC] with g hg
    have hx : 0 ≤ targetSystole C g / (2 * Real.pi) :=
      div_nonneg hg.1 (by positivity)
    have hlog_pos : 0 < Real.log g := by
      have : 1 ≤ Real.log g := by linarith [hg.2, hx]
      linarith
    exact div_le_div_of_nonneg_right
      (gluingRadius_le_log_log_of_scale hg.1 hg.2) hlog_pos.le
  · exact hloglog_div

/-- The center-separation scale has leading coefficient `2 / 3`, leaving the
exponent gap needed to find a second center from genus-linear quotient area. -/
theorem tendsto_gluingSeparationRadius_div_log
    {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun g : ℕ ↦ gluingSeparationRadius C g / Real.log g)
      atTop (𝓝 (2 / 3 : ℝ)) := by
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hradius := tendsto_gluingRadius_div_log hC
  have htarget := tendsto_targetSystole_div_log C
  have hsum : Tendsto
      (fun g : ℕ ↦
        2 * (gluingRadius C g / Real.log g) +
          (1 / 2 : ℝ) * (targetSystole C g / Real.log g))
      atTop (𝓝 (2 / 3 : ℝ)) := by
    convert hradius.const_mul 2 |>.add (htarget.const_mul (1 / 2 : ℝ)) using 1
    norm_num
  apply hsum.congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with g hg
  dsimp [gluingSeparationRadius, gluingDepth]
  field_simp

/-- The separation scale is eventually strictly below `log g`; this is the
coarse exponent gap used by the quotient-area center-selection argument. -/
theorem eventually_gluingSeparationRadius_lt_log
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ g : ℕ in atTop,
      gluingSeparationRadius C g < Real.log g := by
  have hratio : ∀ᶠ g : ℕ in atTop,
      gluingSeparationRadius C g / Real.log g < (3 / 4 : ℝ) :=
    (tendsto_gluingSeparationRadius_div_log hC).eventually
      (Iio_mem_nhds (by norm_num : (2 / 3 : ℝ) < 3 / 4))
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hratio, hlog.eventually_gt_atTop 0] with g hratio_g hlog_g
  have h := (div_lt_iff₀ hlog_g).mp hratio_g
  nlinarith

end SystolicGrowth
