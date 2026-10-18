module

public import Geometry.QuotientOrbitBall
public import Geometry.HyperbolicBallUpperVolume
public import Geometry.GluingCenterParameters

@[expose] public section

/-!
# Separated gluing centers under a genuine area budget

The gluing separation scale has a strict exponential-versus-linear area gap.
Combined with the actual quotient orbit-ball estimate, this selects two
separated centers on any surface satisfying the displayed covolume lower
bound. The genus-dependent Gauss--Bonnet area formula is not constructed or
assumed implicitly here; its budget remains an explicit conditional premise.
-/

open Filter MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise Topology UpperHalfPlane

namespace SystolicGrowth

/-- The required center-separation radius is eventually nonnegative. -/
theorem eventually_gluingSeparationRadius_nonneg {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ g : ℕ in atTop, 0 ≤ gluingSeparationRadius C g := by
  filter_upwards [eventually_targetSystole_nonneg_and_scale hC] with g hg
  have hr : 0 ≤ gluingRadius C g := by
    rw [gluingRadius, Real.arsinh_nonneg_iff]
    exact div_nonneg hg.1 (by positivity)
  dsimp only [gluingSeparationRadius, gluingDepth]
  linarith [hg.1]

/-- A fixed exponent gap above the limiting coefficient `2/3` leaves the
ball-area upper bound strictly sublinear in the genus. -/
theorem eventually_gluingSeparationRadius_le_seven_tenths_log {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ g : ℕ in atTop,
      gluingSeparationRadius C g ≤ (7 / 10 : ℝ) * Real.log g := by
  have hratio : ∀ᶠ g : ℕ in atTop,
      gluingSeparationRadius C g / Real.log g < (7 / 10 : ℝ) :=
    (tendsto_gluingSeparationRadius_div_log hC).eventually
      (Iio_mem_nhds (by norm_num : (2 / 3 : ℝ) < 7 / 10))
  have hlog : Tendsto (fun g : ℕ => Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hratio, hlog.eventually_gt_atTop 0] with g hg hlogg
  exact ((div_lt_iff₀ hlogg).mp hg).le

/-- The explicit genuine ball-area envelope eventually lies below every
positive genus-linear area budget. -/
theorem eventually_gluingAreaEnvelope_lt_linear_budget {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ g : ℕ in atTop,
      6 * Real.exp (4 * gluingSeparationRadius C g / 3) < c * ((g : ℝ) - 1) := by
  have hlog : Tendsto (fun g : ℕ => Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun g : ℕ => Real.exp (-(1 / 15 : ℝ) * Real.log g))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by norm_num : -(1 / 15 : ℝ) < 0) hlog)
  have hsmall : ∀ᶠ g : ℕ in atTop,
      Real.exp (-(1 / 15 : ℝ) * Real.log g) < c / 12 :=
    hdecay.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 12))
  filter_upwards [eventually_gluingSeparationRadius_le_seven_tenths_log hC,
    hsmall, eventually_ge_atTop 2] with g hD hsmallg hg
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hexp : Real.exp ((14 / 15 : ℝ) * Real.log g) =
      (g : ℝ) * Real.exp (-(1 / 15 : ℝ) * Real.log g) := by
    calc
      Real.exp ((14 / 15 : ℝ) * Real.log g) =
          Real.exp (Real.log g + (-(1 / 15 : ℝ) * Real.log g)) := by
            congr 1
            ring
      _ = Real.exp (Real.log g) * Real.exp (-(1 / 15 : ℝ) * Real.log g) := Real.exp_add _ _
      _ = (g : ℝ) * Real.exp (-(1 / 15 : ℝ) * Real.log g) := by rw [Real.exp_log hgpos]
  calc
    6 * Real.exp (4 * gluingSeparationRadius C g / 3) ≤
        6 * Real.exp ((14 / 15 : ℝ) * Real.log g) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      linarith
    _ = 6 * ((g : ℝ) * Real.exp (-(1 / 15 : ℝ) * Real.log g)) := by rw [hexp]
    _ < c * ((g : ℝ) / 2) := by
      have hmul := mul_lt_mul_of_pos_left hsmallg hgpos
      nlinarith
    _ ≤ c * ((g : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hc.le

/-- The upstairs ball at the gluing-separation scale is eventually smaller
than the displayed linear area budget, uniformly in its actual center. -/
theorem eventually_gluingBall_volume_lt_linear_budget {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ g : ℕ in atTop, ∀ o : ℍ,
      volume (Metric.ball o (gluingSeparationRadius C g)) <
        ENNReal.ofReal (c * ((g : ℝ) - 1)) := by
  filter_upwards [eventually_gluingSeparationRadius_nonneg hC,
    eventually_gluingAreaEnvelope_lt_linear_budget hC hc] with g hD harea
  intro o
  exact lt_of_le_of_lt (volume_ball_le_ofReal_six_mul_exp_four_thirds o hD)
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr harea)

/-- Conditional Gauss--Bonnet-budget consumer: any actual closed surface
with the displayed positive genus-linear covolume lower bound has a lifted
second gluing center separated from the first center's entire deck orbit.
The covolume bound is explicit because its genus formula remains separate. -/
theorem eventually_exists_gluing_orbit_centers_of_area_budget {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ g : ℕ in atTop, ∀ (X : ClosedHyperbolicSurface g) (o : ℍ),
      ENNReal.ofReal (c * ((g : ℝ) - 1)) ≤ covolume X.deckGroup ℍ volume →
      ∃ z : ℍ, ∀ γ : X.deckGroup, gluingSeparationRadius C g ≤ dist o (γ • z) := by
  filter_upwards [eventually_gluingBall_volume_lt_linear_budget hC hc] with g hg
  intro X o hbudget
  exact X.exists_orbit_separated_center_of_volume_lt_covolume o
    (gluingSeparationRadius C g) ((hg o).trans_le hbudget)

/-- The global gluing radius also has a strict area gap against any component
genus at least a fixed positive fraction of the global genus. -/
theorem eventually_gluingBall_volume_lt_component_budget {C c a : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ g : ℕ in atTop, ∀ (h : ℕ) (o : ℍ), a * (g : ℝ) ≤ h →
      volume (Metric.ball o (gluingSeparationRadius C g)) <
        ENNReal.ofReal (c * ((h : ℝ) - 1)) := by
  have hscale : Tendsto (fun g : ℕ => a * (g : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gluingBall_volume_lt_linear_budget hC
    (by positivity : 0 < c * a / 2), hscale.eventually_ge_atTop 2] with g hg hscaleg
  intro h o hgenus
  have hcompare : (c * a / 2) * ((g : ℝ) - 1) ≤ c * ((h : ℝ) - 1) := by
    calc
      (c * a / 2) * ((g : ℝ) - 1) = c * (a * ((g : ℝ) - 1) / 2) := by ring
      _ ≤ c * ((h : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hc.le
  exact (hg o).trans_le (ENNReal.ofReal_le_ofReal hcompare)

/-- Component-scale conditional Gauss--Bonnet-budget consumer: the global
gluing radius gives actual separated orbit centers on every sufficiently
large comparable-genus component, provided its genuine covolume satisfies
the explicit component-genus area lower bound. -/
theorem eventually_exists_gluing_orbit_centers_of_component_area_budget {C c a : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ g : ℕ in atTop, ∀ (h : ℕ) (X : ClosedHyperbolicSurface h) (o : ℍ),
      a * (g : ℝ) ≤ h →
      ENNReal.ofReal (c * ((h : ℝ) - 1)) ≤ covolume X.deckGroup ℍ volume →
      ∃ z : ℍ, ∀ γ : X.deckGroup, gluingSeparationRadius C g ≤ dist o (γ • z) := by
  filter_upwards [eventually_gluingBall_volume_lt_component_budget hC hc ha] with g hg
  intro h X o hgenus hbudget
  exact X.exists_orbit_separated_center_of_volume_lt_covolume o
    (gluingSeparationRadius C g) ((hg h o hgenus).trans_le hbudget)

#print axioms eventually_gluingAreaEnvelope_lt_linear_budget
#print axioms eventually_gluingBall_volume_lt_linear_budget
#print axioms eventually_exists_gluing_orbit_centers_of_area_budget
#print axioms eventually_gluingBall_volume_lt_component_budget
#print axioms eventually_exists_gluing_orbit_centers_of_component_area_budget

end SystolicGrowth
