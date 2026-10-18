module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarConformalCoordinates
public import Geometry.GluingCollarCurvatureProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# Weak curvature of the actual conformal collar factor

The constructed conformal radial chart transforms the original tangent
form to the factor `exp (2 Φ)`, where `Φ` is the logarithm of the native
warp at the actual inverse coordinate. Its weak second derivative has the
exact conformal area density and original seam jump. Window containment
only records the genuine domain of this open coordinate.
-/

open Set MeasureTheory

namespace SystolicGrowth

noncomputable section

/-- The logarithmic conformal factor in the constructed original collar chart. -/
def gluingCollarConformalLogFactor {r : ℝ} (hr : 0 < r) (u : ℝ) : ℝ :=
  Real.log (gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm u))

@[simp]
theorem gluingCollarConformalRadialChart_symm_zero {r : ℝ} (hr : 0 < r) :
    (gluingCollarConformalRadialChart hr).symm 0 = 0 := by
  simpa using gluingCollarConformalRadialChart_left_inv hr 0

/-- The actual inverse chart preserves positivity relative to the original seam. -/
theorem gluingCollarConformalRadialChart_symm_pos {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ (gluingCollarConformalRadialChart hr).target) (hu0 : 0 < u) :
    0 < (gluingCollarConformalRadialChart hr).symm u := by
  have hright := (gluingCollarConformalRadialChart hr).right_inv hu
  change gluingCollarConformalRadius r ((gluingCollarConformalRadialChart hr).symm u) = u at hright
  apply (gluingCollarConformalRadius_strictMono hr).lt_iff_lt.mp
  rwa [gluingCollarConformalRadius_zero, hright]

/-- The actual inverse chart preserves negativity relative to the original seam. -/
theorem gluingCollarConformalRadialChart_symm_neg {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ (gluingCollarConformalRadialChart hr).target) (hu0 : u < 0) :
    (gluingCollarConformalRadialChart hr).symm u < 0 := by
  have hright := (gluingCollarConformalRadialChart hr).right_inv hu
  change gluingCollarConformalRadius r ((gluingCollarConformalRadialChart hr).symm u) = u at hright
  apply (gluingCollarConformalRadius_strictMono hr).lt_iff_lt.mp
  rwa [gluingCollarConformalRadius_zero, hright]

theorem gluingCollarConformalLogFactor_continuousOn {r : ℝ} (hr : 0 < r) :
    ContinuousOn (gluingCollarConformalLogFactor hr)
      (gluingCollarConformalRadialChart hr).target := by
  exact ((gluingCollarWarp_continuous r).comp_continuousOn
    (gluingCollarConformalRadialChart hr).continuousOn_symm).log
    (fun _ _ => (gluingCollarWarp_pos hr _).ne')

/-- Away from the seam on the positive side, the actual logarithmic
factor has derivative `cosh(r + inverse u)`. -/
theorem gluingCollarConformalLogFactor_hasDerivAt_pos {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ (gluingCollarConformalRadialChart hr).target) (hu0 : 0 < u) :
    HasDerivAt (gluingCollarConformalLogFactor hr)
      (Real.cosh (r + (gluingCollarConformalRadialChart hr).symm u)) u := by
  have hi := (gluingCollarConformalRadialChart_symm_hasStrictDerivAt hr hu).hasDerivAt
  have hsign := gluingCollarConformalRadialChart_symm_pos hr hu hu0
  have hh := ((gluingCollarWarp_hasDerivAt_pos r hsign).comp u hi).log
    (gluingCollarWarp_pos hr _).ne'
  convert hh using 1 <;> first
    | rfl
    | dsimp only [Function.comp_apply]
      field_simp [(gluingCollarWarp_pos hr _).ne']

/-- Away from the seam on the negative side, the actual logarithmic
factor has derivative `-cosh(r - inverse u)`. -/
theorem gluingCollarConformalLogFactor_hasDerivAt_neg {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ (gluingCollarConformalRadialChart hr).target) (hu0 : u < 0) :
    HasDerivAt (gluingCollarConformalLogFactor hr)
      (-Real.cosh (r - (gluingCollarConformalRadialChart hr).symm u)) u := by
  have hi := (gluingCollarConformalRadialChart_symm_hasStrictDerivAt hr hu).hasDerivAt
  have hsign := gluingCollarConformalRadialChart_symm_neg hr hu hu0
  have hh := ((gluingCollarWarp_hasDerivAt_neg r hsign).comp u hi).log
    (gluingCollarWarp_pos hr _).ne'
  convert hh using 1 <;> first
    | rfl
    | dsimp only [Function.comp_apply]
      field_simp [(gluingCollarWarp_pos hr _).ne']

/-- The positive-side logarithmic slope has exactly the conformal area
density as derivative. -/
theorem gluingCollarConformalLogSlope_hasDerivAt_pos {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ (gluingCollarConformalRadialChart hr).target) (hu0 : 0 < u) :
    HasDerivAt (fun v => Real.cosh (r + (gluingCollarConformalRadialChart hr).symm v))
      (gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm u) ^ 2) u := by
  have hi := (gluingCollarConformalRadialChart_symm_hasStrictDerivAt hr hu).hasDerivAt
  have hsign := gluingCollarConformalRadialChart_symm_pos hr hu hu0
  convert (hi.const_add r).cosh using 1; first
    | rfl
    | rw [gluingCollarWarp_eq_of_nonneg r hsign.le]
      ring

/-- The negative-side logarithmic slope has the same exact conformal
area density as derivative. -/
theorem gluingCollarConformalLogSlope_hasDerivAt_neg {r u : ℝ} (hr : 0 < r)
    (hu : u ∈ (gluingCollarConformalRadialChart hr).target) (hu0 : u < 0) :
    HasDerivAt (fun v => -Real.cosh (r - (gluingCollarConformalRadialChart hr).symm v))
      (gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm u) ^ 2) u := by
  have hi := (gluingCollarConformalRadialChart_symm_hasStrictDerivAt hr hu).hasDerivAt
  have hsign := gluingCollarConformalRadialChart_symm_neg hr hu hu0
  convert (hi.const_sub r).cosh.neg using 1 <;> first
    | rfl
    | rw [gluingCollarWarp_eq_of_nonpos r hsign.le]
      ring

/-- The actual log factor identifies conformal area density, including
the seam, with the original metric's positive conformal coefficient. -/
theorem gluingCollarConformalLogFactor_exp_two {r : ℝ} (hr : 0 < r) (u : ℝ) :
    Real.exp (2 * gluingCollarConformalLogFactor hr u) =
      gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm u) ^ 2 := by
  rw [show 2 * gluingCollarConformalLogFactor hr u =
    gluingCollarConformalLogFactor hr u + gluingCollarConformalLogFactor hr u by ring,
    Real.exp_add, gluingCollarConformalLogFactor,
    Real.exp_log (gluingCollarWarp_pos hr _)]
  ring

/-- The genuine weak second derivative of the actual logarithmic
conformal factor is conformal area density plus the original seam atom.
The window hypotheses state only the actual chart domain and compact-test
endpoint conditions; no curvature conclusion is assumed. -/
theorem gluingCollarConformalLogFactor_weak_second_derivative_Icc
    {r a b : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0) :
    (∫ u in a..b, gluingCollarConformalLogFactor hr u * deriv (deriv φ) u) =
      (∫ u in a..b, gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm u) ^ 2 * φ u) +
        2 * Real.cosh r * φ 0 := by
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdφ' : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have hφ'' : Continuous (deriv (deriv φ)) := hφ'.continuous_deriv_one
  let F := gluingCollarConformalLogFactor hr
  let inv := (gluingCollarConformalRadialChart hr).symm
  let Bminus : ℝ → ℝ := fun u => -Real.cosh (r - inv u)
  let Bplus : ℝ → ℝ := fun u => Real.cosh (r + inv u)
  let Wminus : ℝ → ℝ := fun u => F u * deriv φ u - Bminus u * φ u
  let Wplus : ℝ → ℝ := fun u => F u * deriv φ u - Bplus u * φ u
  let H : ℝ → ℝ := fun u => F u * deriv (deriv φ) u - gluingCollarWarp r (inv u) ^ 2 * φ u
  have hF : ContinuousOn F (Icc a b) :=
    (gluingCollarConformalLogFactor_continuousOn hr).mono hwindow
  have hinv : ContinuousOn inv (Icc a b) :=
    (gluingCollarConformalRadialChart hr).continuousOn_symm.mono hwindow
  have hBm : ContinuousOn Bminus (Icc a b) :=
    (Real.continuous_cosh.comp_continuousOn (continuousOn_const.sub hinv)).neg
  have hBp : ContinuousOn Bplus (Icc a b) :=
    Real.continuous_cosh.comp_continuousOn (continuousOn_const.add hinv)
  have hWm : ContinuousOn Wminus (Icc a b) :=
    (hF.mul hφ'.continuous.continuousOn).sub (hBm.mul hφ.continuous.continuousOn)
  have hWp : ContinuousOn Wplus (Icc a b) :=
    (hF.mul hφ'.continuous.continuousOn).sub (hBp.mul hφ.continuous.continuousOn)
  have hH : ContinuousOn H (Icc a b) :=
    (hF.mul hφ''.continuousOn).sub
      (((gluingCollarWarp_continuous r).comp_continuousOn hinv).pow 2 |>.mul hφ.continuous.continuousOn)
  have hLeftSubset : Icc a 0 ⊆ Icc a b := Icc_subset_Icc le_rfl hb.le
  have hRightSubset : Icc 0 b ⊆ Icc a b := Icc_subset_Icc ha.le le_rfl
  have hminusDeriv (u : ℝ) (hu : u ∈ Ioo a 0) : HasDerivAt Wminus (H u) u := by
    have hutarget := hwindow (hLeftSubset (Ioo_subset_Icc_self hu))
    have hlog := gluingCollarConformalLogFactor_hasDerivAt_neg hr hutarget hu.2
    have hslope := gluingCollarConformalLogSlope_hasDerivAt_neg hr hutarget hu.2
    convert (hlog.mul (hdφ' u).hasDerivAt).sub (hslope.mul (hdφ u).hasDerivAt) using 1 <;>
      first | rfl | dsimp [H, F, Bminus, inv]; ring
  have hplusDeriv (u : ℝ) (hu : u ∈ Ioo 0 b) : HasDerivAt Wplus (H u) u := by
    have hutarget := hwindow (hRightSubset (Ioo_subset_Icc_self hu))
    have hlog := gluingCollarConformalLogFactor_hasDerivAt_pos hr hutarget hu.1
    have hslope := gluingCollarConformalLogSlope_hasDerivAt_pos hr hutarget hu.1
    convert (hlog.mul (hdφ' u).hasDerivAt).sub (hslope.mul (hdφ u).hasDerivAt) using 1 <;>
      first | rfl | dsimp [H, F, Bplus, inv]; ring
  have hIntLeft : IntervalIntegrable H volume a 0 :=
    (hH.mono hLeftSubset).intervalIntegrable_of_Icc ha.le
  have hIntRight : IntervalIntegrable H volume 0 b :=
    (hH.mono hRightSubset).intervalIntegrable_of_Icc hb.le
  have hminusIntegral : (∫ u in a..0, H u) = Wminus 0 - Wminus a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le
      (hWm.mono hLeftSubset) hminusDeriv hIntLeft
  have hplusIntegral : (∫ u in 0..b, H u) = Wplus b - Wplus 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le
      (hWp.mono hRightSubset) hplusDeriv hIntRight
  have hweak : (∫ u in a..b, H u) = 2 * Real.cosh r * φ 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hIntLeft hIntRight,
      hminusIntegral, hplusIntegral]
    simp only [Wminus, Wplus, Bminus, Bplus, inv,
      gluingCollarConformalRadialChart_symm_zero, add_zero, sub_zero,
      hφa, hφb, hφ'a, hφ'b, mul_zero, zero_sub]
    ring
  have hfactorInt : IntervalIntegrable (fun u => F u * deriv (deriv φ) u) volume a b :=
    (hF.mul hφ''.continuousOn).intervalIntegrable_of_Icc (by linarith)
  have hareaInt : IntervalIntegrable (fun u => gluingCollarWarp r (inv u) ^ 2 * φ u) volume a b :=
    (((gluingCollarWarp_continuous r).comp_continuousOn hinv).pow 2 |>.mul
      hφ.continuous.continuousOn).intervalIntegrable_of_Icc (by linarith)
  rw [show H = fun u => F u * deriv (deriv φ) u -
    gluingCollarWarp r (inv u) ^ 2 * φ u from rfl,
    intervalIntegral.integral_sub hfactorInt hareaInt] at hweak
  linarith

/-- The negative weak Laplacian of the actual log factor has exactly
negative conformal area plus the original negative seam curvature atom. -/
theorem gluingCollarConformalLogFactor_curvature_pairing_Icc
    {r a b : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0) :
    -(∫ u in a..b, gluingCollarConformalLogFactor hr u * deriv (deriv φ) u) =
      -(∫ u in a..b, Real.exp (2 * gluingCollarConformalLogFactor hr u) * φ u) -
        2 * Real.cosh r * φ 0 := by
  simp_rw [gluingCollarConformalLogFactor_exp_two hr]
  have hh := gluingCollarConformalLogFactor_weak_second_derivative_Icc
    hr ha hb hwindow hφ hφa hφb hφ'a hφ'b
  linarith

/-- Against every nonnegative compact-window test, the actual conformal
weak curvature is bounded above by negative conformal area. -/
theorem gluingCollarConformalLogFactor_curvature_le_neg_area_Icc
    {r a b : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0)
    (hφnonneg : ∀ u ∈ Icc a b, 0 ≤ φ u) :
    -(∫ u in a..b, gluingCollarConformalLogFactor hr u * deriv (deriv φ) u) ≤
      -(∫ u in a..b, Real.exp (2 * gluingCollarConformalLogFactor hr u) * φ u) := by
  rw [gluingCollarConformalLogFactor_curvature_pairing_Icc hr ha hb hwindow
    hφ hφa hφb hφ'a hφ'b]
  exact sub_le_self _ (mul_nonneg (mul_nonneg (by norm_num) (Real.cosh_pos r).le)
    (hφnonneg 0 ⟨ha.le, hb.le⟩))

#print axioms gluingCollarConformalLogFactor_hasDerivAt_pos
#print axioms gluingCollarConformalLogFactor_hasDerivAt_neg
#print axioms gluingCollarConformalLogFactor_exp_two
#print axioms gluingCollarConformalLogFactor_weak_second_derivative_Icc
#print axioms gluingCollarConformalLogFactor_curvature_pairing_Icc
#print axioms gluingCollarConformalLogFactor_curvature_le_neg_area_Icc

end
end SystolicGrowth
