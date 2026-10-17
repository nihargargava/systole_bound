module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarSmooth
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

/-!
# Actual local smooth inverses of the lifted hyperbolic polar map

At each positive radial parameter the explicit polar derivative is an
invertible real continuous linear map. Its equivalence is constructed from
the actual radial and angular coefficients and the actual centered Cayley
derivative. The native inverse-function theorem then gives local inverse
coordinates for the unchanged polar map. There is no global injectivity,
global diffeomorphism, or glued-atlas assertion.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

theorem Internal.GluingPolarDiffeomorphHelpers.polar_radial_coefficient_ne_zero (p : ℝ × ℝ) :
    (1 : ℝ) / (2 * Real.cosh (p.1 / 2) ^ 2) ≠ 0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 2 (Real.cosh_pos (p.1 / 2)).ne'))

theorem Internal.GluingPolarDiffeomorphHelpers.polar_angular_coefficient_ne_zero
    (p : ℝ × ℝ) (hp : 0 < p.1) : Real.tanh (p.1 / 2) ≠ 0 := by
  apply ne_of_gt
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)

/-- The actual disk differential as a real continuous linear equivalence. -/
noncomputable def gluingPolarDiskLiftDerivEquiv
    (p : ℝ × ℝ) (hp : 0 < p.1) : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 (1 / (2 * Real.cosh (p.1 / 2) ^ 2))
        (Internal.GluingPolarDiffeomorphHelpers.polar_radial_coefficient_ne_zero p))).prodCongr
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
        (Units.mk0 (Real.tanh (p.1 / 2)) (Internal.GluingPolarDiffeomorphHelpers.polar_angular_coefficient_ne_zero p hp)))).trans
      Complex.equivRealProdCLM.symm).trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (Complex.exp ((p.2 : ℂ) * Complex.I)) (Complex.exp_ne_zero _)))

/-- The constructed equivalence is exactly the proved disk differential. -/
theorem gluingPolarDiskLiftDerivEquiv_toCLM
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    (gluingPolarDiskLiftDerivEquiv p hp : (ℝ × ℝ) →L[ℝ] ℂ) =
      gluingPolarDiskLiftFDeriv p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [gluingPolarDiskLiftFDeriv_apply]
  simp [gluingPolarDiskLiftDerivEquiv, ContinuousLinearEquiv.smulLeft,
    Complex.equivRealProdCLM_symm_apply, gluingPolarDiskLift, Units.smul_def, smul_eq_mul]
  ring

/-- The actual centered Cayley coefficient is nonzero on every lifted disk point. -/
theorem gluingPolarLift_cayley_coefficient_ne_zero (o : ℍ) (p : ℝ × ℝ) :
    gluingCenteredCayleyDeriv o (gluingPolarDiskLift p) ≠ 0 := by
  unfold gluingCenteredCayleyDeriv
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr o.im_pos.ne')
      (by norm_num)) Complex.I_ne_zero)
    (pow_ne_zero 2 (one_sub_gluingPolarDiskLift_ne_zero p))

/-- The actual positive-radius polar differential as a real linear equivalence. -/
noncomputable def gluingPolarLiftDerivEquiv
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  (gluingPolarDiskLiftDerivEquiv p hp).trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (gluingCenteredCayleyDeriv o (gluingPolarDiskLift p))
        (gluingPolarLift_cayley_coefficient_ne_zero o p)))

/-- The equivalence's underlying map is exactly the actual polar differential. -/
theorem gluingPolarLiftDerivEquiv_toCLM
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    (gluingPolarLiftDerivEquiv o p hp : (ℝ × ℝ) →L[ℝ] ℂ) =
      gluingPolarLiftFDeriv o p := by
  apply ContinuousLinearMap.ext
  intro v
  change gluingPolarLiftDerivEquiv o p hp v = gluingPolarLiftFDeriv o p v
  simp only [gluingPolarLiftDerivEquiv, ContinuousLinearEquiv.trans_apply]
  have hd := congrArg (fun f : (ℝ × ℝ) →L[ℝ] ℂ => f v)
    (gluingPolarDiskLiftDerivEquiv_toCLM p hp)
  change gluingPolarDiskLiftDerivEquiv p hp v = gluingPolarDiskLiftFDeriv p v at hd
  rw [hd, gluingPolarLiftFDeriv, ContinuousLinearMap.comp_apply,
    gluingCenteredCayleyFDeriv_apply]
  simp [ContinuousLinearEquiv.smulLeft, gluingCenteredCayleyDeriv]
  ring

/-- Positive radius gives an actual invertible derivative, not an input premise. -/
theorem gluingPolarLift_hasFDerivAt_equiv
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasFDerivAt (gluingPolarLift o)
      (gluingPolarLiftDerivEquiv o p hp : (ℝ × ℝ) →L[ℝ] ℂ) p := by
  rw [gluingPolarLiftDerivEquiv_toCLM]
  exact gluingPolarLift_hasFDerivAt o p

/-- A genuine local inverse chart of the explicit polar lift at positive radius. -/
noncomputable def gluingPolarLiftLocalHomeomorph
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) : OpenPartialHomeomorph (ℝ × ℝ) ℂ :=
  (gluingPolarLift_contDiff o).contDiffAt.toOpenPartialHomeomorph (gluingPolarLift o)
    (gluingPolarLift_hasFDerivAt_equiv o p hp) (by simp)

/-- The local chart's forward function is the original actual polar map. -/
@[simp] theorem gluingPolarLiftLocalHomeomorph_apply
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) (v : ℝ × ℝ) :
    gluingPolarLiftLocalHomeomorph o p hp v = gluingPolarLift o v := rfl

theorem gluingPolarLiftLocalHomeomorph_mem_source
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    p ∈ (gluingPolarLiftLocalHomeomorph o p hp).source :=
  (gluingPolarLift_contDiff o).contDiffAt.mem_toOpenPartialHomeomorph_source
    (gluingPolarLift_hasFDerivAt_equiv o p hp) (by simp)

/-- The genuine local inverse is smooth at the actual image point. -/
theorem gluingPolarLiftLocalHomeomorph_symm_contDiffAt
    (o : ℍ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    ContDiffAt ℝ ⊤ (gluingPolarLiftLocalHomeomorph o p hp).symm (gluingPolarLift o p) :=
  (gluingPolarLift_contDiff o).contDiffAt.to_localInverse
    (gluingPolarLift_hasFDerivAt_equiv o p hp) (by simp)

#print axioms gluingPolarLiftDerivEquiv_toCLM
#print axioms gluingPolarLiftLocalHomeomorph
#print axioms gluingPolarLiftLocalHomeomorph_symm_contDiffAt

end SystolicGrowth
