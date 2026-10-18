module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-!
# Smooth conformal coordinates of a genuine positive warp

The reciprocal-warp primitive and its actual inverse are smooth on their
open domains. The literal tensor `dt² + W(t)² dθ²` becomes conformally
Euclidean under this coordinate change. No native nonsmooth warp or
postulated inverse occurs in these constructions.
-/

open Set MeasureTheory
open scoped Topology ContDiff

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The actual reciprocal-warp primitive, based at zero. -/
def smoothWarpConformalRadius (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (W s)⁻¹

@[simp] theorem smoothWarpConformalRadius_zero (W : ℝ → ℝ) :
    smoothWarpConformalRadius W 0 = 0 := by
  simp [smoothWarpConformalRadius]

theorem smoothWarpConformalRadius_hasStrictDerivAt {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (t : ℝ) :
    HasStrictDerivAt (smoothWarpConformalRadius W) (W t)⁻¹ t :=
  (hW.inv₀ (fun s => (hpos s).ne')).integral_hasStrictDerivAt 0 t

theorem smoothWarpConformalRadius_contDiff {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) :
    ContDiff ℝ ∞ (smoothWarpConformalRadius W) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (smoothWarpConformalRadius_hasStrictDerivAt hW.continuous hpos t).hasDerivAt.differentiableAt, ?_⟩
  have hd : deriv (smoothWarpConformalRadius W) = fun t => (W t)⁻¹ :=
    funext fun t => (smoothWarpConformalRadius_hasStrictDerivAt hW.continuous hpos t).hasDerivAt.deriv
  rw [hd]
  exact hW.inv (fun t => (hpos t).ne')

theorem smoothWarpConformalRadius_strictMono {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) :
    StrictMono (smoothWarpConformalRadius W) := by
  apply strictMono_of_hasDerivAt_pos
    (fun t => (smoothWarpConformalRadius_hasStrictDerivAt hW hpos t).hasDerivAt)
  exact fun t => inv_pos.mpr (hpos t)

theorem smoothWarpConformalRadius_isOpenEmbedding {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) :
    Topology.IsOpenEmbedding (smoothWarpConformalRadius W) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_iff_continuousAt.mpr fun t =>
      (smoothWarpConformalRadius_hasStrictDerivAt hW hpos t).hasDerivAt.continuousAt)
    (smoothWarpConformalRadius_strictMono hW hpos).injective
  exact isOpenMap_of_hasStrictDerivAt
    (smoothWarpConformalRadius_hasStrictDerivAt hW hpos)
    (fun t => inv_ne_zero (hpos t).ne')

/-- The real radial coordinate with its genuine inverse on the open image. -/
def smoothWarpConformalRadialChart {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) : OpenPartialHomeomorph ℝ ℝ :=
  (smoothWarpConformalRadius_isOpenEmbedding hW hpos).toOpenPartialHomeomorph
    (smoothWarpConformalRadius W)

@[simp] theorem smoothWarpConformalRadialChart_apply {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (t : ℝ) :
    smoothWarpConformalRadialChart hW hpos t = smoothWarpConformalRadius W t := rfl

@[simp] theorem smoothWarpConformalRadialChart_source {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) :
    (smoothWarpConformalRadialChart hW hpos).source = univ := rfl

@[simp] theorem smoothWarpConformalRadialChart_left_inv {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (t : ℝ) :
    (smoothWarpConformalRadialChart hW hpos).symm (smoothWarpConformalRadius W t) = t :=
  (smoothWarpConformalRadialChart hW hpos).left_inv (mem_univ t)

theorem smoothWarpConformalRadialChart_symm_hasStrictDerivAt {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) {s : ℝ}
    (hs : s ∈ (smoothWarpConformalRadialChart hW hpos).target) :
    HasStrictDerivAt (smoothWarpConformalRadialChart hW hpos).symm
      (W ((smoothWarpConformalRadialChart hW hpos).symm s)) s := by
  simpa only [inv_inv] using
    (smoothWarpConformalRadialChart hW hpos).hasStrictDerivAt_symm hs
      (inv_ne_zero (hpos _).ne')
      (smoothWarpConformalRadius_hasStrictDerivAt hW hpos _)

theorem smoothWarpConformalRadialChart_symm_contDiffOn {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) :
    ContDiffOn ℝ ∞ (smoothWarpConformalRadialChart hW.continuous hpos).symm
      (smoothWarpConformalRadialChart hW.continuous hpos).target := by
  intro s hs
  exact ((smoothWarpConformalRadialChart hW.continuous hpos).contDiffAt_symm_deriv
    (inv_ne_zero (hpos _).ne') hs
    (smoothWarpConformalRadius_hasStrictDerivAt hW.continuous hpos _).hasDerivAt
    (smoothWarpConformalRadius_contDiff hW hpos).contDiffAt).contDiffWithinAt

/-- The literal conformal coordinate in the Euclidean complex plane. -/
def smoothWarpConformalCoordinate (W : ℝ → ℝ) (z : ℂ) : ℂ :=
  (smoothWarpConformalRadius W z.re : ℂ) + (z.im : ℂ) * Complex.I

/-- Conjugating the radial product chart by the real-complex linear
equivalence supplies its actual inverse; the original angular coordinate
is unchanged. -/
def smoothWarpConformalChart {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) : OpenPartialHomeomorph ℂ ℂ :=
  (Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph.trans
    ((smoothWarpConformalRadialChart hW hpos).prod (OpenPartialHomeomorph.refl ℝ))).trans
    Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem smoothWarpConformalChart_apply {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z : ℂ) :
    smoothWarpConformalChart hW hpos z = smoothWarpConformalCoordinate W z := by
  simp [smoothWarpConformalChart, smoothWarpConformalCoordinate,
    Complex.equivRealProdCLM_symm_apply]

@[simp] theorem smoothWarpConformalChart_source {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) :
    (smoothWarpConformalChart hW hpos).source = univ := by
  simp [smoothWarpConformalChart]

@[simp] theorem smoothWarpConformalChart_symm_apply {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z : ℂ) :
    (smoothWarpConformalChart hW hpos).symm z =
      ((smoothWarpConformalRadialChart hW hpos).symm z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  simp [smoothWarpConformalChart, Complex.equivRealProdCLM_symm_apply]

theorem smoothWarpConformalChart_target {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) :
    (smoothWarpConformalChart hW hpos).target =
      {z : ℂ | z.re ∈ (smoothWarpConformalRadialChart hW hpos).target} := by
  ext z
  simp [smoothWarpConformalChart]

theorem smoothWarpConformalCoordinate_contDiff {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) :
    ContDiff ℝ ∞ (smoothWarpConformalCoordinate W) := by
  exact (Complex.ofRealCLM.contDiff.comp
    ((smoothWarpConformalRadius_contDiff hW hpos).comp Complex.reCLM.contDiff)).add
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).mul contDiff_const)

theorem smoothWarpConformalChart_symm_contDiffOn {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) :
    ContDiffOn ℝ ∞ (smoothWarpConformalChart hW.continuous hpos).symm
      (smoothWarpConformalChart hW.continuous hpos).target := by
  intro z hz
  rw [smoothWarpConformalChart_target] at hz
  have hrad : ContDiffAt ℝ ∞
      (smoothWarpConformalRadialChart hW.continuous hpos).symm z.re :=
    (smoothWarpConformalRadialChart_symm_contDiffOn hW hpos).contDiffAt
      ((smoothWarpConformalRadialChart hW.continuous hpos).open_target.mem_nhds hz)
  have h : ContDiffAt ℝ ∞ (fun z : ℂ =>
      ((smoothWarpConformalRadialChart hW.continuous hpos).symm z.re : ℂ) +
        (z.im : ℂ) * Complex.I) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z (hrad.comp z Complex.reCLM.contDiff.contDiffAt)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z Complex.imCLM.contDiff.contDiffAt).mul
        (contDiffAt_const (c := Complex.I)))
  have hf : ((smoothWarpConformalChart hW.continuous hpos).symm : ℂ → ℂ) =
      fun z => ((smoothWarpConformalRadialChart hW.continuous hpos).symm z.re : ℂ) +
        (z.im : ℂ) * Complex.I := funext (smoothWarpConformalChart_symm_apply hW.continuous hpos)
  rw [hf]
  exact h.contDiffWithinAt

/-- The genuine differential of the conformal coordinate. -/
def smoothWarpConformalDerivative (W : ℝ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((W z.re)⁻¹ • Complex.reCLM) +
    Complex.I • (Complex.ofRealCLM.comp Complex.imCLM)

@[simp] theorem smoothWarpConformalDerivative_apply (W : ℝ → ℝ) (z v : ℂ) :
    smoothWarpConformalDerivative W z v =
      ((v.re / W z.re : ℝ) : ℂ) + (v.im : ℂ) * Complex.I := by
  simp [smoothWarpConformalDerivative, div_eq_mul_inv, mul_comm]

theorem smoothWarpConformalCoordinate_hasFDerivAt {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z : ℂ) :
    HasFDerivAt (smoothWarpConformalCoordinate W) (smoothWarpConformalDerivative W z) z := by
  have hr := (smoothWarpConformalRadius_hasStrictDerivAt hW hpos z.re).hasDerivAt.hasFDerivAt.comp z
    Complex.reCLM.hasFDerivAt
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt).const_smul Complex.I)
  have hf : smoothWarpConformalCoordinate W =
      (Complex.ofRealCLM ∘ smoothWarpConformalRadius W ∘ Complex.reCLM) +
        Complex.I • (Complex.ofRealCLM ∘ Complex.imCLM) := by
    funext w
    simp [smoothWarpConformalCoordinate, mul_comm]
  have hd : smoothWarpConformalDerivative W z =
      Complex.ofRealCLM.comp ((ContinuousLinearMap.toSpanSingleton ℝ ((W z.re)⁻¹)).comp Complex.reCLM) +
        Complex.I • (Complex.ofRealCLM.comp Complex.imCLM) := by
    ext v
    simp [smoothWarpConformalDerivative, mul_comm]
  rw [hf, hd]
  exact h

/-- The positive smooth radial conformal coefficient on the actual image. -/
def smoothWarpConformalFactor {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (s : ℝ) : ℝ :=
  W ((smoothWarpConformalRadialChart hW hpos).symm s)

theorem smoothWarpConformalFactor_pos {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (s : ℝ) :
    0 < smoothWarpConformalFactor hW hpos s := hpos _

theorem smoothWarpConformalFactor_contDiffOn {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) :
    ContDiffOn ℝ ∞ (smoothWarpConformalFactor hW.continuous hpos)
      (smoothWarpConformalRadialChart hW.continuous hpos).target :=
  hW.comp_contDiffOn (smoothWarpConformalRadialChart_symm_contDiffOn hW hpos)

/-- The genuine inverse-coordinate differential. -/
def smoothWarpConformalInverseDerivative {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (smoothWarpConformalFactor hW hpos z.re • Complex.reCLM) +
    Complex.I • (Complex.ofRealCLM.comp Complex.imCLM)

@[simp] theorem smoothWarpConformalInverseDerivative_apply {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z v : ℂ) :
    smoothWarpConformalInverseDerivative hW hpos z v =
      ((smoothWarpConformalFactor hW hpos z.re * v.re : ℝ) : ℂ) +
        (v.im : ℂ) * Complex.I := by
  simp [smoothWarpConformalInverseDerivative, mul_comm]

theorem smoothWarpConformalChart_symm_hasFDerivAt {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) {z : ℂ}
    (hz : z ∈ (smoothWarpConformalChart hW hpos).target) :
    HasFDerivAt (smoothWarpConformalChart hW hpos).symm
      (smoothWarpConformalInverseDerivative hW hpos z) z := by
  rw [smoothWarpConformalChart_target] at hz
  have hr := (smoothWarpConformalRadialChart_symm_hasStrictDerivAt hW hpos hz).hasDerivAt.hasFDerivAt.comp z
    Complex.reCLM.hasFDerivAt
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt).const_smul Complex.I)
  have hf : ((smoothWarpConformalChart hW hpos).symm : ℂ → ℂ) =
      (Complex.ofRealCLM ∘ (smoothWarpConformalRadialChart hW hpos).symm ∘ Complex.reCLM) +
        Complex.I • (Complex.ofRealCLM ∘ Complex.imCLM) := by
    funext w
    simp [mul_comm]
  have hd : smoothWarpConformalInverseDerivative hW hpos z =
      Complex.ofRealCLM.comp ((ContinuousLinearMap.toSpanSingleton ℝ
        (smoothWarpConformalFactor hW hpos z.re)).comp Complex.reCLM) +
        Complex.I • (Complex.ofRealCLM.comp Complex.imCLM) := by
    ext v
    simp [smoothWarpConformalInverseDerivative, mul_comm]
  rw [hf, hd]
  exact h

/-- **Math.** In the actual inverse coordinate, the same tensor has the
literal Euclidean conformal coefficient. -/
theorem smoothWarpTangentForm_inverse_eq_conformal {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z v w : ℂ) :
    (smoothWarpConformalInverseDerivative hW hpos z v).re *
        (smoothWarpConformalInverseDerivative hW hpos z w).re +
      W ((smoothWarpConformalChart hW hpos).symm z).re ^ 2 *
        (smoothWarpConformalInverseDerivative hW hpos z v).im *
        (smoothWarpConformalInverseDerivative hW hpos z w).im =
      smoothWarpConformalFactor hW hpos z.re ^ 2 * (v.re * w.re + v.im * w.im) := by
  simp [smoothWarpConformalInverseDerivative_apply, smoothWarpConformalFactor]
  ring

/-- **Math.** Exact equality of the same warped tensor with the conformal
Euclidean tensor, evaluated on its actual coordinate differential. -/
theorem smoothWarpTangentForm_eq_conformal {W : ℝ → ℝ}
    (hW : Continuous W) (hpos : ∀ t, 0 < W t) (z v w : ℂ) :
    v.re * w.re + W z.re ^ 2 * v.im * w.im =
      smoothWarpConformalFactor hW hpos (smoothWarpConformalCoordinate W z).re ^ 2 *
        ((smoothWarpConformalDerivative W z v).re * (smoothWarpConformalDerivative W z w).re +
          (smoothWarpConformalDerivative W z v).im * (smoothWarpConformalDerivative W z w).im) := by
  simp only [smoothWarpConformalFactor, smoothWarpConformalCoordinate,
    smoothWarpConformalDerivative_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
    smoothWarpConformalRadialChart_left_inv]
  field_simp [(hpos z.re).ne']
  ring

#print axioms smoothWarpConformalRadius_contDiff
#print axioms smoothWarpConformalRadialChart_symm_contDiffOn
#print axioms smoothWarpConformalChart_symm_contDiffOn
#print axioms smoothWarpConformalCoordinate_hasFDerivAt
#print axioms smoothWarpConformalChart_symm_hasFDerivAt
#print axioms smoothWarpTangentForm_inverse_eq_conformal
#print axioms smoothWarpTangentForm_eq_conformal

end

end SystolicGrowth
