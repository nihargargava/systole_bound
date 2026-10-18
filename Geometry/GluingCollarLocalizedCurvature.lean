module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLocalizedSmoothWarp
public import Geometry.GluingCurvatureBoundedWarp
public import Geometry.GluingCollarCurvatureMeasure
public import Geometry.GluingCollarSmoothCurvatureConvergence
public import Geometry.GluingCollarSmoothDerivativeBounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Weak curvature limit of actual localized collar smoothing

The genuine compactly localized smooth warp has the original seam-containing
radial curvature as its distributional limit. Both integrations by parts and
the quantitative compact-test error are proved. Uniform total variation and
the surface-wide smoothing remain separate obligations.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SystolicGrowth

/-- The actual first derivative away from the corner. The cutoff removes the
corner in the localized warp, but this formula needs only the native ordinary
derivative on its genuine differentiability locus. -/
theorem gluingCollarLocalizedSmoothWarp_deriv_of_ne
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    {t : ℝ} (ht : t ≠ 0) :
    deriv (gluingCollarLocalizedSmoothWarp r ε b) t =
      deriv b t * (gluingCollarSmoothWarp r ε t - gluingCollarWarp r t) +
        b t * deriv (gluingCollarSmoothWarp r ε) t +
          (1 - b t) * deriv (gluingCollarWarp r) t := by
  have hb : HasDerivAt b (deriv b t) t :=
    ((b.contDiff : ContDiff ℝ 1 b).differentiable (by norm_num) t).hasDerivAt
  have hF := ((gluingCollarSmoothWarp_contDiff r hε 1).differentiable
    (by norm_num) t).hasDerivAt
  have hf := gluingCollarWarp_hasDerivAt_of_ne r ht
  have h := ((hb.mul hF).add (((hasDerivAt_const t (1 : ℝ)).sub hb).mul hf)).deriv
  change deriv (gluingCollarLocalizedSmoothWarp r ε b) t = _ at h
  rw [h]
  dsimp only [Pi.sub_apply]
  ring

/-- The literal second derivative of the localized warp. At the seam the
cutoff is identically one nearby, so no derivative of the native corner is
assumed in obtaining this all-point identity. -/
theorem gluingCollarLocalizedSmoothWarp_second_deriv
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t =
      b t * deriv (deriv (gluingCollarSmoothWarp r ε)) t +
        (1 - b t) * gluingCollarWarp r t +
          2 * deriv b t *
            (deriv (gluingCollarSmoothWarp r ε) t - deriv (gluingCollarWarp r) t) +
          deriv (deriv b) t *
            (gluingCollarSmoothWarp r ε t - gluingCollarWarp r t) := by
  by_cases ht : t = 0
  · subst t
    have hb : (b : ℝ → ℝ) =ᶠ[𝓝 0] fun _ => 1 := b.eventuallyEq_one
    have hb0 : b 0 = 1 := hb.eq_of_nhds
    have hb' : deriv b 0 = 0 := by simpa using hb.deriv_eq
    have hb'' : deriv (deriv b) 0 = 0 := by
      simpa using hb.deriv.deriv_eq
    have hW : gluingCollarLocalizedSmoothWarp r ε b =ᶠ[𝓝 0]
        gluingCollarSmoothWarp r ε := by
      filter_upwards [hb] with s hs
      simp [gluingCollarLocalizedSmoothWarp, hs]
    rw [hW.deriv.deriv_eq, hb0, hb', hb'']
    ring
  · have hfirst : deriv (gluingCollarLocalizedSmoothWarp r ε b) =ᶠ[𝓝 t]
        fun s => deriv b s * (gluingCollarSmoothWarp r ε s - gluingCollarWarp r s) +
          b s * deriv (gluingCollarSmoothWarp r ε) s +
            (1 - b s) * deriv (gluingCollarWarp r) s := by
      filter_upwards [eventually_ne_nhds ht] with s hs
      exact gluingCollarLocalizedSmoothWarp_deriv_of_ne r hε b hs
    have hb : ContDiff ℝ 2 b := b.contDiff
    have hF := gluingCollarSmoothWarp_contDiff r hε 2
    have hb₁ := (hb.differentiable (by norm_num) t).hasDerivAt
    have hb₂ := (hb.differentiable_deriv_two t).hasDerivAt
    have hF₁ := (hF.differentiable (by norm_num) t).hasDerivAt
    have hF₂ := (hF.differentiable_deriv_two t).hasDerivAt
    have hf₁ := gluingCollarWarp_hasDerivAt_of_ne r ht
    have hf₂ := gluingCollarWarp_hasDerivAt_deriv r ht
    have h := (((hb₂.mul (hF₁.sub hf₁)).add (hb₁.mul hF₂)).add
      (((hasDerivAt_const t (1 : ℝ)).sub hb₁).mul hf₂)).deriv
    change deriv (fun s => deriv b s *
      (gluingCollarSmoothWarp r ε s - gluingCollarWarp r s) +
        b s * deriv (gluingCollarSmoothWarp r ε) s +
          (1 - b s) * deriv (gluingCollarWarp r) s) t = _ at h
    rw [hfirst.deriv_eq, h]
    dsimp only [Pi.sub_apply]
    ring

/-- Localization may introduce positive curvature, but its absolute radial
curvature is bounded by the positive unlocalized second derivative and the
three explicit cutoff terms. No sign assumption on the localized curvature
is imposed. -/
theorem gluingCollarLocalizedSmoothWarp_abs_second_deriv_le
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t| ≤
      deriv (deriv (gluingCollarSmoothWarp r ε)) t + gluingCollarWarp r t +
        2 * |deriv b t| *
          (|deriv (gluingCollarSmoothWarp r ε) t| + |deriv (gluingCollarWarp r) t|) +
        |deriv (deriv b) t| * Real.cosh r * ε := by
  let A := deriv (deriv (gluingCollarSmoothWarp r ε)) t
  let f := gluingCollarWarp r t
  have hA : 0 ≤ A := (gluingCollarSmoothWarp_second_deriv_pos hr hε hε1 t).le
  have hf : 0 ≤ f := (gluingCollarWarp_pos hr t).le
  have hb : 0 ≤ b t := b.nonneg
  have hb1 : 0 ≤ 1 - b t := sub_nonneg.mpr b.le_one
  have hfour (a c d e : ℝ) : |a + c + d + e| ≤ |a| + |c| + |d| + |e| := by
    have h₁ := abs_add_le a c
    have h₂ := abs_add_le (a + c) d
    have h₃ := abs_add_le (a + c + d) e
    linarith
  rw [gluingCollarLocalizedSmoothWarp_second_deriv r hε b]
  calc
    _ ≤ |b t * A| + |(1 - b t) * f| +
        |2 * deriv b t *
          (deriv (gluingCollarSmoothWarp r ε) t - deriv (gluingCollarWarp r) t)| +
        |deriv (deriv b) t * (gluingCollarSmoothWarp r ε t - f)| := by
      exact hfour _ _ _ _
    _ ≤ A + f + 2 * |deriv b t| *
        (|deriv (gluingCollarSmoothWarp r ε) t| + |deriv (gluingCollarWarp r) t|) +
        |deriv (deriv b) t| * (Real.cosh r * ε) := by
      rw [abs_of_nonneg (mul_nonneg hb hA), abs_of_nonneg (mul_nonneg hb1 hf),
        abs_mul (2 * deriv b t), abs_mul (2 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_mul (deriv (deriv b) t)]
      apply add_le_add
      · apply add_le_add
        · exact add_le_add
            (by simpa using mul_le_mul_of_nonneg_right b.le_one hA)
            (by nlinarith [mul_nonneg hb hf])
        · exact mul_le_mul_of_nonneg_left (by simpa using (abs_sub_le
            (deriv (gluingCollarSmoothWarp r ε) t) 0 (deriv (gluingCollarWarp r) t)))
            (mul_nonneg (by norm_num) (abs_nonneg _))
      · exact mul_le_mul_of_nonneg_left
          (gluingCollarSmoothWarp_uniform_bound r hε.le t) (abs_nonneg _)
    _ = _ := by dsimp [A, f]; ring

/-- Uniform control of the genuine unlocalized second-derivative integral
from the actual endpoint derivative. -/
theorem gluingCollarSmoothWarp_second_deriv_integral_le
    {r ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∫ t : ℝ in Icc (-R) R, deriv (deriv (gluingCollarSmoothWarp r ε)) t) ≤
      2 * Real.cosh (r + R) := by
  have hF := gluingCollarSmoothWarp_contDiff r hε 2
  have hF' : ContDiff ℝ 1 (deriv (gluingCollarSmoothWarp r ε)) := hF.deriv'
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -R ≤ R by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show -R ≤ R by linarith) hF'.continuous.continuousOn
      (fun t _ => (hF.differentiable_deriv_two t).hasDerivAt)
      (hF'.continuous_deriv_one.intervalIntegrable (-R) R),
    gluingCollarSmoothWarp_deriv_neg r hε]
  have h := gluingCollarSmoothWarp_deriv_le_native (r := r) hε hR.le
  linarith

/-- Every actual localized approximation has uniformly bounded absolute
radial curvature on a fixed compact window. The bound is independent of ε;
it is constructed from genuine compact bounds of the chosen smooth cutoff. -/
theorem gluingCollarLocalizedSmoothWarp_uniform_abs_second_deriv_integral_bound
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (b : ContDiffBump (0 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫ t : ℝ in Icc (-R) R,
        |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t|) ≤ B := by
  have hb : ContDiff ℝ 2 b := b.contDiff
  have hcomp : IsCompact (Icc (-R) R) := isCompact_Icc
  have hbd : ContDiff ℝ 1 (deriv (b : ℝ → ℝ)) := hb.deriv'
  have hb' : Continuous (deriv (b : ℝ → ℝ)) := hbd.continuous
  have hb'' : Continuous (deriv (deriv (b : ℝ → ℝ))) := hbd.continuous_deriv_one
  obtain ⟨B₁, hB₁⟩ := hcomp.exists_bound_of_continuousOn hb'.continuousOn
  obtain ⟨B₂, hB₂⟩ := hcomp.exists_bound_of_continuousOn hb''.continuousOn
  have hzero : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 hzero)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0 hzero)
  let M := Real.sinh (r + R) + 4 * B₁ * Real.cosh (r + R) + B₂ * Real.cosh r
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨2 * Real.cosh (r + R) + 2 * R * M, by positivity, ?_⟩
  intro ε hε hε1
  have hW := (gluingCollarLocalizedSmoothWarp_contDiff r hε b 2).deriv'.continuous_deriv_one
  have hF := (gluingCollarSmoothWarp_contDiff r hε 2).deriv'.continuous_deriv_one
  have hpoint (t : ℝ) (ht : t ∈ Icc (-R) R) :
      |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t| ≤
        deriv (deriv (gluingCollarSmoothWarp r ε)) t + M := by
    have hb₁ : |deriv b t| ≤ B₁ := by simpa only [Real.norm_eq_abs] using hB₁ t ht
    have hb₂ : |deriv (deriv b) t| ≤ B₂ := by simpa only [Real.norm_eq_abs] using hB₂ t ht
    have hd₁ := gluingCollarSmoothWarp_deriv_abs_le_window hr hε hR.le ht
    have hd₂ := gluingCollarWarp_deriv_abs_le_positive_radius hr hR.le ht
    have hf := gluingCollarWarp_abs_le_window hr ht
    have hfirst : 2 * |deriv b t| *
        (|deriv (gluingCollarSmoothWarp r ε) t| + |deriv (gluingCollarWarp r) t|) ≤
        4 * B₁ * Real.cosh (r + R) := by
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hb₁ (by norm_num : (0 : ℝ) ≤ 2))
        (add_le_add hd₁ hd₂) (by positivity) (by positivity)
      nlinarith only [h]
    have hsecond : |deriv (deriv b) t| * Real.cosh r * ε ≤ B₂ * Real.cosh r := by
      have h := mul_le_mul (mul_le_mul_of_nonneg_right hb₂ (Real.cosh_pos r).le)
        hε1 hε.le (mul_nonneg hB₂0 (Real.cosh_pos r).le)
      simpa using h
    have h := gluingCollarLocalizedSmoothWarp_abs_second_deriv_le hr hε hε1 b t
    dsimp [M]
    linarith [le_abs_self (gluingCollarWarp r t)]
  have hint :
      (∫ t : ℝ in Icc (-R) R,
        |deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) t|) ≤
      ∫ t : ℝ in Icc (-R) R, deriv (deriv (gluingCollarSmoothWarp r ε)) t + M := by
    exact integral_mono_ae hW.abs.integrableOn_Icc
      ((hF.add continuous_const).integrableOn_Icc)
      (ae_restrict_mem measurableSet_Icc |>.mono fun t ht => hpoint t ht)
  have hvolume : (volume : Measure ℝ).real (Icc (-R) R) = 2 * R := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [integral_add hF.integrableOn_Icc (integrableOn_const (by simp)), integral_const,
    measureReal_restrict_apply_univ, hvolume, smul_eq_mul] at hint
  have hFTC := gluingCollarSmoothWarp_second_deriv_integral_le hε hR (r := r)
  linarith

/-- Both actual global integrations by parts for a localized smooth warp. -/
theorem gluingCollarLocalizedSmoothWarp_weak_second_derivative
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    (∫ s, gluingCollarLocalizedSmoothWarp r ε b s * deriv (deriv φ) s) =
      ∫ s, deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) s * φ s := by
  let F := gluingCollarLocalizedSmoothWarp r ε b
  have hF : ContDiff ℝ 2 F := gluingCollarLocalizedSmoothWarp_contDiff r hε b 2
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have h1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := F) (u' := deriv F) (v := deriv φ) (v' := deriv (deriv φ))
    (fun s _ => (hF.differentiable (by norm_num) s).hasDerivAt)
    (fun s _ => (hφ.differentiable_deriv_two s).hasDerivAt)
    ((hF.continuous.mul hφ'.continuous_deriv_one).integrable_of_hasCompactSupport
      hsupport.deriv.deriv.mul_left)
    ((hF'.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport
      hsupport.deriv.mul_left)
    ((hF.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport
      hsupport.deriv.mul_left)
  have h2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := deriv F) (u' := deriv (deriv F)) (v := φ) (v' := deriv φ)
    (fun s _ => (hF.differentiable_deriv_two s).hasDerivAt)
    (fun s _ => (hφ.differentiable (by norm_num) s).hasDerivAt)
    ((hF'.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport
      hsupport.deriv.mul_left)
    ((hF'.continuous_deriv_one.mul hφ.continuous).integrable_of_hasCompactSupport
      hsupport.mul_left)
    ((hF'.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hsupport.mul_left)
  dsimp only [F] at h1 h2
  rw [h1, h2, neg_neg]

/-- Compact-test error stays quantitative after genuine localization. -/
theorem gluingCollarLocalizedSmoothWarp_curvature_pairing_error
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (b : ContDiffBump (0 : ℝ))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    |(∫ s, gluingCollarLocalizedSmoothWarp r ε b s * deriv (deriv φ) s) -
        (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)| ≤
      Real.cosh r * ε * ∫ s, |deriv (deriv φ) s| := by
  have hφ'' : Continuous (deriv (deriv φ)) := hφ.deriv'.continuous_deriv_one
  have hI : Integrable (fun s : ℝ =>
      gluingCollarLocalizedSmoothWarp r ε b s * deriv (deriv φ) s) :=
    ((gluingCollarLocalizedSmoothWarp_continuous r ε b).mul hφ'').integrable_of_hasCompactSupport
      hsupport.deriv.deriv.mul_left
  have hJ : Integrable (fun s : ℝ => gluingCollarWarp r s * deriv (deriv φ) s) :=
    ((gluingCollarWarp_continuous r).mul hφ'').integrable_of_hasCompactSupport
      hsupport.deriv.deriv.mul_left
  have hAbs : Integrable (fun s : ℝ => |deriv (deriv φ) s|) :=
    hφ''.abs.integrable_of_hasCompactSupport hsupport.deriv.deriv.abs
  rw [gluingCollarRadialSecondDerivativeMeasure_weak_second_derivative hr hφ hsupport,
    ← integral_sub hI hJ]
  calc
    _ ≤ ∫ s, |gluingCollarLocalizedSmoothWarp r ε b s * deriv (deriv φ) s -
        gluingCollarWarp r s * deriv (deriv φ) s| := abs_integral_le_integral_abs
    _ ≤ ∫ s, (Real.cosh r * ε) * |deriv (deriv φ) s| := by
      apply integral_mono (hI.sub hJ).abs (hAbs.const_mul _)
      intro s
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (gluingCollarLocalizedSmoothWarp_uniform_bound r hε b s) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- Actual localized second derivatives converge against every compact
`C²` test to the native measure, with its unchanged seam atom. -/
theorem gluingCollarLocalizedSmoothWarp_curvature_pairing_tendsto
    {r : ℝ} (hr : 0 < r) (b : ContDiffBump (0 : ℝ))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupport : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ =>
      ∫ s, deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) s * φ s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖(∫ s, deriv (deriv (gluingCollarLocalizedSmoothWarp r ε b)) s * φ s) -
        (∫ s, φ s ∂gluingCollarRadialSecondDerivativeMeasure r)‖ ≤
      Real.cosh r * ε * ∫ s, |deriv (deriv φ) s| := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← gluingCollarLocalizedSmoothWarp_weak_second_derivative r hε b hφ hsupport,
      Real.norm_eq_abs]
    exact gluingCollarLocalizedSmoothWarp_curvature_pairing_error hr hε.le b hφ hsupport
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
  have hlim : Tendsto
      (fun ε : ℝ => Real.cosh r * ε * ∫ s, |deriv (deriv φ) s|)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun ε : ℝ => Real.cosh r * ε * ∫ s, |deriv (deriv φ) s|) := by
      fun_prop
    simpa using hc.tendsto 0
  exact hlim.mono_left nhdsWithin_le_nhds

#print axioms gluingCollarLocalizedSmoothWarp_weak_second_derivative
#print axioms gluingCollarLocalizedSmoothWarp_second_deriv
#print axioms gluingCollarLocalizedSmoothWarp_abs_second_deriv_le
#print axioms gluingCollarLocalizedSmoothWarp_uniform_abs_second_deriv_integral_bound
#print axioms gluingCollarLocalizedSmoothWarp_curvature_pairing_error
#print axioms gluingCollarLocalizedSmoothWarp_curvature_pairing_tendsto

end SystolicGrowth
