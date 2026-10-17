module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarConformalCurvature
public import Mathlib.MeasureTheory.VectorMeasure.Integral

@[expose] public section

/-!
# Finite curvature measure for the actual conformal collar factor

On every compact window in the genuine conformal coordinate target, the
negative weak Laplacian of the actual logarithmic metric factor is a finite
signed measure. Its magnitude is conformal area density plus the original
seam atom. Tensor tests identify this measure with the potential's weak
derivative, rather than merely assigning a coordinate curvature name.
-/

open Set MeasureTheory

namespace SystolicGrowth

noncomputable section

/-- Radial conformal area density of the actual logarithmic metric factor.
Only restrictions within the genuine chart target are used below. -/
def gluingCollarConformalRadialAreaMeasure {r : ℝ} (hr : 0 < r) : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (Real.exp (2 * gluingCollarConformalLogFactor hr u)))

/-- The genuine radial weak second-derivative magnitude, including the
unchanged original seam jump. -/
def gluingCollarConformalRadialCurvatureMagnitude {r : ℝ} (hr : 0 < r) : Measure ℝ :=
  gluingCollarConformalRadialAreaMeasure hr + ENNReal.ofReal (2 * Real.cosh r) • Measure.dirac 0

/-- Actual compact-window continuity constructs finite conformal area;
no global regularity outside the open coordinate target is assumed. -/
theorem gluingCollarConformalRadialAreaMeasure_restrict_isFinite
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) :
    IsFiniteMeasure ((gluingCollarConformalRadialAreaMeasure hr).restrict (Icc a b)) := by
  have hf : ContinuousOn (fun u => Real.exp (2 * gluingCollarConformalLogFactor hr u))
      (Icc a b) := Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul ((gluingCollarConformalLogFactor_continuousOn hr).mono hwindow))
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hf
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  rw [gluingCollarConformalRadialAreaMeasure, withDensity_apply _ measurableSet_Icc]
  calc
    (∫⁻ u in Icc a b, ENNReal.ofReal (Real.exp (2 * gluingCollarConformalLogFactor hr u))) ≤
        ∫⁻ _u in Icc a b, ENNReal.ofReal K := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact ENNReal.ofReal_le_ofReal (hK (mem_image_of_mem _ hu))
    _ < ⊤ := by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top isCompact_Icc.measure_lt_top

theorem gluingCollarConformalRadialCurvatureMagnitude_restrict_isFinite
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) :
    IsFiniteMeasure ((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)) := by
  letI := gluingCollarConformalRadialAreaMeasure_restrict_isFinite hr hwindow
  letI : IsFiniteMeasure (ENNReal.ofReal (2 * Real.cosh r) • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  rw [gluingCollarConformalRadialCurvatureMagnitude, Measure.restrict_add]
  infer_instance

/-- The compact radial restriction times angular Lebesgue measure on an
actual bounded interval, in the original unchanged angular coordinate. -/
def gluingCollarConformalCurvatureMagnitudeOnRectangle {r : ℝ}
    (hr : 0 < r) (a b u v : ℝ) : Measure (ℝ × ℝ) :=
  ((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)).prod
    (volume.restrict (Icc u v))

theorem gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite
    {r a b : ℝ} (hr : 0 < r)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target) (u v : ℝ) :
    IsFiniteMeasure (gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v) := by
  letI := gluingCollarConformalRadialCurvatureMagnitude_restrict_isFinite hr hwindow
  unfold gluingCollarConformalCurvatureMagnitudeOnRectangle
  infer_instance

/-- The finite negative weak curvature measure of the genuine conformal
factor on a compact coordinate rectangle. -/
def gluingCollarConformalCurvatureOnRectangle {r : ℝ} (hr : 0 < r)
    (a b : ℝ) (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (u v : ℝ) : SignedMeasure (ℝ × ℝ) := by
  letI := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  exact -(gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v).toSignedMeasure

theorem gluingCollarConformalCurvatureOnRectangle_nonpositive {r a b : ℝ}
    (hr : 0 < r) (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (u v : ℝ) : gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v ≤ 0 := by
  letI := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  exact neg_nonpos.mpr (Measure.zero_le_toSignedMeasure _)

/-- The exact finite total variation is the actual conformal area-plus-
seam magnitude, not an unspecified variation bound. -/
theorem gluingCollarConformalCurvatureOnRectangle_totalVariation {r a b : ℝ}
    (hr : 0 < r) (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (u v : ℝ) :
    (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).totalVariation =
      gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v := by
  let μ := gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v
  letI := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  let j : JordanDecomposition (ℝ × ℝ) :=
    { posPart := μ
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : j.toSignedMeasure = μ.toSignedMeasure := by
    simp [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero]
  change (-μ.toSignedMeasure).totalVariation = μ
  rw [SignedMeasure.totalVariation_neg, ← hj, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp [j]

theorem gluingCollarConformalCurvatureOnRectangle_totalVariation_isFinite {r a b : ℝ}
    (hr : 0 < r) (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (u v : ℝ) :
    IsFiniteMeasure (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).totalVariation := by
  rw [gluingCollarConformalCurvatureOnRectangle_totalVariation]
  exact gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v

/-- Continuous radial test pairings have the exact conformal area and
original seam mass on the actual chart window. -/
theorem gluingCollarConformalRadialCurvatureMagnitude_integral_Icc
    {r a b : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ s in Icc a b, φ s ∂gluingCollarConformalRadialCurvatureMagnitude hr) =
      (∫ s in a..b, Real.exp (2 * gluingCollarConformalLogFactor hr s) * φ s) +
        2 * Real.cosh r * φ 0 := by
  let density := gluingCollarConformalRadialAreaMeasure hr
  let atom := ENNReal.ofReal (2 * Real.cosh r) • Measure.dirac (0 : ℝ)
  letI := gluingCollarConformalRadialAreaMeasure_restrict_isFinite hr hwindow
  letI : IsFiniteMeasure atom := (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  have hdensityMass : density (Icc a b) ≠ ⊤ := by
    simpa only [Measure.restrict_apply_univ] using
      measure_ne_top ((gluingCollarConformalRadialAreaMeasure hr).restrict (Icc a b)) univ
  have hd : IntegrableOn φ (Icc a b) density :=
    hφ.continuousOn.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Icc
      (Subset.refl _) hdensityMass
  have hat : IntegrableOn φ (Icc a b) atom := hφ.integrableOn_Icc
  have hzero : (0 : ℝ) ∈ Icc a b := ⟨ha.le, hb.le⟩
  change (∫ s, φ s ∂(density + atom).restrict (Icc a b)) = _
  rw [Measure.restrict_add, integral_add_measure hd hat]
  have hf : ContinuousOn (fun u => Real.exp (2 * gluingCollarConformalLogFactor hr u))
      (Icc a b) := Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul ((gluingCollarConformalLogFactor_continuousOn hr).mono hwindow))
  have hdensity : (∫ s in Icc a b, φ s ∂density) =
      ∫ s in a..b, Real.exp (2 * gluingCollarConformalLogFactor hr s) * φ s := by
    rw [show density = volume.withDensity
        (fun u => ENNReal.ofReal (Real.exp (2 * gluingCollarConformalLogFactor hr u))) from rfl,
      setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        ((hf.aemeasurable measurableSet_Icc).ennreal_ofReal)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ measurableSet_Icc]
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show a ≤ b by linarith)]
  have hatom : (∫ s in Icc a b, φ s ∂atom) = 2 * Real.cosh r * φ 0 := by
    dsimp [atom]
    rw [Measure.restrict_smul, restrict_dirac]
    simp only [if_pos hzero, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.cosh r by positivity), smul_eq_mul]
  rw [hdensity, hatom]

/-- The actual radial measure pairing is the genuine log-factor weak
second derivative, under exactly the compact-test endpoint conditions. -/
theorem gluingCollarConformalRadialCurvatureMagnitude_weak_second_derivative_Icc
    {r a b : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0) :
    (∫ s in Icc a b, φ s ∂gluingCollarConformalRadialCurvatureMagnitude hr) =
      ∫ s in a..b, gluingCollarConformalLogFactor hr s * deriv (deriv φ) s := by
  rw [gluingCollarConformalRadialCurvatureMagnitude_integral_Icc hr ha hb hwindow hφ.continuous]
  simp_rw [gluingCollarConformalLogFactor_exp_two hr]
  exact (gluingCollarConformalLogFactor_weak_second_derivative_Icc
    hr ha hb hwindow hφ hφa hφb hφ'a hφ'b).symm

/-- The actual finite signed measure pairs against a genuine tensor test
as the negative radial weak second derivative of the actual conformal factor. -/
theorem gluingCollarConformalCurvatureOnRectangle_weak_radial_tensor
    {r a b : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (u v : ℝ) {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : Continuous ψ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0) :
    Integrable (fun p : ℝ × ℝ => φ p.1 * ψ p.2)
      (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).totalVariation ∧
    (∫ᵛ p : ℝ × ℝ, (φ p.1 * ψ p.2 : ℝ)
      ∂<•gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v) =
      -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
        gluingCollarConformalLogFactor hr p.1 * deriv (deriv φ) p.1 * ψ p.2) := by
  letI := gluingCollarConformalRadialCurvatureMagnitude_restrict_isFinite hr hwindow
  letI := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  have hmass : gluingCollarConformalRadialCurvatureMagnitude hr (Icc a b) ≠ ⊤ := by
    simpa only [Measure.restrict_apply_univ] using
      measure_ne_top ((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)) univ
  have hφint : Integrable φ ((gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)) :=
    hφ.continuous.continuousOn.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Icc
      (Subset.refl _) hmass
  have hψint : Integrable ψ (volume.restrict (Icc u v)) := hψ.integrableOn_Icc
  constructor
  · rw [gluingCollarConformalCurvatureOnRectangle_totalVariation,
      gluingCollarConformalCurvatureMagnitudeOnRectangle]
    exact hφint.mul_prod hψint
  · rw [gluingCollarConformalCurvatureOnRectangle, VectorMeasure.integral_neg_vectorMeasure,
      VectorMeasure.integral_toSignedMeasure, gluingCollarConformalCurvatureMagnitudeOnRectangle,
      integral_prod_mul,
      gluingCollarConformalRadialCurvatureMagnitude_weak_second_derivative_Icc
        hr ha hb hwindow hφ hφa hφb hφ'a hφ'b,
      Measure.volume_eq_prod,
      setIntegral_prod_mul (fun s => gluingCollarConformalLogFactor hr s * deriv (deriv φ) s)
        ψ (Icc a b) (Icc u v),
      integral_Icc_eq_integral_Ioc (x := a) (y := b),
      ← intervalIntegral.integral_of_le (show a ≤ b by linarith)]

/-- Genuine two-dimensional tensor tests pair with the negative Euclidean
Laplacian of the actual conformal potential. The angular derivative term
vanishes by the endpoint conditions, not by a curvature assumption. -/
theorem gluingCollarConformalCurvatureOnRectangle_weak_laplacian_tensor
    {r a b u v : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (huv : u ≤ v) {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hφa : φ a = 0) (hφb : φ b = 0)
    (hφ'a : deriv φ a = 0) (hφ'b : deriv φ b = 0)
    (hψ'u : deriv ψ u = 0) (hψ'v : deriv ψ v = 0) :
    Integrable (fun p : ℝ × ℝ => φ p.1 * ψ p.2)
      (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).totalVariation ∧
    IntegrableOn (fun p : ℝ × ℝ => gluingCollarConformalLogFactor hr p.1 *
      (deriv (deriv φ) p.1 * ψ p.2 + φ p.1 * deriv (deriv ψ) p.2))
      (Icc a b ×ˢ Icc u v) ∧
    (∫ᵛ p : ℝ × ℝ, (φ p.1 * ψ p.2 : ℝ)
      ∂<•gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v) =
      -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
        gluingCollarConformalLogFactor hr p.1 *
          (deriv (deriv φ) p.1 * ψ p.2 + φ p.1 * deriv (deriv ψ) p.2)) := by
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hψ' : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  have hφ'' : Continuous (deriv (deriv φ)) := hφ'.continuous_deriv_one
  have hψ'' : Continuous (deriv (deriv ψ)) := hψ'.continuous_deriv_one
  have hF : ContinuousOn (gluingCollarConformalLogFactor hr) (Icc a b) :=
    (gluingCollarConformalLogFactor_continuousOn hr).mono hwindow
  have hi1 : IntegrableOn (fun p : ℝ × ℝ =>
      gluingCollarConformalLogFactor hr p.1 * deriv (deriv φ) p.1 * ψ p.2)
      (Icc a b ×ˢ Icc u v) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (hF.mul hφ''.continuousOn).integrableOn_Icc.mul_prod hψ.continuous.integrableOn_Icc
  have hi2 : IntegrableOn (fun p : ℝ × ℝ =>
      gluingCollarConformalLogFactor hr p.1 * φ p.1 * deriv (deriv ψ) p.2)
      (Icc a b ×ˢ Icc u v) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (hF.mul hφ.continuous.continuousOn).integrableOn_Icc.mul_prod hψ''.integrableOn_Icc
  have hangular : (∫ t in Icc u v, deriv (deriv ψ) t) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hψ'.continuous.continuousOn
        (fun t _ => (hψ.differentiable_deriv_two t).hasDerivAt) (hψ''.intervalIntegrable u v),
      hψ'v, hψ'u, sub_self]
  have hzero : (∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
      gluingCollarConformalLogFactor hr p.1 * φ p.1 * deriv (deriv ψ) p.2) = 0 := by
    rw [Measure.volume_eq_prod,
      setIntegral_prod_mul (fun s => gluingCollarConformalLogFactor hr s * φ s)
        (deriv (deriv ψ)) (Icc a b) (Icc u v), hangular, mul_zero]
  have hsplit : (fun p : ℝ × ℝ => gluingCollarConformalLogFactor hr p.1 *
      (deriv (deriv φ) p.1 * ψ p.2 + φ p.1 * deriv (deriv ψ) p.2)) =
      (fun p => gluingCollarConformalLogFactor hr p.1 * deriv (deriv φ) p.1 * ψ p.2 +
        gluingCollarConformalLogFactor hr p.1 * φ p.1 * deriv (deriv ψ) p.2) := by
    funext p
    ring
  obtain ⟨htest, hradial⟩ := gluingCollarConformalCurvatureOnRectangle_weak_radial_tensor
    hr ha hb hwindow u v hφ hψ.continuous hφa hφb hφ'a hφ'b
  refine ⟨htest, ?_, ?_⟩
  · rw [hsplit]
    exact hi1.add hi2
  · rw [hsplit, integral_add hi1 hi2, hzero, add_zero]
    exact hradial

/-- The ordinary Euclidean directional derivative of a collar-coordinate
test, used to express its actual weak Laplacian. -/
def gluingCollarTestDirectionalDerivative (η : (ℝ × ℝ) → ℝ)
    (e p : ℝ × ℝ) : ℝ := fderiv ℝ η p e

theorem gluingCollarTestDirectionalDerivative_contDiff {η : (ℝ × ℝ) → ℝ}
    (hη : ContDiff ℝ 2 η) (e : ℝ × ℝ) :
    ContDiff ℝ 1 (gluingCollarTestDirectionalDerivative η e) := by
  exact (hη.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

theorem gluingCollarTestSecondDirectionalDerivative_continuous {η : (ℝ × ℝ) → ℝ}
    (hη : ContDiff ℝ 2 η) (e : ℝ × ℝ) :
    Continuous (gluingCollarTestDirectionalDerivative
      (gluingCollarTestDirectionalDerivative η e) e) := by
  exact ((gluingCollarTestDirectionalDerivative_contDiff hη e).contDiff_fderiv_apply
    (m := 0) (by norm_num)).continuous.comp (continuous_id.prodMk continuous_const)

theorem gluingCollarTestDirectionalDerivative_radial {η : (ℝ × ℝ) → ℝ}
    (hη : Differentiable ℝ η) (s θ : ℝ) :
    deriv (fun t => η (t, θ)) s = gluingCollarTestDirectionalDerivative η (1, 0) (s, θ) := by
  exact ((hη (s, θ)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s θ))).deriv

theorem gluingCollarTestDirectionalDerivative_angular {η : (ℝ × ℝ) → ℝ}
    (hη : Differentiable ℝ η) (s θ : ℝ) :
    deriv (fun t => η (s, t)) θ = gluingCollarTestDirectionalDerivative η (0, 1) (s, θ) := by
  exact ((hη (s, θ)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ s).prodMk (hasDerivAt_id θ))).deriv

theorem gluingCollarTestSecondDirectionalDerivative_radial {η : (ℝ × ℝ) → ℝ}
    (hη : ContDiff ℝ 2 η) (s θ : ℝ) :
    deriv (deriv (fun t => η (t, θ))) s =
      gluingCollarTestDirectionalDerivative (gluingCollarTestDirectionalDerivative η (1, 0))
        (1, 0) (s, θ) := by
  have hfirst : deriv (fun t => η (t, θ)) =
      fun t => gluingCollarTestDirectionalDerivative η (1, 0) (t, θ) := by
    funext t
    exact gluingCollarTestDirectionalDerivative_radial (hη.differentiable (by norm_num)) t θ
  rw [hfirst]
  exact gluingCollarTestDirectionalDerivative_radial
    ((gluingCollarTestDirectionalDerivative_contDiff hη (1, 0)).differentiable (by norm_num)) s θ

theorem gluingCollarTestSecondDirectionalDerivative_angular {η : (ℝ × ℝ) → ℝ}
    (hη : ContDiff ℝ 2 η) (s θ : ℝ) :
    deriv (deriv (fun t => η (s, t))) θ =
      gluingCollarTestDirectionalDerivative (gluingCollarTestDirectionalDerivative η (0, 1))
        (0, 1) (s, θ) := by
  have hfirst : deriv (fun t => η (s, t)) =
      fun t => gluingCollarTestDirectionalDerivative η (0, 1) (s, t) := by
    funext t
    exact gluingCollarTestDirectionalDerivative_angular (hη.differentiable (by norm_num)) s t
  rw [hfirst]
  exact gluingCollarTestDirectionalDerivative_angular
    ((gluingCollarTestDirectionalDerivative_contDiff hη (0, 1)).differentiable (by norm_num)) s θ

/-- The trace of the genuine Euclidean second derivative in the actual
radial and unchanged angular conformal coordinates. -/
def gluingCollarTestLaplacian (η : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  gluingCollarTestDirectionalDerivative (gluingCollarTestDirectionalDerivative η (1, 0)) (1, 0) p +
    gluingCollarTestDirectionalDerivative (gluingCollarTestDirectionalDerivative η (0, 1)) (0, 1) p

/-- Arbitrary genuine `C²` coordinate tests identify the finite signed
curvature with the negative weak Laplacian of the actual log factor.
The endpoint hypotheses are precisely zero test and zero normal derivative
on the radial boundary, and zero normal derivative on the angular boundary. -/
theorem gluingCollarConformalCurvatureOnRectangle_weak_laplacian
    {r a b u v : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (huv : u ≤ v) {η : (ℝ × ℝ) → ℝ} (hη : ContDiff ℝ 2 η)
    (hradial : ∀ θ ∈ Icc u v,
      η (a, θ) = 0 ∧ η (b, θ) = 0 ∧
      gluingCollarTestDirectionalDerivative η (1, 0) (a, θ) = 0 ∧
      gluingCollarTestDirectionalDerivative η (1, 0) (b, θ) = 0)
    (hangular : ∀ s ∈ Icc a b,
      gluingCollarTestDirectionalDerivative η (0, 1) (s, u) = 0 ∧
      gluingCollarTestDirectionalDerivative η (0, 1) (s, v) = 0) :
    Integrable η
      (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).totalVariation ∧
    IntegrableOn (fun p : ℝ × ℝ =>
      gluingCollarConformalLogFactor hr p.1 * gluingCollarTestLaplacian η p)
      (Icc a b ×ˢ Icc u v) ∧
    (∫ᵛ p : ℝ × ℝ, η p ∂<•gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v) =
      -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
        gluingCollarConformalLogFactor hr p.1 * gluingCollarTestLaplacian η p) := by
  let ν := (gluingCollarConformalRadialCurvatureMagnitude hr).restrict (Icc a b)
  let μ := gluingCollarConformalCurvatureMagnitudeOnRectangle hr a b u v
  let D1 := gluingCollarTestDirectionalDerivative
    (gluingCollarTestDirectionalDerivative η (1, 0)) (1, 0)
  let D2 := gluingCollarTestDirectionalDerivative
    (gluingCollarTestDirectionalDerivative η (0, 1)) (0, 1)
  let F := gluingCollarConformalLogFactor hr
  letI := gluingCollarConformalRadialCurvatureMagnitude_restrict_isFinite hr hwindow
  letI := gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite hr hwindow u v
  have hrect : IsCompact (Icc a b ×ˢ Icc u v) := isCompact_Icc.prod isCompact_Icc
  have hμrestrict : μ.restrict (Icc a b ×ˢ Icc u v) = μ := by
    dsimp [μ, gluingCollarConformalCurvatureMagnitudeOnRectangle]
    rw [← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, inter_self, inter_self]
  have hηint : Integrable η μ := by
    have h : IntegrableOn η (Icc a b ×ˢ Icc u v) μ :=
      hη.continuous.continuousOn.integrableOn_compact hrect
    simpa only [IntegrableOn, hμrestrict] using h
  have hF : ContinuousOn F (Icc a b) :=
    (gluingCollarConformalLogFactor_continuousOn hr).mono hwindow
  have hFrect : ContinuousOn (fun p : ℝ × ℝ => F p.1) (Icc a b ×ˢ Icc u v) :=
    hF.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hD1 : Continuous D1 := gluingCollarTestSecondDirectionalDerivative_continuous hη (1, 0)
  have hD2 : Continuous D2 := gluingCollarTestSecondDirectionalDerivative_continuous hη (0, 1)
  have hi1 : IntegrableOn (fun p : ℝ × ℝ => F p.1 * D1 p) (Icc a b ×ˢ Icc u v) :=
    (hFrect.mul hD1.continuousOn).integrableOn_compact hrect
  have hi2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 * D2 p) (Icc a b ×ˢ Icc u v) :=
    (hFrect.mul hD2.continuousOn).integrableOn_compact hrect
  have hi1prod : Integrable (fun p : ℝ × ℝ => F p.1 * D1 p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc u v))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] using hi1
  have hi2prod : Integrable (fun p : ℝ × ℝ => F p.1 * D2 p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc u v))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] using hi2
  have hrpair : (∫ p, η p ∂μ) = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v, F p.1 * D1 p := by
    change (∫ p, η p ∂ν.prod (volume.restrict (Icc u v))) = _
    rw [integral_prod_symm η hηint, Measure.volume_eq_prod,
      ← Measure.prod_restrict, integral_prod_symm _ hi1prod]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : ContDiff ℝ 2 (fun t => η (t, θ)) :=
      hη.comp (contDiff_id.prodMk contDiff_const)
    obtain ⟨hleft, hright, hdleft, hdright⟩ := hradial θ hθ
    have hdleft' : deriv (fun t => η (t, θ)) a = 0 := by
      rw [gluingCollarTestDirectionalDerivative_radial (hη.differentiable (by norm_num))]
      exact hdleft
    have hdright' : deriv (fun t => η (t, θ)) b = 0 := by
      rw [gluingCollarTestDirectionalDerivative_radial (hη.differentiable (by norm_num))]
      exact hdright
    change (∫ t in Icc a b, η (t, θ) ∂gluingCollarConformalRadialCurvatureMagnitude hr) = _
    rw [gluingCollarConformalRadialCurvatureMagnitude_weak_second_derivative_Icc
      hr ha hb hwindow hs hleft hright hdleft' hdright',
      intervalIntegral.integral_of_le (show a ≤ b by linarith),
      ← integral_Icc_eq_integral_Ioc]
    simp_rw [gluingCollarTestSecondDirectionalDerivative_radial hη]
    rfl
  have hangzero : (∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v, F p.1 * D2 p) = 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hi2prod]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [integral_const_mul]
    have hslice : ContDiff ℝ 2 (fun θ => η (s, θ)) :=
      hη.comp (contDiff_const.prodMk contDiff_id)
    have hslice' : ContDiff ℝ 1 (deriv (fun θ => η (s, θ))) := hslice.deriv'
    have hslice'' : Continuous (deriv (deriv (fun θ => η (s, θ)))) :=
      hslice'.continuous_deriv_one
    have hleft : deriv (fun θ => η (s, θ)) u = 0 := by
      rw [gluingCollarTestDirectionalDerivative_angular (hη.differentiable (by norm_num))]
      exact (hangular s hs).1
    have hright : deriv (fun θ => η (s, θ)) v = 0 := by
      rw [gluingCollarTestDirectionalDerivative_angular (hη.differentiable (by norm_num))]
      exact (hangular s hs).2
    have hangularint : (∫ θ in Icc u v, D2 (s, θ)) = 0 := by
      simp_rw [show ∀ θ, D2 (s, θ) = deriv (deriv (fun t => η (s, t))) θ from
        fun θ => (gluingCollarTestSecondDirectionalDerivative_angular hη s θ).symm]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hslice'.continuous.continuousOn
          (fun θ _ => (hslice.differentiable_deriv_two θ).hasDerivAt)
          (hslice''.intervalIntegrable u v), hright, hleft, sub_self]
    rw [hangularint, mul_zero]
    rfl
  have hlap : (fun p : ℝ × ℝ => F p.1 * gluingCollarTestLaplacian η p) =
      (fun p => F p.1 * D1 p + F p.1 * D2 p) := by
    funext p
    exact mul_add _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [gluingCollarConformalCurvatureOnRectangle_totalVariation]
    exact hηint
  · change IntegrableOn (fun p : ℝ × ℝ => F p.1 * gluingCollarTestLaplacian η p) _
    rw [hlap]
    exact hi1.add hi2
  · rw [gluingCollarConformalCurvatureOnRectangle, VectorMeasure.integral_neg_vectorMeasure,
      VectorMeasure.integral_toSignedMeasure]
    change -(∫ p, η p ∂μ) = -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
      F p.1 * gluingCollarTestLaplacian η p)
    rw [hrpair, hlap, integral_add hi1 hi2, hangzero, add_zero]

/-- The usual compactly contained `C²` test contract discharges all
boundary terms automatically. This is the full two-variable weak
Laplacian identity, not only a tensor-test statement. -/
theorem gluingCollarConformalCurvatureOnRectangle_weak_laplacian_of_tsupport_subset
    {r a b u v : ℝ} (hr : 0 < r) (ha : a < 0) (hb : 0 < b)
    (hwindow : Icc a b ⊆ (gluingCollarConformalRadialChart hr).target)
    (huv : u ≤ v) {η : (ℝ × ℝ) → ℝ} (hη : ContDiff ℝ 2 η)
    (hsupport : tsupport η ⊆ Ioo a b ×ˢ Ioo u v) :
    Integrable η
      (gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v).totalVariation ∧
    IntegrableOn (fun p : ℝ × ℝ =>
      gluingCollarConformalLogFactor hr p.1 * gluingCollarTestLaplacian η p)
      (Icc a b ×ˢ Icc u v) ∧
    (∫ᵛ p : ℝ × ℝ, η p ∂<•gluingCollarConformalCurvatureOnRectangle hr a b hwindow u v) =
      -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
        gluingCollarConformalLogFactor hr p.1 * gluingCollarTestLaplacian η p) := by
  apply gluingCollarConformalCurvatureOnRectangle_weak_laplacian hr ha hb hwindow huv hη
  · intro θ _
    have hleft : (a, θ) ∉ tsupport η := fun h => (lt_irrefl a) (hsupport h).1.1
    have hright : (b, θ) ∉ tsupport η := fun h => (lt_irrefl b) (hsupport h).1.2
    refine ⟨image_eq_zero_of_notMem_tsupport hleft, image_eq_zero_of_notMem_tsupport hright,
      ?_, ?_⟩
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hleft]
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hright]
  · intro s _
    have hleft : (s, u) ∉ tsupport η := fun h => (lt_irrefl u) (hsupport h).2.1
    have hright : (s, v) ∉ tsupport η := fun h => (lt_irrefl v) (hsupport h).2.2
    constructor
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hleft]
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hright]

#print axioms gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite
#print axioms gluingCollarConformalCurvatureMagnitudeOnRectangle_isFinite
#print axioms gluingCollarConformalCurvatureOnRectangle_totalVariation
#print axioms gluingCollarConformalRadialCurvatureMagnitude_weak_second_derivative_Icc
#print axioms gluingCollarConformalCurvatureOnRectangle_weak_radial_tensor
#print axioms gluingCollarConformalCurvatureOnRectangle_weak_laplacian_tensor
#print axioms gluingCollarConformalCurvatureOnRectangle_weak_laplacian
#print axioms gluingCollarConformalCurvatureOnRectangle_weak_laplacian_of_tsupport_subset

end
end SystolicGrowth
