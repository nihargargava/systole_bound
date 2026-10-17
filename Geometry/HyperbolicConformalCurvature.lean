module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarConformalCurvatureMeasure
public import Geometry.HyperbolicArea
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

/-!
# Actual hyperbolic curvature in upper-half-plane coordinates

The coordinate area measure below is the pushforward of the original
upper-half-plane volume, not an independently supplied density. Its
negative is identified with the weak Laplacian of the literal conformal
factor `-log y` on compact rectangles contained in the upper half-plane.
-/

open Set MeasureTheory
open scoped UpperHalfPlane NNReal

namespace SystolicGrowth

noncomputable section

/-- The ordinary real and imaginary coordinates of the original upper half-plane. -/
def hyperbolicConformalCoordinates (z : ℍ) : ℝ × ℝ := (z.re, z.im)

theorem hyperbolicConformalCoordinates_measurableEmbedding :
    MeasurableEmbedding hyperbolicConformalCoordinates :=
  Complex.measurableEquivRealProd.measurableEmbedding.comp
    UpperHalfPlane.measurableEmbedding_coe

/-- The actual hyperbolic volume pushed into its genuine Euclidean coordinates. -/
def hyperbolicConformalAreaMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure ℍ).map hyperbolicConformalCoordinates

/-- The literal conformal factor of the original upper-half-plane metric. -/
def hyperbolicConformalLogFactor (p : ℝ × ℝ) : ℝ := -Real.log p.2

/-- The original area pushforward has the genuine `y⁻²` density on every
measurable set contained in the coordinate domain. -/
theorem hyperbolicConformalAreaMeasure_apply {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hpositive : ∀ p ∈ s, 0 < p.2) :
    hyperbolicConformalAreaMeasure s =
      ∫⁻ p : ℝ × ℝ in s, ENNReal.ofReal (1 / p.2 ^ 2) := by
  have himage : UpperHalfPlane.coe '' (hyperbolicConformalCoordinates ⁻¹' s) =
      Complex.measurableEquivRealProd ⁻¹' s := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hz
      exact ⟨⟨z, hpositive (z.re, z.im) hz⟩, hz, rfl⟩
  rw [hyperbolicConformalAreaMeasure,
    Measure.map_apply hyperbolicConformalCoordinates_measurableEmbedding.measurable hs,
    UpperHalfPlane.volume_eq_lintegral, himage]
  have heq : (fun z : ℂ => (↑((1 / ‖z.im‖₊) ^ 2 : NNReal) : ENNReal)) =
      fun z => ENNReal.ofReal (1 / (Complex.measurableEquivRealProd z).2 ^ 2) := by
    funext z
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp only [NNReal.coe_pow, NNReal.coe_inv, coe_nnnorm,
      Real.norm_eq_abs, one_div, inv_pow, sq_abs, Complex.measurableEquivRealProd_apply]
  rw [heq]
  convert! Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding _ _
    using 1
  rfl

/-- The actual first Frechet derivative of `-log y`. -/
theorem hyperbolicConformalLogFactor_hasFDerivAt {p : ℝ × ℝ} (hp : 0 < p.2) :
    HasFDerivAt hyperbolicConformalLogFactor
      (-(p.2⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  exact (hasFDerivAt_snd.log hp.ne').neg

theorem hyperbolicConformalLogFactor_first_x {p : ℝ × ℝ} (hp : 0 < p.2) :
    gluingCollarTestDirectionalDerivative hyperbolicConformalLogFactor (1, 0) p = 0 := by
  simp [gluingCollarTestDirectionalDerivative,
    (hyperbolicConformalLogFactor_hasFDerivAt hp).fderiv]

theorem hyperbolicConformalLogFactor_first_y {p : ℝ × ℝ} (hp : 0 < p.2) :
    gluingCollarTestDirectionalDerivative hyperbolicConformalLogFactor (0, 1) p = -p.2⁻¹ := by
  simp [gluingCollarTestDirectionalDerivative,
    (hyperbolicConformalLogFactor_hasFDerivAt hp).fderiv]

/-- The genuine trace of the two second Frechet derivatives is the
original hyperbolic area density, on the actual coordinate domain. -/
theorem hyperbolicConformalLogFactor_laplacian {p : ℝ × ℝ} (hp : 0 < p.2) :
    gluingCollarTestLaplacian hyperbolicConformalLogFactor p = 1 / p.2 ^ 2 := by
  have hpos : ∀ᶠ q : ℝ × ℝ in nhds p, 0 < q.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  have hx : gluingCollarTestDirectionalDerivative hyperbolicConformalLogFactor (1, 0) =ᶠ[nhds p]
      fun _ => (0 : ℝ) := hpos.mono fun q hq => hyperbolicConformalLogFactor_first_x hq
  have hy : gluingCollarTestDirectionalDerivative hyperbolicConformalLogFactor (0, 1) =ᶠ[nhds p]
      fun q => -q.2⁻¹ := hpos.mono fun q hq => hyperbolicConformalLogFactor_first_y hq
  have hdy : HasFDerivAt (fun q : ℝ × ℝ => -q.2⁻¹)
      (-(-(p.2 ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((hasDerivAt_inv hp.ne').comp_hasFDerivAt p
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ))).neg
  rw [gluingCollarTestLaplacian, gluingCollarTestDirectionalDerivative,
    gluingCollarTestDirectionalDerivative, hx.fderiv_eq, hy.fderiv_eq, hdy.fderiv]
  simp

/-- The restriction of original hyperbolic area to a compact coordinate rectangle. -/
def hyperbolicConformalAreaOnRectangle (a b u v : ℝ) : Measure (ℝ × ℝ) :=
  hyperbolicConformalAreaMeasure.restrict (Icc a b ×ˢ Icc u v)

/-- The density formula is derived from original hyperbolic volume, also
as an equality of measures rather than merely a numerical mass formula. -/
theorem hyperbolicConformalAreaOnRectangle_eq_withDensity {a b u v : ℝ}
    (hu : 0 < u) :
    hyperbolicConformalAreaOnRectangle a b u v =
      (volume.restrict (Icc a b ×ˢ Icc u v)).withDensity
        (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  ext s hs
  rw [hyperbolicConformalAreaOnRectangle, Measure.restrict_apply hs,
    hyperbolicConformalAreaMeasure_apply (hs.inter (measurableSet_Icc.prod measurableSet_Icc))
      (fun p hp => hu.trans_le hp.2.2.1), withDensity_apply _ hs,
    Measure.restrict_restrict hs]

theorem hyperbolicConformalDensity_continuousOn {a b u v : ℝ} (hu : 0 < u) :
    ContinuousOn (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (Icc a b ×ˢ Icc u v) :=
  continuousOn_const.div (continuous_snd.continuousOn.pow 2)
    (fun _ hp => pow_ne_zero 2 (hu.trans_le hp.2.1).ne')

/-- Actual hyperbolic area on a positive-height compact rectangle is finite. -/
theorem hyperbolicConformalAreaOnRectangle_isFinite {a b u v : ℝ} (hu : 0 < u) :
    IsFiniteMeasure (hyperbolicConformalAreaOnRectangle a b u v) := by
  rw [hyperbolicConformalAreaOnRectangle_eq_withDensity hu]
  have hi : IntegrableOn (fun p : ℝ × ℝ => 1 / p.2 ^ 2) (Icc a b ×ˢ Icc u v) :=
    (hyperbolicConformalDensity_continuousOn hu).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  exact isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by positivity)).mpr hi)

/-- The finite signed smooth-interior curvature candidate is negative
actual hyperbolic area in the genuine coordinate chart. -/
def hyperbolicConformalCurvatureOnRectangle (a b : ℝ) {u : ℝ} (hu : 0 < u) (v : ℝ) :
    SignedMeasure (ℝ × ℝ) := by
  letI := hyperbolicConformalAreaOnRectangle_isFinite (a := a) (b := b) (v := v) hu
  exact -(hyperbolicConformalAreaOnRectangle a b u v).toSignedMeasure

/-- No additional variation measure is supplied: the actual original area
is exactly the total variation of the negative smooth curvature. -/
theorem hyperbolicConformalCurvatureOnRectangle_totalVariation (a b : ℝ)
    {u : ℝ} (hu : 0 < u) (v : ℝ) :
    (hyperbolicConformalCurvatureOnRectangle a b hu v).totalVariation =
      hyperbolicConformalAreaOnRectangle a b u v := by
  letI := hyperbolicConformalAreaOnRectangle_isFinite (a := a) (b := b) (v := v) hu
  let μ := hyperbolicConformalAreaOnRectangle a b u v
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

/-- The actual smooth-interior signed curvature is nonpositive. -/
theorem hyperbolicConformalCurvatureOnRectangle_nonpositive (a b : ℝ)
    {u : ℝ} (hu : 0 < u) (v : ℝ) :
    hyperbolicConformalCurvatureOnRectangle a b hu v ≤ 0 := by
  letI := hyperbolicConformalAreaOnRectangle_isFinite (a := a) (b := b) (v := v) hu
  exact neg_nonpos.mpr (Measure.zero_le_toSignedMeasure _)

/-- Its finite total variation is a proved consequence of the actual
positive-height coordinate rectangle, not a supplied measure assumption. -/
theorem hyperbolicConformalCurvatureOnRectangle_totalVariation_isFinite (a b : ℝ)
    {u : ℝ} (hu : 0 < u) (v : ℝ) :
    IsFiniteMeasure (hyperbolicConformalCurvatureOnRectangle a b hu v).totalVariation := by
  rw [hyperbolicConformalCurvatureOnRectangle_totalVariation]
  exact hyperbolicConformalAreaOnRectangle_isFinite hu

/-- The coordinate signed pairing is literally minus the original
upper-half-plane volume pairing on the genuine coordinate preimage. -/
theorem hyperbolicConformalCurvatureOnRectangle_integral_eq_hyperbolicVolume
    (a b : ℝ) {u : ℝ} (hu : 0 < u) (v : ℝ) (η : (ℝ × ℝ) → ℝ) :
    (∫ᵛ p : ℝ × ℝ, η p ∂<•hyperbolicConformalCurvatureOnRectangle a b hu v) =
      -(∫ z : ℍ in hyperbolicConformalCoordinates ⁻¹' (Icc a b ×ˢ Icc u v),
        η (hyperbolicConformalCoordinates z)) := by
  letI := hyperbolicConformalAreaOnRectangle_isFinite (a := a) (b := b) (v := v) hu
  rw [hyperbolicConformalCurvatureOnRectangle, VectorMeasure.integral_neg_vectorMeasure,
    VectorMeasure.integral_toSignedMeasure, hyperbolicConformalAreaOnRectangle,
    hyperbolicConformalAreaMeasure,
    Measure.restrict_map hyperbolicConformalCoordinates_measurableEmbedding.measurable
      (measurableSet_Icc.prod measurableSet_Icc),
    hyperbolicConformalCoordinates_measurableEmbedding.integral_map]

/-- The usual test pairing with the actual original area is the derived
Euclidean density integral. -/
theorem hyperbolicConformalAreaOnRectangle_integral {a b u v : ℝ} (hu : 0 < u)
    (η : (ℝ × ℝ) → ℝ) :
    (∫ p, η p ∂hyperbolicConformalAreaOnRectangle a b u v) =
      ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v, (1 / p.2 ^ 2) * η p := by
  rw [hyperbolicConformalAreaOnRectangle_eq_withDensity hu,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / p.2 ^ 2)]

/-- Actual twice-integrated differentiation of `-log y`, for arbitrary
compact `C²` tests with their usual vanishing boundary jets. -/
theorem hyperbolicConformalLogFactor_weak_second_derivative_Icc
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφu : φ u = 0) (hφv : φ v = 0)
    (hφ'u : deriv φ u = 0) (hφ'v : deriv φ v = 0) :
    (∫ y in u..v, -Real.log y * deriv (deriv φ) y) =
      ∫ y in u..v, (1 / y ^ 2) * φ y := by
  let F : ℝ → ℝ := fun y => -Real.log y
  let B : ℝ → ℝ := fun y => -y⁻¹
  let W : ℝ → ℝ := fun y => F y * deriv φ y - B y * φ y
  let H : ℝ → ℝ := fun y => F y * deriv (deriv φ) y - (1 / y ^ 2) * φ y
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hφ'' : Continuous (deriv (deriv φ)) := hφ'.continuous_deriv_one
  have hpos (y : ℝ) (hy : y ∈ Icc u v) : 0 < y := hu.trans_le hy.1
  have hF : ContinuousOn F (Icc u v) :=
    (Real.continuousOn_log.mono fun y hy => (hpos y hy).ne').neg
  have hB : ContinuousOn B (Icc u v) :=
    (continuousOn_id.inv₀ fun y hy => (hpos y hy).ne').neg
  have hA : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (Icc u v) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (hpos y hy).ne')
  have hW : ContinuousOn W (Icc u v) :=
    (hF.mul hφ'.continuous.continuousOn).sub (hB.mul hφ.continuous.continuousOn)
  have hH : ContinuousOn H (Icc u v) :=
    (hF.mul hφ''.continuousOn).sub (hA.mul hφ.continuous.continuousOn)
  have hW' (y : ℝ) (hy : y ∈ Ioo u v) : HasDerivAt W (H y) y := by
    have hlog : HasDerivAt F (-y⁻¹) y :=
      (Real.hasDerivAt_log (hpos y (Ioo_subset_Icc_self hy)).ne').neg
    have hinv : HasDerivAt B (1 / y ^ 2) y := by
      convert! (hasDerivAt_inv (hpos y (Ioo_subset_Icc_self hy)).ne').neg using 1
      simp
    convert (hlog.mul (hφ.differentiable_deriv_two y).hasDerivAt).sub
      (hinv.mul (hφ.differentiable (by norm_num) y).hasDerivAt) using 1 <;>
      first | rfl | dsimp [H, F, B]; ring
  have hweak : (∫ y in u..v, H y) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hW hW'
      (hH.intervalIntegrable_of_Icc huv)]
    simp [W, hφu, hφv, hφ'u, hφ'v]
  have hiF : IntervalIntegrable (fun y => F y * deriv (deriv φ) y) volume u v :=
    (hF.mul hφ''.continuousOn).intervalIntegrable_of_Icc huv
  have hiA : IntervalIntegrable (fun y => (1 / y ^ 2) * φ y) volume u v :=
    (hA.mul hφ.continuous.continuousOn).intervalIntegrable_of_Icc huv
  rw [show H = fun y => F y * deriv (deriv φ) y - (1 / y ^ 2) * φ y from rfl,
    intervalIntegral.integral_sub hiF hiA, sub_eq_zero] at hweak
  exact hweak

/-- Arbitrary genuine `C²` tests identify the finite negative original
hyperbolic area with the weak Laplacian of the actual conformal factor.
The boundary conditions are only the usual vanishing test jets. -/
theorem hyperbolicConformalCurvatureOnRectangle_weak_laplacian
    {a b u v : ℝ} (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v)
    {η : (ℝ × ℝ) → ℝ} (hη : ContDiff ℝ 2 η)
    (hx : ∀ y ∈ Icc u v,
      gluingCollarTestDirectionalDerivative η (1, 0) (a, y) = 0 ∧
      gluingCollarTestDirectionalDerivative η (1, 0) (b, y) = 0)
    (hy : ∀ x ∈ Icc a b,
      η (x, u) = 0 ∧ η (x, v) = 0 ∧
      gluingCollarTestDirectionalDerivative η (0, 1) (x, u) = 0 ∧
      gluingCollarTestDirectionalDerivative η (0, 1) (x, v) = 0) :
    Integrable η (hyperbolicConformalCurvatureOnRectangle a b hu v).totalVariation ∧
    IntegrableOn (fun p : ℝ × ℝ =>
      hyperbolicConformalLogFactor p * gluingCollarTestLaplacian η p)
      (Icc a b ×ˢ Icc u v) ∧
    (∫ᵛ p : ℝ × ℝ, η p ∂<•hyperbolicConformalCurvatureOnRectangle a b hu v) =
      -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
        hyperbolicConformalLogFactor p * gluingCollarTestLaplacian η p) := by
  let μ := hyperbolicConformalAreaOnRectangle a b u v
  let D1 := gluingCollarTestDirectionalDerivative
    (gluingCollarTestDirectionalDerivative η (1, 0)) (1, 0)
  let D2 := gluingCollarTestDirectionalDerivative
    (gluingCollarTestDirectionalDerivative η (0, 1)) (0, 1)
  let F : ℝ → ℝ := fun y => -Real.log y
  let A : ℝ × ℝ → ℝ := fun p => (1 / p.2 ^ 2) * η p
  letI := hyperbolicConformalAreaOnRectangle_isFinite (a := a) (b := b) (v := v) hu
  have hrect : IsCompact (Icc a b ×ˢ Icc u v) := isCompact_Icc.prod isCompact_Icc
  have hμrestrict : μ.restrict (Icc a b ×ˢ Icc u v) = μ := by
    dsimp [μ, hyperbolicConformalAreaOnRectangle]
    rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc), inter_self]
  have hηint : Integrable η μ := by
    have h : IntegrableOn η (Icc a b ×ˢ Icc u v) μ :=
      hη.continuous.continuousOn.integrableOn_compact hrect
    simpa only [IntegrableOn, hμrestrict] using h
  have hF : ContinuousOn F (Icc u v) :=
    (Real.continuousOn_log.mono fun _ hy => (hu.trans_le hy.1).ne').neg
  have hFrect : ContinuousOn (fun p : ℝ × ℝ => F p.2) (Icc a b ×ˢ Icc u v) :=
    hF.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hD1 : Continuous D1 := gluingCollarTestSecondDirectionalDerivative_continuous hη (1, 0)
  have hD2 : Continuous D2 := gluingCollarTestSecondDirectionalDerivative_continuous hη (0, 1)
  have hi1 : IntegrableOn (fun p : ℝ × ℝ => F p.2 * D1 p) (Icc a b ×ˢ Icc u v) :=
    (hFrect.mul hD1.continuousOn).integrableOn_compact hrect
  have hi2 : IntegrableOn (fun p : ℝ × ℝ => F p.2 * D2 p) (Icc a b ×ˢ Icc u v) :=
    (hFrect.mul hD2.continuousOn).integrableOn_compact hrect
  have hiA : IntegrableOn A (Icc a b ×ˢ Icc u v) :=
    ((hyperbolicConformalDensity_continuousOn hu).mul hη.continuous.continuousOn)
      |>.integrableOn_compact hrect
  have hi1prod : Integrable (fun p : ℝ × ℝ => F p.2 * D1 p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc u v))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] using hi1
  have hi2prod : Integrable (fun p : ℝ × ℝ => F p.2 * D2 p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc u v))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] using hi2
  have hiAprod : Integrable A
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc u v))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] using hiA
  have hxzero : (∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v, F p.2 * D1 p) = 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hi1prod]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy'
    rw [integral_const_mul]
    have hslice : ContDiff ℝ 2 (fun x => η (x, y)) :=
      hη.comp (contDiff_id.prodMk contDiff_const)
    have hslice' : ContDiff ℝ 1 (deriv (fun x => η (x, y))) := hslice.deriv'
    have hslice'' : Continuous (deriv (deriv (fun x => η (x, y)))) :=
      hslice'.continuous_deriv_one
    have hleft : deriv (fun x => η (x, y)) a = 0 := by
      rw [gluingCollarTestDirectionalDerivative_radial (hη.differentiable (by norm_num))]
      exact (hx y hy').1
    have hright : deriv (fun x => η (x, y)) b = 0 := by
      rw [gluingCollarTestDirectionalDerivative_radial (hη.differentiable (by norm_num))]
      exact (hx y hy').2
    have hzero : (∫ x in Icc a b, D1 (x, y)) = 0 := by
      simp_rw [show ∀ x, D1 (x, y) = deriv (deriv (fun t => η (t, y))) x from
        fun x => (gluingCollarTestSecondDirectionalDerivative_radial hη x y).symm]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hslice'.continuous.continuousOn
          (fun x _ => (hslice.differentiable_deriv_two x).hasDerivAt)
          (hslice''.intervalIntegrable a b), hright, hleft, sub_self]
    rw [hzero, mul_zero]
    rfl
  have hypair : (∫ p, η p ∂μ) = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v, F p.2 * D2 p := by
    rw [hyperbolicConformalAreaOnRectangle_integral hu, Measure.volume_eq_prod,
      ← Measure.prod_restrict, integral_prod _ hiAprod, integral_prod _ hi2prod]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx'
    have hslice : ContDiff ℝ 2 (fun y => η (x, y)) :=
      hη.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨hleft, hright, hdleft, hdright⟩ := hy x hx'
    have hdleft' : deriv (fun y => η (x, y)) u = 0 := by
      rw [gluingCollarTestDirectionalDerivative_angular (hη.differentiable (by norm_num))]
      exact hdleft
    have hdright' : deriv (fun y => η (x, y)) v = 0 := by
      rw [gluingCollarTestDirectionalDerivative_angular (hη.differentiable (by norm_num))]
      exact hdright
    have hp := hyperbolicConformalLogFactor_weak_second_derivative_Icc
      hu huv hslice hleft hright hdleft' hdright'
    simp_rw [intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc] at hp
    simp_rw [gluingCollarTestSecondDirectionalDerivative_angular hη] at hp
    exact hp.symm
  have hlap : (fun p : ℝ × ℝ => hyperbolicConformalLogFactor p * gluingCollarTestLaplacian η p) =
      (fun p => F p.2 * D1 p + F p.2 * D2 p) := by
    funext p
    exact mul_add _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hyperbolicConformalCurvatureOnRectangle_totalVariation]
    exact hηint
  · rw [hlap]
    exact hi1.add hi2
  · rw [hyperbolicConformalCurvatureOnRectangle, VectorMeasure.integral_neg_vectorMeasure,
      VectorMeasure.integral_toSignedMeasure]
    change -(∫ p, η p ∂μ) = -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
      hyperbolicConformalLogFactor p * gluingCollarTestLaplacian η p)
    rw [hypair, hlap, integral_add hi1 hi2, hxzero, zero_add]

/-- Compactly contained arbitrary `C²` tests discharge every boundary
term. The pairing is with negative original upper-half-plane area. -/
theorem hyperbolicConformalCurvatureOnRectangle_weak_laplacian_of_tsupport_subset
    {a b u v : ℝ} (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v)
    {η : (ℝ × ℝ) → ℝ} (hη : ContDiff ℝ 2 η)
    (hsupport : tsupport η ⊆ Ioo a b ×ˢ Ioo u v) :
    Integrable η (hyperbolicConformalCurvatureOnRectangle a b hu v).totalVariation ∧
    IntegrableOn (fun p : ℝ × ℝ =>
      hyperbolicConformalLogFactor p * gluingCollarTestLaplacian η p)
      (Icc a b ×ˢ Icc u v) ∧
    (∫ᵛ p : ℝ × ℝ, η p ∂<•hyperbolicConformalCurvatureOnRectangle a b hu v) =
      -(∫ p : ℝ × ℝ in Icc a b ×ˢ Icc u v,
        hyperbolicConformalLogFactor p * gluingCollarTestLaplacian η p) := by
  apply hyperbolicConformalCurvatureOnRectangle_weak_laplacian hab hu huv hη
  · intro y _
    have hleft : (a, y) ∉ tsupport η := fun h => (lt_irrefl a) (hsupport h).1.1
    have hright : (b, y) ∉ tsupport η := fun h => (lt_irrefl b) (hsupport h).1.2
    constructor
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hleft]
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hright]
  · intro x _
    have hleft : (x, u) ∉ tsupport η := fun h => (lt_irrefl u) (hsupport h).2.1
    have hright : (x, v) ∉ tsupport η := fun h => (lt_irrefl v) (hsupport h).2.2
    refine ⟨image_eq_zero_of_notMem_tsupport hleft, image_eq_zero_of_notMem_tsupport hright,
      ?_, ?_⟩
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hleft]
    · simp [gluingCollarTestDirectionalDerivative, fderiv_of_notMem_tsupport ℝ hright]

#print axioms hyperbolicConformalAreaMeasure_apply
#print axioms hyperbolicConformalLogFactor_laplacian
#print axioms hyperbolicConformalAreaOnRectangle_eq_withDensity
#print axioms hyperbolicConformalAreaOnRectangle_isFinite
#print axioms hyperbolicConformalCurvatureOnRectangle_totalVariation
#print axioms hyperbolicConformalCurvatureOnRectangle_integral_eq_hyperbolicVolume
#print axioms hyperbolicConformalCurvatureOnRectangle_weak_laplacian_of_tsupport_subset

end
end SystolicGrowth
