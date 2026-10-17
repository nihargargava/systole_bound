module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinRetraction
public import Geometry.GluingGeodesics
public import Geometry.GluingFinFermiCoordinates
public import Geometry.GluingFinFermiInverse
public import Geometry.GluingFinFermiSymmetry
public import Geometry.HyperbolicCurveLength
public import Geometry.HyperbolicMetricSegments
public import Geometry.HyperbolicMidpointComparison
public import Geometry.LipschitzCoordinateCalculus
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.MetricSpace.Gluing

@[expose] public section

/-!
# Actual augmented fin-chain distance

Local costs permit all ordinary-Lipschitz Fermi curves in the radial window,
including excursions into a fin. Finite walks use the quotient that identifies
entire adjacent fins. Every genuine strip walk gives an upper bound for this
augmented distance. Clipping ambient curves back to strips supplies the
reverse bound, with distortion tending to one as the fin width tends to zero.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SystolicGrowth

/-- Along any differentiable Fermi-coordinate curve, the ambient Poincare
speed is the exact scaled finite-strip speed. This identifies the integrand
used by the augmented fin-chain cost with hyperbolic length. -/
theorem gluingCollarFiniteFermiCurve_speed_eq
    (lam : ℝ) {β : ℝ → ℂ} {t : ℝ} (hβ : DifferentiableAt ℝ β t) :
    ‖deriv (fun s => gluingFinFermiLift lam ((β s).re, (β s).im)) t‖ /
        (gluingFinFermiPoint lam (β t).re (β t).im).im =
      |lam| * gluingCollarFiniteStripSpeed lam β t := by
  have hre : HasDerivAt (fun s => (β s).re) (deriv β t).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hβ.hasDerivAt
  have him : HasDerivAt (fun s => (β s).im) (deriv β t).im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hβ.hasDerivAt
  have hp : HasDerivAt (fun s => ((β s).re, (β s).im))
      ((deriv β t).re, (deriv β t).im) t := hre.prodMk him
  have hF := (gluingFinFermiLift_hasFDerivAt lam ((β t).re, (β t).im)).comp_hasDerivAt t hp
  have hreal : deriv (fun s => (β s).re) t = (deriv β t).re := hre.deriv
  have himag : deriv (fun s => (β s).im) t = (deriv β t).im := him.deriv
  change ‖deriv (gluingFinFermiLift lam ∘
    (fun s => ((β s).re, (β s).im))) t‖ / _ = _
  rw [hF.deriv,
    ← (gluingFinFermiLift_hasFDerivAt lam ((β t).re, (β t).im)).fderiv,
    gluingFinFermiLift_fderiv_speed]
  have hspeed : gluingCollarFiniteStripSpeed lam β t =
      Real.sqrt (Real.cosh (lam * (β t).im) ^ 2 * (deriv β t).re ^ 2 +
        (deriv β t).im ^ 2) := by
    simp only [gluingCollarFiniteStripSpeed, Complex.norm_def, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, one_mul, hreal, himag]
    congr 1
    ring
  simp only [hspeed]

/-- The exact Fermi speed identity holds almost everywhere for every
Lipschitz path used in the ambient fin-distance infimum. -/
theorem gluingCollarFiniteFermiCurve_speed_eq_ae
    (lam : ℝ) {a b : ℝ} {K : ℝ≥0} {β : ℝ → ℂ}
    (hab : a ≤ b) (hβ : LipschitzOnWith K β (Icc a b)) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖deriv (fun s => gluingFinFermiLift lam ((β s).re, (β s).im)) t‖ /
          (gluingFinFermiPoint lam (β t).re (β t).im).im =
        |lam| * gluingCollarFiniteStripSpeed lam β t := by
  filter_upwards [lipschitzComplex_differentiableAt_ae hab hβ] with t ht
  exact gluingCollarFiniteFermiCurve_speed_eq lam ht

/-- The ambient Fermi path cost and the Poincare length of its image differ
by exactly the curvature scale, for every Lipschitz path competitor. -/
theorem gluingCollarFiniteFermiCurve_cost_eq_scaled_poincare
    (lam : ℝ) {a b : ℝ} {K : ℝ≥0} {β : ℝ → ℂ}
    (hab : a ≤ b) (hβ : LipschitzOnWith K β (Icc a b)) :
    ENNReal.ofReal |lam| *
        (∫⁻ t in Icc a b,
          ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)) =
      ∫⁻ t in Icc a b,
        ENNReal.ofReal
          (‖deriv (fun s => gluingFinFermiLift lam ((β s).re, (β s).im)) t‖ /
            (gluingFinFermiPoint lam (β t).re (β t).im).im) := by
  calc
    _ = ∫⁻ t in Icc a b,
        ENNReal.ofReal (|lam| * gluingCollarFiniteStripSpeed lam β t) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      funext t
      exact (ENNReal.ofReal_mul (abs_nonneg lam)).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [gluingCollarFiniteFermiCurve_speed_eq_ae lam hab hβ]
        with t ht
      rw [ht]

/-- Every ordinary-Lipschitz competitor in the unit parameter interval has
an ordinary-Lipschitz image under the finite-curvature Fermi map. The bounds
may depend on the competitor: its coordinate image lies in a compact
rectangle, on which the smooth Fermi map is Lipschitz. -/
theorem gluingCollarFiniteFermiCurve_image_lipschitz
    (lam : ℝ) {K : ℝ≥0} {β : ℝ → ℂ}
    (hβ : LipschitzOnWith K β (Icc (0 : ℝ) 1)) :
    ∃ K' : ℝ≥0, LipschitzOnWith K'
      (fun t => gluingFinFermiLift lam ((β t).re, (β t).im))
      (Icc (0 : ℝ) 1) := by
  obtain ⟨Kr, Ki, hRe, hIm⟩ :=
    (lipschitzCoordinate_iff_re_im (α := β) (a := 0) (b := 1)).mp ⟨K, hβ⟩
  let γ : ℝ → ℝ × ℝ := fun t => ((β t).re, (β t).im)
  have hγ : LipschitzOnWith (max Kr Ki) γ (Icc (0 : ℝ) 1) := by
    simpa only [γ] using hRe.prodMk hIm
  let X : ℝ := |(β 0).re| + (Kr : ℝ) + 1
  let Y : ℝ := |(β 0).im| + (Ki : ℝ) + 1
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hReBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |(β t).re| ≤ X := by
    have hdiff := hRe.dist_le_mul t ht 0 (by simp)
    have hdiff' : |(β t).re - (β 0).re| ≤ (Kr : ℝ) * |t| := by
      simpa only [Real.dist_eq, abs_zero, sub_zero] using hdiff
    have hcoord : |(β t).re| ≤ |(β t).re - (β 0).re| + |(β 0).re| := by
      calc
        |(β t).re| = |((β t).re - (β 0).re) + (β 0).re| := by congr 1; ring
        _ ≤ |(β t).re - (β 0).re| + |(β 0).re| := abs_add_le _ _
    dsimp [X]
    calc
      |(β t).re| ≤ (Kr : ℝ) * |t| + |(β 0).re| := by linarith [hcoord, hdiff']
      _ ≤ (Kr : ℝ) + |(β 0).re| := by
        nlinarith [mul_le_mul_of_nonneg_left (htime t ht) (NNReal.coe_nonneg Kr)]
      _ ≤ |(β 0).re| + (Kr : ℝ) + 1 := by linarith
  have hImBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |(β t).im| ≤ Y := by
    have hdiff := hIm.dist_le_mul t ht 0 (by simp)
    have hdiff' : |(β t).im - (β 0).im| ≤ (Ki : ℝ) * |t| := by
      simpa only [Real.dist_eq, abs_zero, sub_zero] using hdiff
    have hcoord : |(β t).im| ≤ |(β t).im - (β 0).im| + |(β 0).im| := by
      calc
        |(β t).im| = |((β t).im - (β 0).im) + (β 0).im| := by congr 1; ring
        _ ≤ |(β t).im - (β 0).im| + |(β 0).im| := abs_add_le _ _
    dsimp [Y]
    calc
      |(β t).im| ≤ (Ki : ℝ) * |t| + |(β 0).im| := by linarith [hcoord, hdiff']
      _ ≤ (Ki : ℝ) + |(β 0).im| := by
        nlinarith [mul_le_mul_of_nonneg_left (htime t ht) (NNReal.coe_nonneg Ki)]
      _ ≤ |(β 0).im| + (Ki : ℝ) + 1 := by linarith
  let box : Set (ℝ × ℝ) := Icc (-X) X ×ˢ Icc (-Y) Y
  have hγbox : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ box := by
    intro t ht
    have hx := abs_le.mp (hReBound t ht)
    have hy := abs_le.mp (hImBound t ht)
    exact ⟨hx, hy⟩
  have hF : ContDiff ℝ 1 (gluingFinFermiLift lam) := by
    have harg : ContDiff ℝ 1 (fun p : ℝ × ℝ => lam * p.2) := by fun_prop
    have hsinh : ContDiff ℝ 1 (fun p : ℝ × ℝ => Real.sinh (lam * p.2)) :=
      Real.contDiff_sinh.comp harg
    have hcosh : ContDiff ℝ 1 (fun p : ℝ × ℝ => Real.cosh (lam * p.2)) :=
      Real.contDiff_cosh.comp harg
    have hcoshNe : ∀ p : ℝ × ℝ, Real.cosh (lam * p.2) ≠ 0 :=
      fun p => (Real.cosh_pos (lam * p.2)).ne'
    have htanh : ContDiff ℝ 1 (fun p : ℝ × ℝ => Real.tanh (lam * p.2)) := by
      have hEq : (fun p : ℝ × ℝ => Real.tanh (lam * p.2)) =
          (fun p => Real.sinh (lam * p.2) / Real.cosh (lam * p.2)) := by
        funext p
        exact Real.tanh_eq_sinh_div_cosh (lam * p.2)
      rw [hEq]
      exact hsinh.div hcosh hcoshNe
    have hexp : ContDiff ℝ 1 (fun p : ℝ × ℝ => Real.exp (lam * p.1)) := by
      fun_prop
    have hreal : ContDiff ℝ 1
        (fun p : ℝ × ℝ => Real.exp (lam * p.1) * Real.tanh (lam * p.2)) := by
      exact hexp.mul htanh
    have himag : ContDiff ℝ 1
        (fun p : ℝ × ℝ => Real.exp (lam * p.1) / Real.cosh (lam * p.2)) := by
      exact hexp.div hcosh hcoshNe
    change ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      Complex.ofReal (Real.exp (lam * p.1) * Real.tanh (lam * p.2)) +
        Complex.ofReal (Real.exp (lam * p.1) / Real.cosh (lam * p.2)) * Complex.I)
    exact (Complex.ofRealCLM.contDiff.comp hreal).add
      ((Complex.ofRealCLM.contDiff.comp himag).mul contDiff_const)
  have hFbox : ContDiffOn ℝ 1 (gluingFinFermiLift lam) box :=
    hF.contDiffOn.mono (Set.subset_univ _)
  have hboxConvex : Convex ℝ box := by
    dsimp [box]
    exact (convex_Icc (-X) X).prod (convex_Icc (-Y) Y)
  have hboxCompact : IsCompact box := by
    dsimp [box]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨Kbox, hKbox⟩ := hFbox.exists_lipschitzOnWith one_ne_zero
    hboxConvex hboxCompact
  refine ⟨Kbox * max Kr Ki, ?_⟩
  simpa only [Function.comp_def, γ] using hKbox.comp hγ hγbox

/-- The inverse Fermi coordinates of a positive-height smooth curve, viewed
as one complex-valued path. -/
noncomputable def gluingFinFermiCoordPath (lam : ℝ) (α : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.ofReal (Real.log ‖α t‖ / lam) +
    Complex.ofReal (Real.arsinh ((α t).re / (α t).im) / lam) * Complex.I

/-- The inverse Fermi-coordinate path is smooth whenever the input path stays
in the upper half-plane and the scale is nonzero. -/
theorem gluingFinFermiCoordPath_contDiff
    (lam : ℝ) {α : ℝ → ℂ}
    (hα : ContDiff ℝ 1 α) (hpos : ∀ t, 0 < (α t).im) :
    ContDiff ℝ 1 (gluingFinFermiCoordPath lam α) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hαt : ContDiffAt ℝ 1 α t := hα.contDiffAt
  have hαne : α t ≠ 0 := by
    intro h
    have hp := hpos t
    rw [h] at hp
    exact (lt_irrefl 0 hp)
  have hnorm : ContDiffAt ℝ 1 (fun s => ‖α s‖) t :=
    hαt.norm ℝ hαne
  have hlog : ContDiffAt ℝ 1 (fun s => Real.log ‖α s‖) t :=
    hnorm.log (norm_pos_iff.mpr hαne).ne'
  have hre : ContDiffAt ℝ 1 (fun s => (α s).re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t hαt
  have him : ContDiffAt ℝ 1 (fun s => (α s).im) t :=
    Complex.imCLM.contDiff.contDiffAt.comp t hαt
  have hratio : ContDiffAt ℝ 1 (fun s => (α s).re / (α s).im) t :=
    hre.div him (hpos t).ne'
  have harsinh : ContDiffAt ℝ 1
      (fun s => Real.arsinh ((α s).re / (α s).im)) t :=
    Real.contDiff_arsinh.contDiffAt.comp t hratio
  have hradial : ContDiffAt ℝ 1
      (fun s => Real.log ‖α s‖ / lam) t := hlog.div_const lam
  have htransverse : ContDiffAt ℝ 1
      (fun s => Real.arsinh ((α s).re / (α s).im) / lam) t :=
    harsinh.div_const lam
  change ContDiffAt ℝ 1 (fun s =>
    Complex.ofReal (Real.log ‖α s‖ / lam) +
      Complex.ofReal (Real.arsinh ((α s).re / (α s).im) / lam) * Complex.I) t
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp t hradial).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp t htransverse).mul
      contDiffAt_const)

/-- A smooth positive-height path has Lipschitz inverse Fermi coordinates on
the compact unit interval. -/
theorem exists_gluingFinFermiCoordPath_lipschitz
    (lam : ℝ) {α : ℝ → ℂ} (hα : ContDiff ℝ 1 α)
    (hpos : ∀ t, 0 < (α t).im) :
    ∃ K : ℝ≥0, LipschitzOnWith K (gluingFinFermiCoordPath lam α)
      (Icc (0 : ℝ) 1) := by
  have hcoords := gluingFinFermiCoordPath_contDiff lam hα hpos
  obtain ⟨K, hK⟩ := hcoords.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (0 : ℝ) 1) isCompact_Icc
  exact ⟨K, hK⟩

/-- The finite-curvature Fermi map exactly reconstructs a positive-height
path from its inverse-coordinate path. -/
theorem gluingFinFermiCoordPath_reconstruct
    {lam : ℝ} (hlam : 0 < lam) {α : ℝ → ℂ}
    (hpos : ∀ t, 0 < (α t).im) (t : ℝ) :
    gluingFinFermiLift lam
        ((gluingFinFermiCoordPath lam α t).re,
          (gluingFinFermiCoordPath lam α t).im) = α t := by
  let z : UpperHalfPlane := UpperHalfPlane.ofComplex (α t)
  have hrad : (gluingFinFermiCoordPath lam α t).re =
      gluingFinFermiRadialCoord lam z := by
    simp [gluingFinFermiCoordPath, gluingFinFermiRadialCoord, z,
      UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t)]
  have htrans : (gluingFinFermiCoordPath lam α t).im =
      gluingFinFermiTransverseCoord lam z := by
    simp [gluingFinFermiCoordPath, gluingFinFermiTransverseCoord, z,
      UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t)]
  have hinv := congrArg (fun q : UpperHalfPlane => (q : ℂ))
    (gluingFinFermiPoint_inverse_right hlam z)
  change gluingFinFermiLift lam
      (gluingFinFermiRadialCoord lam z, gluingFinFermiTransverseCoord lam z) =
        (z : ℂ) at hinv
  rw [← hrad, ← htrans] at hinv
  simpa [z, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t)] using hinv

/-- Every Lipschitz Fermi competitor pays at least the hyperbolic distance
between its endpoints, scaled by the curvature parameter. This is the lower
half of identifying the finite ambient slab cost with hyperbolic distance. -/
theorem gluingCollarFiniteFermiCurve_endpoint_dist_le_cost
    (lam : ℝ) {K : ℝ≥0} {β : ℝ → ℂ}
    (hβ : LipschitzOnWith K β (Icc (0 : ℝ) 1)) :
    ENNReal.ofReal (dist (gluingFinFermiPoint lam (β 0).re (β 0).im)
      (gluingFinFermiPoint lam (β 1).re (β 1).im)) ≤
      ENNReal.ofReal |lam| *
        (∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)) := by
  obtain ⟨K', hK'⟩ := gluingCollarFiniteFermiCurve_image_lipschitz lam hβ
  let α : ℝ → ℂ := fun t => gluingFinFermiLift lam ((β t).re, (β t).im)
  have hpos (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : 0 < (α t).im := by
    change 0 < (gluingFinFermiLift lam ((β t).re, (β t).im)).im
    rw [gluingFinFermiLift_im]
    exact div_pos (Real.exp_pos _) (Real.cosh_pos _)
  have hdist := hyperbolic_dist_le_poincare_lintegral_of_lipschitz
    (a := 0) (b := 1) (K := K') (by norm_num) hK' hpos
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      UpperHalfPlane.mk (α t) (hpos t ht) =
      gluingFinFermiPoint lam (β t).re (β t).im := by
    rfl
  rw [hpoint 0 (by norm_num), hpoint 1 (by norm_num)] at hdist
  have hcost : ENNReal.ofReal |lam| *
      (∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖deriv α t‖ / (α t).im) := by
    simpa only [α, gluingFinFermiPoint_im, gluingFinFermiLift_im] using
      gluingCollarFiniteFermiCurve_cost_eq_scaled_poincare lam
      (a := 0) (b := 1) (K := K) (β := β) (by norm_num) hβ
  rw [← hcost] at hdist
  exact hdist

/-- The hyperbolic geodesic between two points whose Fermi radial coordinates
lie in a closed interval stays in that same radial window. This makes the
geodesic available as a competitor for the window-restricted finite Fermi
distance. -/
theorem gluingFinFermiRadialCoord_geodInterp_mem_Icc
    {lam R : ℝ} (hlam : 0 < lam) {z w : UpperHalfPlane}
    (hz : gluingFinFermiRadialCoord lam z ∈ Icc (-R) R)
    (hw : gluingFinFermiRadialCoord lam w ∈ Icc (-R) R)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    gluingFinFermiRadialCoord lam
        (Vendored.RiemannDynamics.geodInterp z w s) ∈ Icc (-R) R := by
  let u : ℝ → ℝ := fun t => gluingFinFermiRadialCoord lam
    (Vendored.RiemannDynamics.geodInterp z w t)
  have hu0 : u 0 = gluingFinFermiRadialCoord lam z := by
    simp [u, Vendored.RiemannDynamics.geodInterp_zero]
  have hu1 : u 1 = gluingFinFermiRadialCoord lam w := by
    simp [u, Vendored.RiemannDynamics.geodInterp_one]
  rcases gluingFinFermiRadialCoord_geodInterp_mono_or_anti hlam z w with
    hmono | hanti
  · constructor
    · calc
        -R ≤ gluingFinFermiRadialCoord lam z := hz.1
        _ = u 0 := hu0.symm
        _ ≤ u s := hmono hs.1
    · calc
        u s ≤ u 1 := hmono hs.2
        _ = gluingFinFermiRadialCoord lam w := hu1
        _ ≤ R := hw.2
  · constructor
    · calc
        -R ≤ gluingFinFermiRadialCoord lam w := hw.1
        _ = u 1 := hu1.symm
        _ ≤ u s := hanti hs.2
    · calc
        u s ≤ u 0 := hanti hs.1
        _ = gluingFinFermiRadialCoord lam z := hu0
        _ ≤ R := hz.2

/-- The closed radial slab is geodesically convex in the hyperbolic plane.
This is the geometric domain corresponding to the window-restricted finite
Fermi distance. -/
def gluingFinFermiRadialWindow (lam R : ℝ) : Set UpperHalfPlane :=
  {z | gluingFinFermiRadialCoord lam z ∈ Icc (-R) R}

/-- The radial slab is closed in the complete hyperbolic plane. -/
theorem gluingFinFermiRadialWindow_isClosed (lam R : ℝ) :
    IsClosed (gluingFinFermiRadialWindow lam R) :=
  isClosed_Icc.preimage (continuous_gluingFinFermiRadialCoord lam)

/-- The radial slab, with its induced hyperbolic metric, is complete. -/
theorem gluingFinFermiRadialWindow_completeSpace (lam R : ℝ) :
    CompleteSpace (gluingFinFermiRadialWindow lam R) :=
  (gluingFinFermiRadialWindow_isClosed lam R).completeSpace_coe

theorem gluingFinFermiRadialWindow_geodSeg_subset
    {lam R : ℝ} (hlam : 0 < lam) {z w : UpperHalfPlane}
    (hz : z ∈ gluingFinFermiRadialWindow lam R)
    (hw : w ∈ gluingFinFermiRadialWindow lam R) :
    Vendored.RiemannDynamics.geodSeg z w ⊆ gluingFinFermiRadialWindow lam R := by
  change gluingFinFermiRadialCoord lam z ∈ Icc (-R) R at hz
  change gluingFinFermiRadialCoord lam w ∈ Icc (-R) R at hw
  intro q hq
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hq
  rcases hq with ⟨t, ht, hqt⟩
  change gluingFinFermiRadialCoord lam q ∈ Icc (-R) R
  rw [← hqt]
  exact gluingFinFermiRadialCoord_geodInterp_mem_Icc hlam hz hw ht

/-- The actual upper fin in one finite-curvature Fermi slab, restricted to
the radial window used by the finite model. -/
def gluingCollarFiniteUpperFin (r R lam ε : ℝ) : Set UpperHalfPlane :=
  {z | gluingFinFermiRadialCoord lam z ∈ Icc (-R) R ∧
    ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam z) ≤
      gluingFinFermiTransverseCoord lam z}

/-- The actual lower fin in one finite-curvature Fermi slab, restricted to
the same radial window. -/
def gluingCollarFiniteLowerFin (r R lam ε : ℝ) : Set UpperHalfPlane :=
  {z | gluingFinFermiRadialCoord lam z ∈ Icc (-R) R ∧
    gluingFinFermiTransverseCoord lam z ≤
      -ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam z)}

/-- Reflection identifies the actual upper and lower finite gluing loci. -/
def gluingCollarFiniteUpperLowerEquiv (r R lam ε : ℝ) :
    gluingCollarFiniteUpperFin r R lam ε ≃ gluingCollarFiniteLowerFin r R lam ε where
  toFun z := ⟨gluingMirror z.1, by
    change gluingFinFermiRadialCoord lam (gluingMirror z.1) ∈ Icc (-R) R ∧
      gluingFinFermiTransverseCoord lam (gluingMirror z.1) ≤
        -ε * gluingCollarWarp r
          (gluingFinFermiRadialCoord lam (gluingMirror z.1))
    rw [gluingFinFermiRadialCoord_mirror, gluingFinFermiTransverseCoord_mirror]
    exact ⟨z.2.1, by linarith [z.2.2]⟩⟩
  invFun z := ⟨gluingMirror z.1, by
    change gluingFinFermiRadialCoord lam (gluingMirror z.1) ∈ Icc (-R) R ∧
      ε * gluingCollarWarp r
          (gluingFinFermiRadialCoord lam (gluingMirror z.1)) ≤
        gluingFinFermiTransverseCoord lam (gluingMirror z.1)
    rw [gluingFinFermiRadialCoord_mirror, gluingFinFermiTransverseCoord_mirror]
    exact ⟨z.2.1, by linarith [z.2.2]⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact gluingMirror_involutive z.1
  right_inv z := by
    apply Subtype.ext
    exact gluingMirror_involutive z.1

/-- The actual fin identification is an isometry for the induced hyperbolic
metrics on both closed loci. -/
theorem gluingCollarFiniteUpperLowerEquiv_isometry (r R lam ε : ℝ) :
    Isometry (gluingCollarFiniteUpperLowerEquiv r R lam ε) :=
  Isometry.of_dist_eq fun a b => by
    change dist (gluingMirror a.1) (gluingMirror b.1) = dist a.1 b.1
    exact gluingMirror_isometry.dist_eq a.1 b.1

/-- The canonical map of the upper fin into its radial slab copy. -/
def gluingCollarFiniteMetricGlueLeft (r R lam ε : ℝ) :
    gluingCollarFiniteUpperFin r R lam ε → gluingFinFermiRadialWindow lam R :=
  fun z => ⟨z.1, z.2.1⟩

/-- The canonical map of the reflected upper fin into the second radial slab
copy; its image is the actual lower gluing locus. -/
def gluingCollarFiniteMetricGlueRight (r R lam ε : ℝ) :
    gluingCollarFiniteUpperFin r R lam ε → gluingFinFermiRadialWindow lam R :=
  fun z => ⟨gluingMirror z.1, by
    change gluingFinFermiRadialCoord lam (gluingMirror z.1) ∈ Icc (-R) R
    rw [gluingFinFermiRadialCoord_mirror]
    exact z.2.1⟩

theorem gluingCollarFiniteMetricGlueLeft_isometry (r R lam ε : ℝ) :
    Isometry (gluingCollarFiniteMetricGlueLeft r R lam ε) :=
  Isometry.of_dist_eq fun _ _ => rfl

theorem gluingCollarFiniteMetricGlueRight_isometry (r R lam ε : ℝ) :
    Isometry (gluingCollarFiniteMetricGlueRight r R lam ε) :=
  Isometry.of_dist_eq fun a b => by
    change dist (gluingMirror a.1) (gluingMirror b.1) = dist a.1 b.1
    exact gluingMirror_isometry.dist_eq a.1 b.1

/-- The common fin is nonempty whenever the radial window is nonempty and
the Fermi scale is positive. A point at radial coordinate zero and sufficiently
large positive transverse coordinate lies in the actual upper fin. -/
theorem gluingCollarFiniteUpperFin_nonempty {r R lam ε : ℝ}
    (hR : 0 ≤ R) (hlam : 0 < lam) :
    Nonempty (gluingCollarFiniteUpperFin r R lam ε) := by
  refine ⟨⟨gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0 + 1), ?_⟩⟩
  change gluingFinFermiRadialCoord lam
      (gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0 + 1)) ∈ Icc (-R) R ∧
    ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam
      (gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0 + 1))) ≤
      gluingFinFermiTransverseCoord lam
        (gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0 + 1))
  rw [gluingFinFermiRadialCoord_point hlam, gluingFinFermiTransverseCoord_point hlam]
  constructor
  · constructor <;> linarith
  · exact le_add_of_nonneg_right (by norm_num)

/-- Mathlib's exact metric quotient for two copies of the radial slab glued
along the actual upper fin and its reflected lower fin. -/
abbrev gluingCollarFiniteMetricGlueSpace (r R lam ε : ℝ)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)] :=
  Metric.GlueSpace (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)

/-- The hyperbolic distance between reflected cross-copy endpoints is bounded
by every route through the common fin. -/
private theorem gluingCollarFiniteMetricGlue_reflectedCross_dist_le {r R lam ε : ℝ}
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    dist x.1 (gluingMirror y.1) ≤
      ⨅ z : gluingCollarFiniteUpperFin r R lam ε,
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε z) := by
  apply le_ciInf
  intro z
  have hmirror : dist z.1 (gluingMirror y.1) =
      dist y.1 (gluingMirror z.1) := by
    calc
      dist z.1 (gluingMirror y.1) =
          dist (gluingMirror z.1) (gluingMirror (gluingMirror y.1)) :=
        (gluingMirror_isometry.dist_eq z.1 (gluingMirror y.1)).symm
      _ = dist (gluingMirror z.1) y.1 := by rw [gluingMirror_involutive]
      _ = dist y.1 (gluingMirror z.1) := dist_comm _ _
  change dist x.1 (gluingMirror y.1) ≤
    dist x.1 z.1 + dist y.1 (gluingMirror z.1)
  calc
    dist x.1 (gluingMirror y.1) ≤
        dist x.1 z.1 + dist z.1 (gluingMirror y.1) := dist_triangle _ _ _
    _ = dist x.1 z.1 + dist y.1 (gluingMirror z.1) := by rw [hmirror]

/-- The actual reflected fin points are identified in the metric gluing. -/
theorem gluingCollarFiniteMetricGlue_commute (r R lam ε : ℝ)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)] :
    Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
        (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) ∘
      gluingCollarFiniteMetricGlueLeft r R lam ε =
    Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
        (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) ∘
      gluingCollarFiniteMetricGlueRight r R lam ε :=
  Metric.toGlue_commute _ _

/-- Each full radial-slab copy embeds isometrically in Mathlib's exact glued
metric space. -/
theorem gluingCollarFiniteMetricGlueLeft_toGlue_isometry (r R lam ε : ℝ)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)] :
    Isometry (Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)) :=
  Metric.toGlueL_isometry _ _

theorem gluingCollarFiniteMetricGlueRight_toGlue_isometry (r R lam ε : ℝ)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)] :
    Isometry (Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)) :=
  Metric.toGlueR_isometry _ _

/-- The two-piece metric gluing is complete when each radial slab is
complete. Its two canonical isometric images are complete and cover the
quotient, so their union is complete. -/
theorem gluingCollarFiniteMetricGlueSpace_completeSpace (r R lam ε : ℝ)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)] :
    CompleteSpace (gluingCollarFiniteMetricGlueSpace r R lam ε) := by
  letI : CompleteSpace (gluingFinFermiRadialWindow lam R) :=
    gluingFinFermiRadialWindow_completeSpace lam R
  let left := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let right := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hcover : Set.range left ∪ Set.range right = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    cases p with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr y => exact Or.inr ⟨y, rfl⟩
  have hleft : IsComplete (Set.range left) :=
    (gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε).isUniformInducing
      |>.isComplete_range
  have hright : IsComplete (Set.range right) :=
    (gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε).isUniformInducing
      |>.isComplete_range
  rw [completeSpace_iff_isComplete_univ, ← hcover]
  exact hleft.union hright

/-- On a proper metric space, a continuous function bounded below by distance
from a fixed point attains its infimum on every nonempty closed set. The
sublevel at one chosen point is compact because it lies in a closed ball. -/
theorem exists_isMinOn_closed_of_distance_lower_bound {s : Set UpperHalfPlane}
    (hs : IsClosed s) (hne : s.Nonempty) (x : UpperHalfPlane)
    (f : UpperHalfPlane → ℝ) (hf : Continuous f)
    (hbound : ∀ z, dist x z ≤ f z) :
    ∃ z ∈ s, ∀ w ∈ s, f z ≤ f w := by
  obtain ⟨z₀, hz₀⟩ := hne
  let K : Set UpperHalfPlane := s ∩ f ⁻¹' Set.Iic (f z₀)
  have hKclosed : IsClosed K := hs.inter (isClosed_Iic.preimage hf)
  have hKsub : K ⊆ Metric.closedBall x (f z₀) := by
    rintro z ⟨_, hz⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact (hbound z).trans hz
  have hKcompact : IsCompact K :=
    (isCompact_closedBall x (f z₀)).of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨z₀, hz₀, by simp⟩
  obtain ⟨z, hz, hmin⟩ := hKcompact.exists_isMinOn hKne hf.continuousOn
  refine ⟨z, hz.1, ?_⟩
  intro w hw
  by_cases hwK : w ∈ K
  · exact hmin hwK
  · have hwlarge : f z₀ < f w := by
      by_contra h
      have hwle : f w ≤ f z₀ := le_of_not_gt h
      exact hwK ⟨hw, hwle⟩
    have hz₀K : z₀ ∈ K := ⟨hz₀, by simp⟩
    exact (hmin hz₀K).trans hwlarge.le

/-- In Mathlib's exact metric gluing, the distance across the two copies is
the infimum of the sums of distances through a common fin point. -/
theorem gluingCollarFiniteMetricGlue_cross_dist (r R lam ε : ℝ)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      ⨅ z : gluingCollarFiniteUpperFin r R lam ε,
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε z) := by
  change Metric.glueDist
      (gluingCollarFiniteMetricGlueLeft r R lam ε)
      (gluingCollarFiniteMetricGlueRight r R lam ε) 0 (.inl x) (.inr y) = _
  simp [Metric.glueDist]

/-- Any route through the common fin is at least as long as the hyperbolic
distance between the endpoints after reflecting the right copy. -/
theorem gluingCollarFiniteMetricGlue_unfolded_cross_dist_le
    {r R lam ε : ℝ}
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    dist x.1 (gluingMirror y.1) ≤
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) := by
  rw [gluingCollarFiniteMetricGlue_cross_dist]
  simpa [gluingCollarFiniteMetricGlueLeft,
    gluingCollarFiniteMetricGlueRight, Subtype.dist_eq] using
    gluingCollarFiniteMetricGlue_reflectedCross_dist_le
      (r := r) (R := R) (lam := lam) (ε := ε) x y

/-- If the left endpoint lies on the common fin, its glued distance to any
right-copy point is exactly the unfolded hyperbolic distance. The upper bound
uses the seam identification to travel entirely in the right copy; the lower
bound is the general reflected-distance inequality. This is a boundary case
needed when proving the finite midpoint comparison for seam test points. -/
theorem gluingCollarFiniteMetricGlue_seam_left_cross_dist_eq
    {r R lam ε : ℝ} [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (a : gluingCollarFiniteUpperFin r R lam ε)
    (y : gluingFinFermiRadialWindow lam R) :
    dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueLeft r R lam ε a))
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist a.1 (gluingMirror y.1) := by
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Q := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  have hcomm := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) a
  change L (I a) = Q (J a) at hcomm
  have hcopy : dist (L (I a)) (Q y) = dist (J a) y := by
    rw [hcomm]
    exact hRI.dist_eq (J a) y
  have hunfold : dist a.1 (gluingMirror y.1) ≤ dist (L (I a)) (Q y) := by
    have h := gluingCollarFiniteMetricGlue_unfolded_cross_dist_le
      (r := r) (R := R) (lam := lam) (ε := ε) (I a) y
    change dist a.1 (gluingMirror y.1) ≤ dist (L (I a)) (Q y) at h
    exact h
  have hreflect : dist (J a) y = dist a.1 (gluingMirror y.1) := by
    dsimp [J, gluingCollarFiniteMetricGlueRight]
    calc
      dist (gluingMirror a.1) y.1 =
          dist (gluingMirror a.1) (gluingMirror (gluingMirror y.1)) := by
            rw [gluingMirror_involutive]
      _ = dist a.1 (gluingMirror y.1) := gluingMirror_isometry.dist_eq _ _
  have hupper : dist (L (I a)) (Q y) ≤ dist a.1 (gluingMirror y.1) := by
    rw [hcopy, hreflect]
  exact le_antisymm hupper hunfold

/-- The cross-piece distance in the finite metric gluing is realized by an
actual point of the common fin. Properness makes the cost sublevel compact;
the actual fin is closed and has an explicitly constructed point. -/
theorem gluingCollarFiniteMetricGlue_cross_dist_attained
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    ∃ z : gluingCollarFiniteUpperFin r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε z) := by
  let f : UpperHalfPlane → ℝ := fun z => dist x.1 z + dist y.1 (gluingMirror z)
  have hf : Continuous f := by
    dsimp [f]
    exact (continuous_const.dist continuous_id).add
      (continuous_const.dist gluingMirror_isometry.continuous)
  have hbound (z : UpperHalfPlane) : dist x.1 z ≤ f z := by
    dsimp [f]
    exact le_add_of_nonneg_right dist_nonneg
  have hUclosed : IsClosed (gluingCollarFiniteUpperFin r R lam ε) := by
    change IsClosed {z | gluingFinFermiRadialCoord lam z ∈ Icc (-R) R ∧
      ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam z) ≤
        gluingFinFermiTransverseCoord lam z}
    apply (isClosed_Icc.preimage (continuous_gluingFinFermiRadialCoord lam)).inter
    exact isClosed_le
      (continuous_const.mul
        ((gluingCollarWarp_continuous r).comp
          (continuous_gluingFinFermiRadialCoord lam)))
      (continuous_gluingFinFermiTransverseCoord lam)
  obtain ⟨z₀⟩ := (gluingCollarFiniteUpperFin_nonempty hR hlam)
  have hUne : (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane).Nonempty :=
    ⟨z₀.1, z₀.2⟩
  obtain ⟨z, hz, hmin⟩ := exists_isMinOn_closed_of_distance_lower_bound
    hUclosed hUne x.1 f hf hbound
  let z' : gluingCollarFiniteUpperFin r R lam ε := ⟨z, hz⟩
  have hinf : (⨅ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x.1 w.1 + dist y.1 (gluingMirror w.1)) =
      dist x.1 z + dist y.1 (gluingMirror z) := by
    apply le_antisymm
    · change (⨅ w : gluingCollarFiniteUpperFin r R lam ε,
        dist x.1 w.1 + dist y.1 (gluingMirror w.1)) ≤
          dist x.1 z + dist y.1 (gluingMirror z)
      have hbounded : BddBelow (Set.range (fun w : gluingCollarFiniteUpperFin r R lam ε =>
          dist x.1 w.1 + dist y.1 (gluingMirror w.1))) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩
      exact ciInf_le hbounded z'
    · change dist x.1 z + dist y.1 (gluingMirror z) ≤
        ⨅ w : gluingCollarFiniteUpperFin r R lam ε,
          dist x.1 w.1 + dist y.1 (gluingMirror w.1)
      exact le_ciInf (fun w : gluingCollarFiniteUpperFin r R lam ε => by
        change f z ≤ f w.1
        exact hmin (w := w.1) w.2)
  refine ⟨z', ?_⟩
  rw [gluingCollarFiniteMetricGlue_cross_dist]
  simpa [f, gluingCollarFiniteMetricGlueLeft,
    gluingCollarFiniteMetricGlueRight, Subtype.dist_eq] using hinf

/-- A minimizing common-fin point minimizes the sum of the two hyperbolic
distances along every geodesic in the common fin. Reflection turns the right
copy's distance into an ordinary distance to the reflected endpoint, so the
generic hyperbolic first-variation lemma applies to this objective. -/
theorem gluingCollarFiniteMetricGlue_cross_seam_geodesic_minimum
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R) :
    ∃ q : gluingCollarFiniteUpperFin r R lam ε,
      (∀ w : gluingCollarFiniteUpperFin r R lam ε,
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
            dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
              dist (gluingMirror y.1)
                (Vendored.RiemannDynamics.geodInterp q.1 w.1 t)) ∧
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
  obtain ⟨q, hqattain⟩ := gluingCollarFiniteMetricGlue_cross_dist_attained
    (r := r) (R := R) (lam := lam) (ε := ε) hR hlam x y
  let cost : gluingCollarFiniteUpperFin r R lam ε → ℝ := fun z =>
    dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
      dist y (gluingCollarFiniteMetricGlueRight r R lam ε z)
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hcross := gluingCollarFiniteMetricGlue_cross_dist r R lam ε x y
  have hqinf : (⨅ z : gluingCollarFiniteUpperFin r R lam ε, cost z) = cost q := by
    rw [← hcross]
    simpa only [cost] using hqattain
  have hcostmin : ∀ z : gluingCollarFiniteUpperFin r R lam ε, cost q ≤ cost z := by
    intro z
    rw [← hqinf]
    apply ciInf_le
    refine ⟨0, ?_⟩
    rintro a ⟨z', rfl⟩
    positivity
  have hmirror (z : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror z.1) = dist (gluingMirror y.1) z.1 := by
    calc
      dist y.1 (gluingMirror z.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror z.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror z.1)).symm
      _ = dist (gluingMirror y.1) z.1 := by rw [gluingMirror_involutive]
  have hcostq : cost q = dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
    dsimp [cost, gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight]
    rw [Subtype.dist_eq, Subtype.dist_eq, hmirror q]
  have hdecomp : dist (L x) (Rg y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
    rw [hcross, hqinf, hcostq]
  refine ⟨q, ?_⟩
  constructor
  intro w t ht
  let p := Vendored.RiemannDynamics.geodInterp q.1 w.1 t
  have hpseg : p ∈ Vendored.RiemannDynamics.geodSeg q.1 w.1 :=
    Vendored.RiemannDynamics.geodInterp_mem_geodSeg q.1 w.1 ht
  have hpfin : p ∈ gluingCollarFiniteUpperFin r R lam ε :=
    hconv q.1 q.2 w.1 w.2 hpseg
  let z : gluingCollarFiniteUpperFin r R lam ε := ⟨p, hpfin⟩
  have hmin := hcostmin z
  have hcostz : cost z = dist x.1 p + dist (gluingMirror y.1) p := by
    dsimp [cost, gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight]
    rw [Subtype.dist_eq, Subtype.dist_eq, hmirror z]
  rw [hcostq, hcostz] at hmin
  · exact hmin
  · exact hdecomp

/-- At the actual minimizing seam point, the summed forward first variation
vanishes or points uphill along every nonconstant common-fin geodesic, provided
neither endpoint coincides with that seam point. Coincident-endpoint cases
require the corresponding one-sided distance derivative and are kept explicit. -/
theorem gluingCollarFiniteMetricGlue_cross_seam_first_variation
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R) :
    ∃ q : gluingCollarFiniteUpperFin r R lam ε,
      (∀ w : gluingCollarFiniteUpperFin r R lam ε,
          0 ≤ geodInterpDistanceForwardDerivative q.1 w.1 x.1 +
            geodInterpDistanceForwardDerivative q.1 w.1 (gluingMirror y.1)) ∧
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
  obtain ⟨q, hmin, hdecomp⟩ := gluingCollarFiniteMetricGlue_cross_seam_geodesic_minimum
    (r := r) (R := R) (lam := lam) (ε := ε) hR hlam hconv x y
  refine ⟨q, ?_, hdecomp⟩
  intro w
  apply geodInterp_distance_forward_derivative_sum_nonneg_of_minimizing
    q.1 w.1 x.1 (gluingMirror y.1)
  exact hmin w

/-- A point of the finite upper fin is either an interior point, a radial
window endpoint, or lies on the seam graph.  This explicit trichotomy is the
boundary split needed when extending the seam-minimizer comparison beyond
common-fin test points. -/
theorem gluingCollarFiniteUpperFin_interior_or_boundary
    {r R lam ε : ℝ} (q : gluingCollarFiniteUpperFin r R lam ε) :
    q.1 ∈ interior (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane) ∨
      gluingFinFermiRadialCoord lam q.1 = -R ∨
      gluingFinFermiRadialCoord lam q.1 = R ∨
      ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
        gluingFinFermiTransverseCoord lam q.1 := by
  rcases q.2 with ⟨⟨hlo, hhi⟩, hseam⟩
  by_cases hlo' : -R < gluingFinFermiRadialCoord lam q.1
  · by_cases hhi' : gluingFinFermiRadialCoord lam q.1 < R
    · by_cases hseam' : ε * gluingCollarWarp r
          (gluingFinFermiRadialCoord lam q.1) < gluingFinFermiTransverseCoord lam q.1
      · left
        let U : Set UpperHalfPlane := {z |
          gluingFinFermiRadialCoord lam z ∈ Ioo (-R) R ∧
            ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam z) <
              gluingFinFermiTransverseCoord lam z}
        have hUopen : IsOpen U := by
          dsimp [U]
          exact (isOpen_Ioo.preimage
              (continuous_gluingFinFermiRadialCoord lam)).inter
            (isOpen_lt
              (continuous_const.mul ((gluingCollarWarp_continuous r).comp
                (continuous_gluingFinFermiRadialCoord lam)))
              (continuous_gluingFinFermiTransverseCoord lam))
        have hUsub : U ⊆ gluingCollarFiniteUpperFin r R lam ε := by
          intro z hz
          exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.le⟩
        have hqU : q.1 ∈ U := ⟨⟨hlo', hhi'⟩, hseam'⟩
        exact (interior_maximal hUsub hUopen) hqU
      · right
        right
        right
        exact le_antisymm hseam (le_of_not_gt hseam')
    · right
      right
      left
      exact le_antisymm hhi (le_of_not_gt hhi')
  · right
    left
    exact le_antisymm (le_of_not_gt hlo') hlo

/-- A seam-cost minimizer cannot lie on the upper radial cap if both
cross-pair endpoints lie strictly below that cap. Moving the seam point
slightly inward at fixed transverse coordinate stays in the fin and strictly
shortens both hyperbolic legs. -/
theorem gluingCollarFiniteUpperFin_minimizer_ne_upper_radial_cap
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ≤
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε w))
    (hxR : (gluingFinFermiInverse lam x.1).1 < R)
    (hyR : (gluingFinFermiInverse lam (gluingMirror y.1)).1 < R) :
    gluingFinFermiRadialCoord lam q.1 ≠ R := by
  intro hqcap
  let cq := gluingFinFermiInverse lam q.1
  let cx := gluingFinFermiInverse lam x.1
  let cy := gluingFinFermiInverse lam (gluingMirror y.1)
  have hxraw : gluingFinFermiRadialCoord lam x.1 ∈ Icc (-R) R := x.2
  have hyraw : gluingFinFermiRadialCoord lam y.1 ∈ Icc (-R) R := y.2
  have hxwindow : cx.1 ∈ Icc (-R) R := by
    simpa [cx, gluingFinFermiInverse] using hxraw
  have hywindow : cy.1 ∈ Icc (-R) R := by
    simpa [cy, gluingFinFermiInverse, gluingFinFermiRadialCoord_mirror] using hyraw
  have hs : max cx.1 cy.1 < R := max_lt_iff.mpr ⟨hxR, hyR⟩
  let t : ℝ := (max cx.1 cy.1 + R) / 2
  have hst : max cx.1 cy.1 < t := by dsimp [t]; linarith
  have htR : t < R := by dsimp [t]; linarith
  have htwindow : t ∈ Icc (-R) R := by
    constructor
    · linarith [hxwindow.1, le_max_left cx.1 cy.1]
    · exact htR.le
  have hwarp : gluingCollarWarp r t ≤ gluingCollarWarp r R := by
    rw [gluingCollarWarp, gluingCollarWarp, abs_of_pos hR]
    apply Real.sinh_le_sinh.mpr
    have habs : |t| ≤ R := abs_le.mpr htwindow
    linarith
  rcases q.2 with ⟨⟨hqlo, hqhi⟩, hqfin⟩
  have hqfinR : ε * gluingCollarWarp r R ≤
      gluingFinFermiTransverseCoord lam q.1 := by
    simpa [hqcap] using hqfin
  let qpt := gluingFinFermiPoint lam t cq.2
  have hqptRad := gluingFinFermiRadialCoord_point
    (α := lam) (t := t) (u := cq.2) hlam
  have hqptTrans := gluingFinFermiTransverseCoord_point
    (α := lam) (t := t) (u := cq.2) hlam
  have hqptFin : qpt ∈ gluingCollarFiniteUpperFin r R lam ε := by
    change gluingFinFermiRadialCoord lam qpt ∈ Icc (-R) R ∧
      ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam qpt) ≤
        gluingFinFermiTransverseCoord lam qpt
    rw [hqptRad, hqptTrans]
    constructor
    · exact htwindow
    · calc
        ε * gluingCollarWarp r t ≤ ε * gluingCollarWarp r R :=
          mul_le_mul_of_nonneg_left hwarp hε
        _ ≤ gluingFinFermiTransverseCoord lam q.1 := hqfinR
  let q' : gluingCollarFiniteUpperFin r R lam ε := ⟨qpt, hqptFin⟩
  have hq'point : q'.1 = gluingFinFermiPoint lam t cq.2 := rfl
  have hqpoint : gluingFinFermiPoint lam R cq.2 = q.1 := by
    simpa [cq, gluingFinFermiInverse, hqcap] using
      gluingFinFermiPoint_inverse_right hlam q.1
  have hxpoint : gluingFinFermiPoint lam cx.1 cx.2 = x.1 := by
    simpa [cx, gluingFinFermiInverse] using
      gluingFinFermiPoint_inverse_right hlam x.1
  have hypoint : gluingFinFermiPoint lam cy.1 cy.2 = gluingMirror y.1 := by
    simpa [cy, gluingFinFermiInverse] using
      gluingFinFermiPoint_inverse_right hlam (gluingMirror y.1)
  have hcx_t : cx.1 < t := (le_max_left _ _).trans_lt hst
  have hcy_t : cy.1 < t := (le_max_right _ _).trans_lt hst
  have hcloserX : |t - cx.1| < |R - cx.1| := by
    rw [abs_of_pos (by linarith : 0 < t - cx.1),
      abs_of_pos (by linarith : 0 < R - cx.1)]
    linarith
  have hcloserY : |t - cy.1| < |R - cy.1| := by
    rw [abs_of_pos (by linarith : 0 < t - cy.1),
      abs_of_pos (by linarith : 0 < R - cy.1)]
    linarith
  have hcoshX := gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt
    (α := lam) (s := cx.1) (t₁ := R) (t₂ := t) (u := cq.2) (v := cx.2)
    hlam hcloserX
  have hcoshY := gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt
    (α := lam) (s := cy.1) (t₁ := R) (t₂ := t) (u := cq.2) (v := cy.2)
    hlam hcloserY
  have hcoshX' : Real.cosh (dist q'.1 x.1) < Real.cosh (dist q.1 x.1) := by
    calc
      _ = Real.cosh (dist (gluingFinFermiPoint lam t cq.2)
          (gluingFinFermiPoint lam cx.1 cx.2)) := by rw [hq'point, ← hxpoint]
      _ < Real.cosh (dist (gluingFinFermiPoint lam R cq.2)
          (gluingFinFermiPoint lam cx.1 cx.2)) := hcoshX
      _ = _ := by rw [hqpoint, hxpoint]
  have hcoshY' : Real.cosh (dist q'.1 (gluingMirror y.1)) <
      Real.cosh (dist q.1 (gluingMirror y.1)) := by
    calc
      _ = Real.cosh (dist (gluingFinFermiPoint lam t cq.2)
          (gluingFinFermiPoint lam cy.1 cy.2)) := by rw [hq'point, ← hypoint]
      _ < Real.cosh (dist (gluingFinFermiPoint lam R cq.2)
          (gluingFinFermiPoint lam cy.1 cy.2)) := hcoshY
      _ = _ := by rw [hqpoint, hypoint]
  have hdistX : dist q'.1 x.1 < dist q.1 x.1 := by
    have h := Real.cosh_lt_cosh.mp hcoshX'
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
    exact h
  have hdistY : dist q'.1 (gluingMirror y.1) <
      dist q.1 (gluingMirror y.1) := by
    have h := Real.cosh_lt_cosh.mp hcoshY'
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
    exact h
  have hmirror (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror w.1) = dist (gluingMirror y.1) w.1 := by
    calc
      dist y.1 (gluingMirror w.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror w.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror w.1)).symm
      _ = dist (gluingMirror y.1) w.1 := by rw [gluingMirror_involutive]
  have hcost (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) =
        dist x.1 w.1 + dist (gluingMirror y.1) w.1 := by
    simp only [gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight, Subtype.dist_eq]
    rw [hmirror w]
  have hminReflect : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
        dist x.1 w.1 + dist (gluingMirror y.1) w.1 := by
    intro w
    have h := hmin w
    rw [hcost q, hcost w] at h
    exact h
  have hcostlt : dist x.1 q'.1 + dist (gluingMirror y.1) q'.1 <
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
    simpa only [dist_comm] using add_lt_add hdistX hdistY
  exact (not_lt_of_ge (hminReflect q')) hcostlt

/-- A seam-cost minimizer cannot lie on the lower radial cap if both
cross-pair endpoints lie strictly above that cap. Moving the seam point
slightly inward at fixed transverse coordinate stays in the fin and strictly
shortens both hyperbolic legs. -/
theorem gluingCollarFiniteLowerFin_minimizer_ne_lower_radial_cap
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ≤
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε w))
    (hxR : -R < (gluingFinFermiInverse lam x.1).1)
    (hyR : -R < (gluingFinFermiInverse lam (gluingMirror y.1)).1) :
    gluingFinFermiRadialCoord lam q.1 ≠ -R := by
  intro hqcap
  let cq := gluingFinFermiInverse lam q.1
  let cx := gluingFinFermiInverse lam x.1
  let cy := gluingFinFermiInverse lam (gluingMirror y.1)
  have hxraw : gluingFinFermiRadialCoord lam x.1 ∈ Icc (-R) R := x.2
  have hyraw : gluingFinFermiRadialCoord lam y.1 ∈ Icc (-R) R := y.2
  have hxwindow : cx.1 ∈ Icc (-R) R := by
    simpa [cx, gluingFinFermiInverse] using hxraw
  have hywindow : cy.1 ∈ Icc (-R) R := by
    simpa [cy, gluingFinFermiInverse, gluingFinFermiRadialCoord_mirror] using hyraw
  have hs : -R < min cx.1 cy.1 := lt_min_iff.mpr ⟨hxR, hyR⟩
  let t : ℝ := (-R + min cx.1 cy.1) / 2
  have hRt : -R < t := by dsimp [t]; linarith
  have htmin : t < min cx.1 cy.1 := by dsimp [t]; linarith
  have htwindow : t ∈ Icc (-R) R := by
    constructor
    · exact hRt.le
    · dsimp [t]
      linarith [hywindow.2, min_le_right cx.1 cy.1]
  have hwarp : gluingCollarWarp r t ≤ gluingCollarWarp r (-R) := by
    rw [gluingCollarWarp, gluingCollarWarp,
      abs_of_neg (by linarith : -R < 0)]
    apply Real.sinh_le_sinh.mpr
    have habs : |t| ≤ R := abs_le.mpr htwindow
    linarith
  rcases q.2 with ⟨⟨hqlo, _⟩, hqfin⟩
  have hqfinR : ε * gluingCollarWarp r (-R) ≤
      gluingFinFermiTransverseCoord lam q.1 := by
    simpa [hqcap] using hqfin
  let qpt := gluingFinFermiPoint lam t cq.2
  have hqptRad := gluingFinFermiRadialCoord_point
    (α := lam) (t := t) (u := cq.2) hlam
  have hqptTrans := gluingFinFermiTransverseCoord_point
    (α := lam) (t := t) (u := cq.2) hlam
  have hqptFin : qpt ∈ gluingCollarFiniteUpperFin r R lam ε := by
    change gluingFinFermiRadialCoord lam qpt ∈ Icc (-R) R ∧
      ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam qpt) ≤
        gluingFinFermiTransverseCoord lam qpt
    rw [hqptRad, hqptTrans]
    constructor
    · exact htwindow
    · calc
        ε * gluingCollarWarp r t ≤ ε * gluingCollarWarp r (-R) :=
          mul_le_mul_of_nonneg_left hwarp hε
        _ ≤ gluingFinFermiTransverseCoord lam q.1 := hqfinR
  let q' : gluingCollarFiniteUpperFin r R lam ε := ⟨qpt, hqptFin⟩
  have hq'point : q'.1 = gluingFinFermiPoint lam t cq.2 := rfl
  have hqpoint : gluingFinFermiPoint lam (-R) cq.2 = q.1 := by
    simpa [cq, gluingFinFermiInverse, hqcap] using
      gluingFinFermiPoint_inverse_right hlam q.1
  have hxpoint : gluingFinFermiPoint lam cx.1 cx.2 = x.1 := by
    simpa [cx, gluingFinFermiInverse] using
      gluingFinFermiPoint_inverse_right hlam x.1
  have hypoint : gluingFinFermiPoint lam cy.1 cy.2 = gluingMirror y.1 := by
    simpa [cy, gluingFinFermiInverse] using
      gluingFinFermiPoint_inverse_right hlam (gluingMirror y.1)
  have hmin_t_x : t < cx.1 := lt_of_lt_of_le htmin (min_le_left _ _)
  have hmin_t_y : t < cy.1 := lt_of_lt_of_le htmin (min_le_right _ _)
  have hcloserX : |t - cx.1| < |-R - cx.1| := by
    rw [abs_of_neg (by linarith : t - cx.1 < 0),
      abs_of_neg (by linarith : -R - cx.1 < 0)]
    linarith
  have hcloserY : |t - cy.1| < |-R - cy.1| := by
    rw [abs_of_neg (by linarith : t - cy.1 < 0),
      abs_of_neg (by linarith : -R - cy.1 < 0)]
    linarith
  have hcoshX := gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt
    (α := lam) (s := cx.1) (t₁ := -R) (t₂ := t) (u := cq.2) (v := cx.2)
    hlam hcloserX
  have hcoshY := gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt
    (α := lam) (s := cy.1) (t₁ := -R) (t₂ := t) (u := cq.2) (v := cy.2)
    hlam hcloserY
  have hcoshX' : Real.cosh (dist q'.1 x.1) < Real.cosh (dist q.1 x.1) := by
    calc
      _ = Real.cosh (dist (gluingFinFermiPoint lam t cq.2)
          (gluingFinFermiPoint lam cx.1 cx.2)) := by rw [hq'point, ← hxpoint]
      _ < Real.cosh (dist (gluingFinFermiPoint lam (-R) cq.2)
          (gluingFinFermiPoint lam cx.1 cx.2)) := hcoshX
      _ = _ := by rw [hqpoint, hxpoint]
  have hcoshY' : Real.cosh (dist q'.1 (gluingMirror y.1)) <
      Real.cosh (dist q.1 (gluingMirror y.1)) := by
    calc
      _ = Real.cosh (dist (gluingFinFermiPoint lam t cq.2)
          (gluingFinFermiPoint lam cy.1 cy.2)) := by rw [hq'point, ← hypoint]
      _ < Real.cosh (dist (gluingFinFermiPoint lam (-R) cq.2)
          (gluingFinFermiPoint lam cy.1 cy.2)) := hcoshY
      _ = _ := by rw [hqpoint, hypoint]
  have hdistX : dist q'.1 x.1 < dist q.1 x.1 := by
    have h := Real.cosh_lt_cosh.mp hcoshX'
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
    exact h
  have hdistY : dist q'.1 (gluingMirror y.1) <
      dist q.1 (gluingMirror y.1) := by
    have h := Real.cosh_lt_cosh.mp hcoshY'
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
    exact h
  have hmirror (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror w.1) = dist (gluingMirror y.1) w.1 := by
    calc
      dist y.1 (gluingMirror w.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror w.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror w.1)).symm
      _ = dist (gluingMirror y.1) w.1 := by rw [gluingMirror_involutive]
  have hcost (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) =
        dist x.1 w.1 + dist (gluingMirror y.1) w.1 := by
    simp only [gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight, Subtype.dist_eq]
    rw [hmirror w]
  have hminReflect : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
        dist x.1 w.1 + dist (gluingMirror y.1) w.1 := by
    intro w
    have h := hmin w
    rw [hcost q, hcost w] at h
    exact h
  have hcostlt : dist x.1 q'.1 + dist (gluingMirror y.1) q'.1 <
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
    simpa only [dist_comm] using add_lt_add hdistX hdistY
  exact (not_lt_of_ge (hminReflect q')) hcostlt

/-- The attained common-fin minimizer for opposite-copy endpoints strictly
inside the upper radial cap lies below that cap. -/
theorem gluingCollarFiniteMetricGlue_cross_dist_attained_below_upper_cap
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam) (hε : 0 ≤ ε)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (hxR : (gluingFinFermiInverse lam x.1).1 < R)
    (hyR : (gluingFinFermiInverse lam (gluingMirror y.1)).1 < R) :
    ∃ q : gluingCollarFiniteUpperFin r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ∧
      gluingFinFermiRadialCoord lam q.1 < R := by
  obtain ⟨q, hqattain⟩ := gluingCollarFiniteMetricGlue_cross_dist_attained
    (r := r) (R := R) (lam := lam) (ε := ε) hR.le hlam x y
  have hcross := gluingCollarFiniteMetricGlue_cross_dist r R lam ε x y
  have hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ≤
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) := by
    intro w
    have hbounded : BddBelow (Set.range (fun z : gluingCollarFiniteUpperFin r R lam ε =>
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε z))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, rfl⟩
      positivity
    calc
      _ = dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) :=
        hqattain.symm
      _ = ⨅ z : gluingCollarFiniteUpperFin r R lam ε,
          dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
            dist y (gluingCollarFiniteMetricGlueRight r R lam ε z) := hcross
      _ ≤ dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) :=
        ciInf_le hbounded w
  have hqne := gluingCollarFiniteUpperFin_minimizer_ne_upper_radial_cap
    hR hlam hε x y q hmin hxR hyR
  rcases q.2 with ⟨⟨_, hqradle⟩, _⟩
  rcases lt_or_eq_of_le hqradle with hlt | heq
  · exact ⟨q, hqattain, hlt⟩
  · exact (hqne heq).elim

/-- If both cross-pair endpoints lie strictly inside the radial window, an
attained common-fin minimizer lies strictly inside the window as well. -/
theorem gluingCollarFiniteMetricGlue_cross_dist_attained_radially_interior
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam) (hε : 0 ≤ ε)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (hxlo : -R < (gluingFinFermiInverse lam x.1).1)
    (hxhi : (gluingFinFermiInverse lam x.1).1 < R)
    (hylo : -R < (gluingFinFermiInverse lam (gluingMirror y.1)).1)
    (hyhi : (gluingFinFermiInverse lam (gluingMirror y.1)).1 < R) :
    ∃ q : gluingCollarFiniteUpperFin r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ∧
      gluingFinFermiRadialCoord lam q.1 ∈ Ioo (-R) R := by
  obtain ⟨q, hqattain, hqhi⟩ :=
    gluingCollarFiniteMetricGlue_cross_dist_attained_below_upper_cap
      (r := r) (R := R) (lam := lam) (ε := ε) hR hlam hε x y hxhi hyhi
  have hcross := gluingCollarFiniteMetricGlue_cross_dist r R lam ε x y
  have hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ≤
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) := by
    intro w
    have hbounded : BddBelow (Set.range (fun z : gluingCollarFiniteUpperFin r R lam ε =>
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε z))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, rfl⟩
      positivity
    calc
      _ = dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) :=
        hqattain.symm
      _ = ⨅ z : gluingCollarFiniteUpperFin r R lam ε,
          dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
            dist y (gluingCollarFiniteMetricGlueRight r R lam ε z) := hcross
      _ ≤ dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) :=
        ciInf_le hbounded w
  have hqne := gluingCollarFiniteLowerFin_minimizer_ne_lower_radial_cap
    hR hlam hε x y q hmin hxlo hylo
  rcases q.2 with ⟨⟨hqlo, _⟩, _⟩
  have hradlo : -R < gluingFinFermiRadialCoord lam q.1 := by
    rcases lt_or_eq_of_le hqlo with hlt | heq
    · exact hlt
    · exact (hqne heq.symm).elim
  exact ⟨q, hqattain, ⟨hradlo, hqhi⟩⟩

/-- The `cosh` of distance from a fixed Fermi point to the seam graph, written
as an explicit scalar function of the graph's radial coordinate. -/
noncomputable def gluingFinFermiSeamCoshDist
    (α r ε s u t : ℝ) : ℝ :=
  Real.cosh (α * u) *
      Real.cosh (α * (ε * gluingCollarWarp r t)) *
      Real.cosh (α * (s - t)) -
    Real.sinh (α * u) * Real.sinh (α * (ε * gluingCollarWarp r t))

/-- Away from the nonsmooth center of the seam profile, the explicit `cosh`
distance along the seam is differentiable. -/
theorem gluingFinFermiSeamCoshDist_hasDerivAt
    {α r ε s u t : ℝ} (ht0 : t ≠ 0) :
    HasDerivAt (gluingFinFermiSeamCoshDist α r ε s u)
      (deriv (gluingFinFermiSeamCoshDist α r ε s u) t) t := by
  have hwarp := gluingCollarWarp_hasDerivAt_of_ne r ht0
  have hwarpDiff : DifferentiableAt ℝ (gluingCollarWarp r) t := hwarp.differentiableAt
  have hdiff : DifferentiableAt ℝ (gluingFinFermiSeamCoshDist α r ε s u) t := by
    unfold gluingFinFermiSeamCoshDist
    fun_prop
  exact hdiff.hasDerivAt

/-- At a seam point away from its central kink, distance to a fixed point
different from that seam point is differentiable along the seam graph. The
formula uses `arcosh` of the explicit Fermi `cosh`-distance. -/
theorem gluingFinFermiSeamGraph_dist_hasDerivAt
    {α r ε s u t : ℝ} (ht0 : t ≠ 0)
    (hneq : gluingFinFermiPoint α s u ≠
      gluingFinFermiPoint α t (ε * gluingCollarWarp r t)) :
    HasDerivAt
      (fun v : ℝ => dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)))
      ((Real.sqrt (gluingFinFermiSeamCoshDist α r ε s u t ^ 2 - 1))⁻¹ *
        deriv (gluingFinFermiSeamCoshDist α r ε s u) t) t := by
  let C := gluingFinFermiSeamCoshDist α r ε s u
  have hC : HasDerivAt C (deriv C t) t := by
    simpa only [C] using gluingFinFermiSeamCoshDist_hasDerivAt (α := α)
      (r := r) (ε := ε) (s := s) (u := u) ht0
  have hcosh (v : ℝ) :
      Real.cosh (dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) = C v := by
    simpa [C, gluingFinFermiSeamCoshDist] using
      gluingFinFermiPoint_cosh_dist α s u v (ε * gluingCollarWarp r v)
  have hdist_eq (v : ℝ) :
      dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)) =
          Real.arcosh (C v) := by
    calc
      _ = Real.arcosh (Real.cosh
          (dist (gluingFinFermiPoint α s u)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)))) :=
        (Real.arcosh_cosh dist_nonneg).symm
      _ = Real.arcosh (C v) := by rw [hcosh v]
  have hdistpos : 0 < dist (gluingFinFermiPoint α s u)
      (gluingFinFermiPoint α t (ε * gluingCollarWarp r t)) :=
    dist_pos.mpr hneq
  have hCgt : 1 < C t := by
    rw [← hcosh t, Real.one_lt_cosh]
    exact ne_of_gt hdistpos
  have hA := (Real.hasDerivAt_arcosh hCgt).comp t hC
  have hdist : (fun v : ℝ => dist (gluingFinFermiPoint α s u)
      (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) =ᶠ[nhds t]
      (fun v => Real.arcosh (C v)) :=
    Filter.Eventually.of_forall hdist_eq
  have hA' := hA.congr_of_eventuallyEq hdist
  simpa only [C, hC.deriv] using hA'

/-- At a local minimum of the sum of distances along a smooth part of the
seam graph, the tangential first variation vanishes. Coincident endpoints
are excluded here; their one-sided distance variation is a separate case. -/
theorem gluingFinFermiSeamGraph_distanceSum_stationary
    {α r ε s₁ u₁ s₂ u₂ t : ℝ} (ht0 : t ≠ 0)
    (hneq₁ : gluingFinFermiPoint α s₁ u₁ ≠
      gluingFinFermiPoint α t (ε * gluingCollarWarp r t))
    (hneq₂ : gluingFinFermiPoint α s₂ u₂ ≠
      gluingFinFermiPoint α t (ε * gluingCollarWarp r t))
    (hmin : IsLocalMin
      (fun v : ℝ =>
        dist (gluingFinFermiPoint α s₁ u₁)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)) +
          dist (gluingFinFermiPoint α s₂ u₂)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) t) :
    deriv (fun v : ℝ =>
      dist (gluingFinFermiPoint α s₁ u₁)
          (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)) +
        dist (gluingFinFermiPoint α s₂ u₂)
          (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) t = 0 := by
  have h₁ := gluingFinFermiSeamGraph_dist_hasDerivAt ht0 hneq₁
  have h₂ := gluingFinFermiSeamGraph_dist_hasDerivAt ht0 hneq₂
  have hsum := h₁.add h₂
  have hstationary := hmin.hasDerivAt_eq_zero hsum
  calc
    deriv (fun v : ℝ =>
        dist (gluingFinFermiPoint α s₁ u₁)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)) +
          dist (gluingFinFermiPoint α s₂ u₂)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) t = _ :=
      hsum.deriv
    _ = 0 := hstationary

/-- A local minimum with a right derivative has nonnegative right derivative.
This half-interval form is what the seam's center kink requires. -/
theorem isLocalMin_hasDerivWithinAt_nonneg_Ici
    {f : ℝ → ℝ} {d : ℝ} (hmin : IsLocalMin f 0)
    (hderiv : HasDerivWithinAt f d (Ici 0) 0) : 0 ≤ d := by
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
    rw [one_mem_posTangentConeAt_iff_frequently, frequently_nhdsWithin_iff]
    have hfreq : ∃ᶠ x in nhds (0 : ℝ), x ∈ Ioi (0 : ℝ) := by
      rw [← mem_closure_iff_frequently]
      simp [closure_Ioi]
    exact hfreq.mono fun x hx => by
      change 0 < x at hx
      exact ⟨le_of_lt hx, hx⟩
  have hlocal : IsLocalMinOn f (Ici 0) 0 := hmin.on (Ici 0)
  have h := hlocal.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt htangent
  simpa using h

/-- A local minimum with a left derivative has nonpositive left derivative.
The direction into `Iic 0` is `-1`. -/
theorem isLocalMin_hasDerivWithinAt_nonpos_Iic
    {f : ℝ → ℝ} {d : ℝ} (hmin : IsLocalMin f 0)
    (hderiv : HasDerivWithinAt f d (Iic 0) 0) : d ≤ 0 := by
  have hneg : HasDerivWithinAt (fun x : ℝ => -x) (-1) (Ici 0) 0 := by
    simpa using (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
  have hmap : MapsTo (fun x : ℝ => -x) (Ici 0) (Iic 0) := by
    intro x hx
    change 0 ≤ x at hx
    exact neg_nonpos.mpr hx
  have hderiv0 : HasDerivWithinAt f d (Iic 0) (-0) := by simpa using hderiv
  have hderiv' : HasDerivWithinAt (fun x : ℝ => f (-x)) (-d) (Ici 0) 0 := by
    simpa [Function.comp_def] using hderiv0.comp 0 hneg hmap
  have hmin0 : IsLocalMin f (-0) := by simpa using hmin
  have hmin' : IsLocalMin (fun x : ℝ => f (-x)) 0 :=
    hmin0.comp_continuous (g := fun x : ℝ => -x) (b := 0) continuousAt_neg
  have hnonneg : 0 ≤ -d :=
    isLocalMin_hasDerivWithinAt_nonneg_Ici hmin' hderiv'
  linarith

/-- The smooth right-hand formula for the `cosh`-distance from a fixed Fermi
point to the seam graph. The actual warp agrees with this branch on `Ici 0`. -/
noncomputable def gluingFinFermiSeamCoshDistRightBranch
    (α r ε s u v : ℝ) : ℝ :=
  Real.cosh (α * u) * Real.cosh (α * (ε * Real.sinh (r + v))) *
      Real.cosh (α * (s - v)) -
    Real.sinh (α * u) * Real.sinh (α * (ε * Real.sinh (r + v)))

/-- The smooth left-hand formula for the `cosh`-distance from a fixed Fermi
point to the seam graph. The actual warp agrees with this branch on `Iic 0`. -/
noncomputable def gluingFinFermiSeamCoshDistLeftBranch
    (α r ε s u v : ℝ) : ℝ :=
  Real.cosh (α * u) * Real.cosh (α * (ε * Real.sinh (r - v))) *
      Real.cosh (α * (s - v)) -
    Real.sinh (α * u) * Real.sinh (α * (ε * Real.sinh (r - v)))

/-- Transfer a smooth derivative of the explicit `cosh` profile through
`arcosh` to distance, provided the fixed endpoint is not the point at the
base parameter. -/
theorem gluingFinFermiSeamGraph_dist_hasDerivWithinAt_of_coshDist
    {α r ε s u a : ℝ} {S : Set ℝ} {C : ℝ → ℝ}
    (hC : HasDerivAt C (deriv C a) a)
    (hcosh : ∀ v ∈ S,
      Real.cosh (dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) = C v)
    (ha : a ∈ S)
    (hneq : gluingFinFermiPoint α s u ≠
      gluingFinFermiPoint α a (ε * gluingCollarWarp r a)) :
    HasDerivWithinAt
      (fun v : ℝ => dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)))
      ((Real.sqrt (C a ^ 2 - 1))⁻¹ * deriv C a) S a := by
  have hdist_eq (v : ℝ) (hv : v ∈ S) :
      dist (gluingFinFermiPoint α s u)
          (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)) =
        Real.arcosh (C v) := by
    calc
      _ = Real.arcosh (Real.cosh
          (dist (gluingFinFermiPoint α s u)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)))) :=
        (Real.arcosh_cosh dist_nonneg).symm
      _ = Real.arcosh (C v) := by rw [hcosh v hv]
  have hdistpos : 0 < dist (gluingFinFermiPoint α s u)
      (gluingFinFermiPoint α a (ε * gluingCollarWarp r a)) := dist_pos.mpr hneq
  have hCgt : 1 < C a := by
    rw [← hcosh a ha, Real.one_lt_cosh]
    exact ne_of_gt hdistpos
  have hA := (Real.hasDerivAt_arcosh hCgt).comp a hC
  have hresult := hA.hasDerivWithinAt.congr_of_mem hdist_eq ha
  simpa only [hA.deriv] using hresult

/-- Away from coincident endpoints, distance along the seam graph has a
right derivative at the radial center, computed using the positive branch. -/
theorem gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_right
    {α r ε s u : ℝ}
    (hneq : gluingFinFermiPoint α s u ≠
      gluingFinFermiPoint α 0 (ε * gluingCollarWarp r 0)) :
    HasDerivWithinAt
      (fun v : ℝ => dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)))
      ((Real.sqrt (gluingFinFermiSeamCoshDistRightBranch α r ε s u 0 ^ 2 - 1))⁻¹ *
        deriv (gluingFinFermiSeamCoshDistRightBranch α r ε s u) 0)
      (Ici 0) 0 := by
  let C := gluingFinFermiSeamCoshDistRightBranch α r ε s u
  have hC : HasDerivAt C (deriv C 0) 0 := by
    have hdiff : DifferentiableAt ℝ C 0 := by
      unfold C gluingFinFermiSeamCoshDistRightBranch
      fun_prop
    exact hdiff.hasDerivAt
  have hcosh (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) :
    Real.cosh (dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) = C v := by
    simpa [C, gluingFinFermiSeamCoshDistRightBranch,
      gluingCollarWarp_eq_of_nonneg r hv] using
      gluingFinFermiPoint_cosh_dist α s u v (ε * gluingCollarWarp r v)
  have hneqC : gluingFinFermiPoint α s u ≠
      gluingFinFermiPoint α 0 (ε * gluingCollarWarp r 0) := hneq
  simpa only [C] using
    gluingFinFermiSeamGraph_dist_hasDerivWithinAt_of_coshDist hC hcosh
      (by simp) hneqC

/-- Away from coincident endpoints, distance along the seam graph has a
left derivative at the radial center, computed using the negative branch. -/
theorem gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_left
    {α r ε s u : ℝ}
    (hneq : gluingFinFermiPoint α s u ≠
      gluingFinFermiPoint α 0 (ε * gluingCollarWarp r 0)) :
    HasDerivWithinAt
      (fun v : ℝ => dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)))
      ((Real.sqrt (gluingFinFermiSeamCoshDistLeftBranch α r ε s u 0 ^ 2 - 1))⁻¹ *
        deriv (gluingFinFermiSeamCoshDistLeftBranch α r ε s u) 0)
      (Iic 0) 0 := by
  let C := gluingFinFermiSeamCoshDistLeftBranch α r ε s u
  have hC : HasDerivAt C (deriv C 0) 0 := by
    have hdiff : DifferentiableAt ℝ C 0 := by
      unfold C gluingFinFermiSeamCoshDistLeftBranch
      fun_prop
    exact hdiff.hasDerivAt
  have hcosh (v : ℝ) (hv : v ∈ Iic (0 : ℝ)) :
    Real.cosh (dist (gluingFinFermiPoint α s u)
        (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) = C v := by
    simpa [C, gluingFinFermiSeamCoshDistLeftBranch,
      gluingCollarWarp_eq_of_nonpos r hv] using
      gluingFinFermiPoint_cosh_dist α s u v (ε * gluingCollarWarp r v)
  simpa only [C] using
    gluingFinFermiSeamGraph_dist_hasDerivWithinAt_of_coshDist hC hcosh
      (by simp) hneq

/-- At a local minimum of the two-endpoint seam distance at the warp's
center, the right derivative is nonnegative and the left derivative is
nonpositive. This is the precise first-order condition at the kink. -/
theorem gluingFinFermiSeamGraph_distanceSum_center_subgradient
    {α r ε s₁ u₁ s₂ u₂ : ℝ}
    (hneq₁ : gluingFinFermiPoint α s₁ u₁ ≠
      gluingFinFermiPoint α 0 (ε * gluingCollarWarp r 0))
    (hneq₂ : gluingFinFermiPoint α s₂ u₂ ≠
      gluingFinFermiPoint α 0 (ε * gluingCollarWarp r 0))
    (hmin : IsLocalMin
      (fun v : ℝ =>
        dist (gluingFinFermiPoint α s₁ u₁)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v)) +
          dist (gluingFinFermiPoint α s₂ u₂)
            (gluingFinFermiPoint α v (ε * gluingCollarWarp r v))) 0) :
    0 ≤
        (Real.sqrt (gluingFinFermiSeamCoshDistRightBranch α r ε s₁ u₁ 0 ^ 2 - 1))⁻¹ *
            deriv (gluingFinFermiSeamCoshDistRightBranch α r ε s₁ u₁) 0 +
          (Real.sqrt (gluingFinFermiSeamCoshDistRightBranch α r ε s₂ u₂ 0 ^ 2 - 1))⁻¹ *
            deriv (gluingFinFermiSeamCoshDistRightBranch α r ε s₂ u₂) 0 ∧
      (Real.sqrt (gluingFinFermiSeamCoshDistLeftBranch α r ε s₁ u₁ 0 ^ 2 - 1))⁻¹ *
            deriv (gluingFinFermiSeamCoshDistLeftBranch α r ε s₁ u₁) 0 +
          (Real.sqrt (gluingFinFermiSeamCoshDistLeftBranch α r ε s₂ u₂ 0 ^ 2 - 1))⁻¹ *
            deriv (gluingFinFermiSeamCoshDistLeftBranch α r ε s₂ u₂) 0 ≤ 0 := by
  have hright₁ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_right hneq₁
  have hright₂ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_right hneq₂
  have hleft₁ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_left hneq₁
  have hleft₂ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_left hneq₂
  constructor
  · exact isLocalMin_hasDerivWithinAt_nonneg_Ici hmin (hright₁.add hright₂)
  · exact isLocalMin_hasDerivWithinAt_nonpos_Iic hmin (hleft₁.add hleft₂)

/-- A radially interior minimizer on the seam graph is a local minimizer of
the explicit two-endpoint distance sum parametrized by radial coordinate.
Nearby points of the graph remain admissible points of the upper fin, so this
is the bridge from the attained metric-gluing minimizer to seam calculus. -/
theorem gluingCollarFiniteMetricGlue_seamGraph_isLocalMin
    {r R lam ε : ℝ} (hlam : 0 < lam)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqrad : gluingFinFermiRadialCoord lam q.1 ∈ Ioo (-R) R)
    (hqseam : ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
      gluingFinFermiTransverseCoord lam q.1)
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t)) :
    IsLocalMin
      (fun v : ℝ =>
        dist (gluingFinFermiPoint lam
            (gluingFinFermiInverse lam x.1).1
            (gluingFinFermiInverse lam x.1).2)
          (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)) +
        dist (gluingFinFermiPoint lam
            (gluingFinFermiInverse lam (gluingMirror y.1)).1
            (gluingFinFermiInverse lam (gluingMirror y.1)).2)
          (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
      (gluingFinFermiRadialCoord lam q.1) := by
  let t₀ := gluingFinFermiRadialCoord lam q.1
  have hqpoint :
      gluingFinFermiPoint lam t₀ (ε * gluingCollarWarp r t₀) = q.1 := by
    rw [← gluingFinFermiPoint_inverse_right hlam q.1]
    simp [t₀, gluingFinFermiInverse, hqseam]
  have hxpoint :
      gluingFinFermiPoint lam (gluingFinFermiInverse lam x.1).1
        (gluingFinFermiInverse lam x.1).2 = x.1 :=
    gluingFinFermiPoint_inverse_right hlam x.1
  have hypoint :
      gluingFinFermiPoint lam
        (gluingFinFermiInverse lam (gluingMirror y.1)).1
        (gluingFinFermiInverse lam (gluingMirror y.1)).2 = gluingMirror y.1 :=
    gluingFinFermiPoint_inverse_right hlam (gluingMirror y.1)
  have hnear : ∀ᶠ v : ℝ in nhds t₀, v ∈ Ioo (-R) R :=
    Ioo_mem_nhds hqrad.1 hqrad.2
  apply Filter.Eventually.mono hnear
  intro v hv
  let p := gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)
  have hpfin : p ∈ gluingCollarFiniteUpperFin r R lam ε := by
    change gluingFinFermiRadialCoord lam p ∈ Icc (-R) R ∧
      ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam p) ≤
        gluingFinFermiTransverseCoord lam p
    rw [gluingFinFermiRadialCoord_point hlam,
      gluingFinFermiTransverseCoord_point hlam]
    exact ⟨⟨hv.1.le, hv.2.le⟩, le_rfl⟩
  let w : gluingCollarFiniteUpperFin r R lam ε := ⟨p, hpfin⟩
  have h := hmin w 1 (by norm_num)
  rw [← hxpoint, ← hypoint, ← hqpoint] at h
  simpa [p, w, Vendored.RiemannDynamics.geodInterp_one] using h

/-- Specialize the seam-graph local-minimum bridge to a minimizer at radial
coordinate zero, expressed directly with the actual cross-copy endpoints. -/
theorem gluingCollarFiniteMetricGlue_centerSeam_isLocalMin
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqrad : gluingFinFermiRadialCoord lam q.1 = 0)
    (hqseam : ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
      gluingFinFermiTransverseCoord lam q.1)
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t)) :
    IsLocalMin
      (fun v : ℝ =>
        dist x.1 (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)) +
          dist (gluingMirror y.1)
            (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v))) 0 := by
  have hqrad' : gluingFinFermiRadialCoord lam q.1 ∈ Ioo (-R) R := by
    rw [hqrad]
    exact ⟨neg_lt_zero.mpr hR, hR⟩
  have hlocal := gluingCollarFiniteMetricGlue_seamGraph_isLocalMin
    hlam x y q hqrad' hqseam hmin
  have hlocal0 : IsLocalMin (fun v : ℝ =>
      dist (gluingFinFermiPoint lam
          (gluingFinFermiInverse lam x.1).1
          (gluingFinFermiInverse lam x.1).2)
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)) +
      dist (gluingFinFermiPoint lam
          (gluingFinFermiInverse lam (gluingMirror y.1)).1
          (gluingFinFermiInverse lam (gluingMirror y.1)).2)
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v))) 0 := by
    simpa [hqrad] using hlocal
  have hxpoint := gluingFinFermiPoint_inverse_right hlam x.1
  have hypoint := gluingFinFermiPoint_inverse_right hlam (gluingMirror y.1)
  apply hlocal0.congr
  filter_upwards [] with v
  simp only [hxpoint, hypoint]

/-- An actual cross-copy minimizer at the center of the seam graph satisfies
the right/left derivative inequalities for the distance sum along the graph.
The result is stated with `derivWithin` so the one-sided directions are
explicit in later boundary-angle comparisons. -/
theorem gluingCollarFiniteMetricGlue_centerSeam_subgradient
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqrad : gluingFinFermiRadialCoord lam q.1 = 0)
    (hqseam : ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
      gluingFinFermiTransverseCoord lam q.1)
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t))
    (hxq : x.1 ≠ q.1) (hyq : gluingMirror y.1 ≠ q.1) :
    0 ≤ derivWithin (fun v : ℝ =>
        dist x.1 (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)) +
          dist (gluingMirror y.1)
            (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
        (Ici 0) 0 ∧
      derivWithin (fun v : ℝ =>
        dist x.1 (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)) +
          dist (gluingMirror y.1)
            (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
        (Iic 0) 0 ≤ 0 := by
  have hlocal := gluingCollarFiniteMetricGlue_centerSeam_isLocalMin
    hR hlam x y q hqrad hqseam hmin
  have hqpoint :
      gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0) = q.1 := by
    rw [← gluingFinFermiPoint_inverse_right hlam q.1]
    have hseam0 : ε * gluingCollarWarp r 0 =
        gluingFinFermiTransverseCoord lam q.1 := by
      simpa [hqrad] using hqseam
    simp only [gluingFinFermiInverse, hqrad]
    rw [← hseam0]
  have hxpoint :
      gluingFinFermiPoint lam (gluingFinFermiInverse lam x.1).1
        (gluingFinFermiInverse lam x.1).2 = x.1 :=
    gluingFinFermiPoint_inverse_right hlam x.1
  have hypoint :
      gluingFinFermiPoint lam
        (gluingFinFermiInverse lam (gluingMirror y.1)).1
        (gluingFinFermiInverse lam (gluingMirror y.1)).2 = gluingMirror y.1 :=
    gluingFinFermiPoint_inverse_right hlam (gluingMirror y.1)
  have hneq₁ : gluingFinFermiPoint lam
      (gluingFinFermiInverse lam x.1).1
      (gluingFinFermiInverse lam x.1).2 ≠
        gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0) := by
    rw [hxpoint, hqpoint]
    exact hxq
  have hneq₂ : gluingFinFermiPoint lam
      (gluingFinFermiInverse lam (gluingMirror y.1)).1
      (gluingFinFermiInverse lam (gluingMirror y.1)).2 ≠
        gluingFinFermiPoint lam 0 (ε * gluingCollarWarp r 0) := by
    rw [hypoint, hqpoint]
    exact hyq
  have hr₁ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_right hneq₁
  have hr₂ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_right hneq₂
  have hl₁ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_left hneq₁
  have hl₂ := gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_left hneq₂
  let dR₁ :=
    (Real.sqrt (gluingFinFermiSeamCoshDistRightBranch lam r ε
      (gluingFinFermiInverse lam x.1).1 (gluingFinFermiInverse lam x.1).2 0 ^ 2 - 1))⁻¹ *
      deriv (gluingFinFermiSeamCoshDistRightBranch lam r ε
        (gluingFinFermiInverse lam x.1).1 (gluingFinFermiInverse lam x.1).2) 0
  let dR₂ :=
    (Real.sqrt (gluingFinFermiSeamCoshDistRightBranch lam r ε
      (gluingFinFermiInverse lam (gluingMirror y.1)).1
      (gluingFinFermiInverse lam (gluingMirror y.1)).2 0 ^ 2 - 1))⁻¹ *
      deriv (gluingFinFermiSeamCoshDistRightBranch lam r ε
        (gluingFinFermiInverse lam (gluingMirror y.1)).1
        (gluingFinFermiInverse lam (gluingMirror y.1)).2) 0
  let dL₁ :=
    (Real.sqrt (gluingFinFermiSeamCoshDistLeftBranch lam r ε
      (gluingFinFermiInverse lam x.1).1 (gluingFinFermiInverse lam x.1).2 0 ^ 2 - 1))⁻¹ *
      deriv (gluingFinFermiSeamCoshDistLeftBranch lam r ε
        (gluingFinFermiInverse lam x.1).1 (gluingFinFermiInverse lam x.1).2) 0
  let dL₂ :=
    (Real.sqrt (gluingFinFermiSeamCoshDistLeftBranch lam r ε
      (gluingFinFermiInverse lam (gluingMirror y.1)).1
      (gluingFinFermiInverse lam (gluingMirror y.1)).2 0 ^ 2 - 1))⁻¹ *
      deriv (gluingFinFermiSeamCoshDistLeftBranch lam r ε
        (gluingFinFermiInverse lam (gluingMirror y.1)).1
        (gluingFinFermiInverse lam (gluingMirror y.1)).2) 0
  have hr₁' : HasDerivWithinAt
      (fun v : ℝ => dist x.1
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
      dR₁ (Ici 0) 0 := by simpa only [dR₁, hxpoint] using hr₁
  have hr₂' : HasDerivWithinAt
      (fun v : ℝ => dist (gluingMirror y.1)
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
      dR₂ (Ici 0) 0 := by simpa only [dR₂, hypoint] using hr₂
  have hl₁' : HasDerivWithinAt
      (fun v : ℝ => dist x.1
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
      dL₁ (Iic 0) 0 := by simpa only [dL₁, hxpoint] using hl₁
  have hl₂' : HasDerivWithinAt
      (fun v : ℝ => dist (gluingMirror y.1)
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
      dL₂ (Iic 0) 0 := by simpa only [dL₂, hypoint] using hl₂
  have hright := hr₁'.add hr₂'
  have hleft := hl₁'.add hl₂'
  have hright_nonneg := isLocalMin_hasDerivWithinAt_nonneg_Ici hlocal hright
  have hleft_nonpos := isLocalMin_hasDerivWithinAt_nonpos_Iic hlocal hleft
  constructor
  · change 0 ≤ derivWithin
      ((fun v : ℝ => dist x.1
          (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v))) +
        (fun v : ℝ => dist (gluingMirror y.1)
          (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))) (Ici 0) 0
    rw [hright.derivWithin (uniqueDiffWithinAt_Ici 0)]
    exact hright_nonneg
  · change derivWithin
      ((fun v : ℝ => dist x.1
          (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v))) +
        (fun v : ℝ => dist (gluingMirror y.1)
          (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))) (Iic 0) 0 ≤ 0
    rw [hleft.derivWithin (uniqueDiffWithinAt_Iic 0)]
    exact hleft_nonpos

/-- Tangential stationarity at a noncentral seam-graph minimizer follows from
the actual fin-minimizing inequality, not from an extra geometric assumption.
The endpoint-noncoincidence hypotheses are isolated for the smooth distance
derivative; the coincident cases need one-sided variation instead. -/
theorem gluingCollarFiniteMetricGlue_seamGraph_tangential_stationary
    {r R lam ε : ℝ} (hlam : 0 < lam)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqrad : gluingFinFermiRadialCoord lam q.1 ∈ Ioo (-R) R)
    (hqseam : ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
      gluingFinFermiTransverseCoord lam q.1)
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t))
    (ht0 : gluingFinFermiRadialCoord lam q.1 ≠ 0)
    (hxq : x.1 ≠ q.1) (hyq : gluingMirror y.1 ≠ q.1) :
    deriv (fun v : ℝ =>
      dist (gluingFinFermiPoint lam (gluingFinFermiInverse lam x.1).1
          (gluingFinFermiInverse lam x.1).2)
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)) +
      dist (gluingFinFermiPoint lam
          (gluingFinFermiInverse lam (gluingMirror y.1)).1
          (gluingFinFermiInverse lam (gluingMirror y.1)).2)
        (gluingFinFermiPoint lam v (ε * gluingCollarWarp r v)))
      (gluingFinFermiRadialCoord lam q.1) = 0 := by
  let t₀ := gluingFinFermiRadialCoord lam q.1
  have hqpoint :
      gluingFinFermiPoint lam t₀ (ε * gluingCollarWarp r t₀) = q.1 := by
    rw [← gluingFinFermiPoint_inverse_right hlam q.1]
    simp [t₀, gluingFinFermiInverse, hqseam]
  have hxpoint :
      gluingFinFermiPoint lam (gluingFinFermiInverse lam x.1).1
        (gluingFinFermiInverse lam x.1).2 = x.1 :=
    gluingFinFermiPoint_inverse_right hlam x.1
  have hypoint :
      gluingFinFermiPoint lam
        (gluingFinFermiInverse lam (gluingMirror y.1)).1
        (gluingFinFermiInverse lam (gluingMirror y.1)).2 = gluingMirror y.1 :=
    gluingFinFermiPoint_inverse_right hlam (gluingMirror y.1)
  have hneq₁ :
      gluingFinFermiPoint lam (gluingFinFermiInverse lam x.1).1
        (gluingFinFermiInverse lam x.1).2 ≠
      gluingFinFermiPoint lam t₀ (ε * gluingCollarWarp r t₀) := by
    rw [hxpoint, hqpoint]
    exact hxq
  have hneq₂ :
      gluingFinFermiPoint lam
        (gluingFinFermiInverse lam (gluingMirror y.1)).1
        (gluingFinFermiInverse lam (gluingMirror y.1)).2 ≠
      gluingFinFermiPoint lam t₀ (ε * gluingCollarWarp r t₀) := by
    rw [hypoint, hqpoint]
    exact hyq
  have hlocal := gluingCollarFiniteMetricGlue_seamGraph_isLocalMin
    hlam x y q hqrad hqseam hmin
  simpa only [t₀] using
    gluingFinFermiSeamGraph_distanceSum_stationary ht0 hneq₁ hneq₂ hlocal

/-- For interior cross-pair endpoints, choose one seam minimizer that is both
radially interior and stationary along every feasible fin geodesic. This
packages the exact minimizer data needed for the remaining boundary-angle
comparison. -/
theorem gluingCollarFiniteMetricGlue_cross_seam_first_variation_radially_interior
    {r R lam ε : ℝ} (hR : 0 < R) (hlam : 0 < lam) (hε : 0 ≤ ε)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R)
    (hxlo : -R < (gluingFinFermiInverse lam x.1).1)
    (hxhi : (gluingFinFermiInverse lam x.1).1 < R)
    (hylo : -R < (gluingFinFermiInverse lam (gluingMirror y.1)).1)
    (hyhi : (gluingFinFermiInverse lam (gluingMirror y.1)).1 < R) :
    ∃ q : gluingCollarFiniteUpperFin r R lam ε,
      (∀ w : gluingCollarFiniteUpperFin r R lam ε,
        0 ≤ geodInterpDistanceForwardDerivative q.1 w.1 x.1 +
          geodInterpDistanceForwardDerivative q.1 w.1 (gluingMirror y.1)) ∧
      (∀ w : gluingCollarFiniteUpperFin r R lam ε,
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
            dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
              dist (gluingMirror y.1)
                (Vendored.RiemannDynamics.geodInterp q.1 w.1 t)) ∧
      gluingFinFermiRadialCoord lam q.1 ∈ Ioo (-R) R ∧
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ∧
      (q.1 ∈ interior (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane) ∨
        ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
          gluingFinFermiTransverseCoord lam q.1) := by
  obtain ⟨q, hmin, hdecomp⟩ :=
    gluingCollarFiniteMetricGlue_cross_seam_geodesic_minimum
      (r := r) (R := R) (lam := lam) (ε := ε) hR.le hlam hconv x y
  have hmirror (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror w.1) = dist (gluingMirror y.1) w.1 := by
    calc
      dist y.1 (gluingMirror w.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror w.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror w.1)).symm
      _ = dist (gluingMirror y.1) w.1 := by rw [gluingMirror_involutive]
  have hcost (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) =
        dist x.1 w.1 + dist (gluingMirror y.1) w.1 := by
    simp only [gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight, Subtype.dist_eq]
    rw [hmirror w]
  have hcostmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε q) ≤
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε w) +
        dist y (gluingCollarFiniteMetricGlueRight r R lam ε w) := by
    intro w
    have h := hmin w 1 (by norm_num)
    rw [hcost q, hcost w]
    simpa [Vendored.RiemannDynamics.geodInterp_one] using h
  have hqhi := gluingCollarFiniteUpperFin_minimizer_ne_upper_radial_cap
    hR hlam hε x y q hcostmin hxhi hyhi
  have hqlo := gluingCollarFiniteLowerFin_minimizer_ne_lower_radial_cap
    hR hlam hε x y q hcostmin hxlo hylo
  rcases q.2 with ⟨⟨hqlo_le, hqhi_le⟩, _⟩
  have hqlo_lt : -R < gluingFinFermiRadialCoord lam q.1 := by
    rcases lt_or_eq_of_le hqlo_le with hlt | heq
    · exact hlt
    · exact (hqlo heq.symm).elim
  have hqhi_lt : gluingFinFermiRadialCoord lam q.1 < R := by
    rcases lt_or_eq_of_le hqhi_le with hlt | heq
    · exact hlt
    · exact (hqhi heq).elim
  have hinteriorOrSeam :
      q.1 ∈ interior (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane) ∨
        ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam q.1) =
          gluingFinFermiTransverseCoord lam q.1 := by
    rcases gluingCollarFiniteUpperFin_interior_or_boundary q with hi | hlo | hhi | hseam
    · exact Or.inl hi
    · exact False.elim ((ne_of_gt hqlo_lt) hlo)
    · exact False.elim ((ne_of_lt hqhi_lt) hhi)
    · exact Or.inr hseam
  refine ⟨q, ?_, ⟨hmin, ⟨⟨hqlo_lt, hqhi_lt⟩, ⟨hdecomp, hinteriorOrSeam⟩⟩⟩⟩
  intro w
  apply geodInterp_distance_forward_derivative_sum_nonneg_of_minimizing
  exact hmin w

/-- At an interior minimizing seam point, every initial direction is locally
admissible in the fin. The minimizing property therefore gives the summed
first-variation inequality toward an arbitrary point of the slab, not only
toward another point of the fin. -/
theorem gluingCollarFiniteMetricGlue_cross_seam_first_variation_of_interior
    {r R lam ε : ℝ}
    (x y z : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqInterior : q.1 ∈ interior
      (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane))
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t)) :
    0 ≤ geodInterpDistanceForwardDerivative q.1 z.1 x.1 +
      geodInterpDistanceForwardDerivative q.1 z.1 (gluingMirror y.1) := by
  let γ : ℝ → UpperHalfPlane := fun t =>
    Vendored.RiemannDynamics.geodInterp q.1 z.1 t
  have hγ : ContinuousAt γ 0 := by
    change ContinuousAt
      (fun t : ℝ => Vendored.RiemannDynamics.geodInterp q.1 z.1 t) 0
    exact (Vendored.RiemannDynamics.continuous_geodInterp.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))).continuousAt
  have hγ0 : γ 0 ∈ interior
      (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane) := by
    simpa [γ, Vendored.RiemannDynamics.geodInterp_zero] using hqInterior
  have hnear :=
    hγ.preimage_mem_nhds (isOpen_interior.mem_nhds hγ0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min 1 (ρ / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; exact min_le_left _ _
  have hδρ : δ < ρ := by
    dsimp [δ]
    exact (min_le_right _ _).trans_lt (by linarith)
  have hlocal : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
        dist x.1 (γ t) + dist (gluingMirror y.1) (γ t) := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) ρ := by
      have habs : |t - 0| = t := by rw [sub_zero, abs_of_nonneg ht.1]
      rw [Metric.mem_ball, Real.dist_eq, habs]
      exact ht.2.trans_lt hδρ
    have hinterior : γ t ∈ interior
        (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane) := hball htball
    let w : gluingCollarFiniteUpperFin r R lam ε := ⟨γ t, interior_subset hinterior⟩
    have hmin' := hmin w 1 (by norm_num)
    simpa [w, γ, Vendored.RiemannDynamics.geodInterp_one] using hmin'
  exact geodInterp_distance_forward_derivative_sum_nonneg_of_local_minimizing
    q.1 z.1 x.1 (gluingMirror y.1) δ hδ hδ1 hlocal

/-- Constant-speed interpolation remains in the closed radial slab, so the
induced slab metric has points at every fractional distance along a segment. -/
theorem exists_gluingFinFermiRadialWindow_interpolation {lam R : ℝ}
    (hlam : 0 < lam) (x y : gluingFinFermiRadialWindow lam R)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ z : gluingFinFermiRadialWindow lam R,
      dist x z = t * dist x y ∧ dist z y = (1 - t) * dist x y := by
  let q := Vendored.RiemannDynamics.geodInterp x.1 y.1 t
  have hq : q ∈ gluingFinFermiRadialWindow lam R :=
    gluingFinFermiRadialWindow_geodSeg_subset hlam x.2 y.2
      (Vendored.RiemannDynamics.geodInterp_mem_geodSeg x.1 y.1 ht)
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · change dist x.1 q = t * dist x.1 y.1
    exact Vendored.RiemannDynamics.dist_geodInterp_left x.1 y.1 ht
  · change dist q y.1 = (1 - t) * dist x.1 y.1
    rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs,
      abs_of_nonneg (by linarith [ht.2])]

/-- Points represented in the left slab copy have an exact midpoint in the
metric gluing, inherited from the convex hyperbolic radial window. -/
theorem gluingCollarFiniteMetricGlue_left_midpoint
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x) m =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      dist m
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 := by
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  obtain ⟨m, hxm, hmy, _⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun a ha b hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  refine ⟨L m, ?_, ?_⟩
  · simpa only [L, hLI.dist_eq] using hxm
  · simpa only [L, hLI.dist_eq] using hmy

/-- A midpoint of two points in the left slab copy satisfies the exact
hyperbolic midpoint-cosh identity against every third point in that same
copy. This is the within-piece comparison input for the finite gluing CAT
argument; it makes no claim yet for third points in the opposite copy. -/
theorem gluingCollarFiniteMetricGlue_left_midpoint_cosh
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y z : gluingFinFermiRadialWindow lam R) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x) m =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      dist m
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      2 * Real.cosh
          (dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2) *
          Real.cosh
            (dist
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) z) m) =
        Real.cosh
            (dist
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) z)
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)) +
          Real.cosh
            (dist
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) z)
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y)) := by
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  obtain ⟨m, hxm, hmy, hcosh⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun a ha b hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  refine ⟨L m, ?_, ?_, ?_⟩
  · simpa only [L, hLI.dist_eq] using hxm
  · simpa only [L, hLI.dist_eq] using hmy
  · simpa only [L, hLI.dist_eq] using hcosh z

/-- The right slab copy has the same exact midpoint-cosh comparison for any
third point represented in that copy. -/
theorem gluingCollarFiniteMetricGlue_right_midpoint_cosh
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y z : gluingFinFermiRadialWindow lam R) :
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (Rg x) m = dist (Rg x) (Rg y) / 2 ∧
      dist m (Rg y) = dist (Rg x) (Rg y) / 2 ∧
      2 * Real.cosh (dist (Rg x) (Rg y) / 2) *
          Real.cosh (dist (Rg z) m) =
        Real.cosh (dist (Rg z) (Rg x)) + Real.cosh (dist (Rg z) (Rg y)) := by
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨m, hxm, hmy, hcosh⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun a ha b hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  refine ⟨Rg m, ?_, ?_, ?_⟩
  · simpa only [Rg, hRI.dist_eq] using hxm
  · simpa only [Rg, hRI.dist_eq] using hmy
  · simpa only [Rg, hRI.dist_eq] using hcosh z

/-- The common fin is intrinsically convex in the glued space: its hyperbolic
midpoint-cosh identity holds against a test point represented on either side
of the quotient. This handles seam endpoints, not arbitrary slab endpoints. -/
theorem gluingCollarFiniteMetricGlue_commonFin_midpoint_cosh
    {r R lam ε : ℝ} [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (a b : gluingCollarFiniteUpperFin r R lam ε) :
    ∃ m : gluingCollarFiniteUpperFin r R lam ε,
      dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
      ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
        2 * Real.cosh
            (dist
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueLeft r R lam ε a))
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueLeft r R lam ε b)) / 2) *
            Real.cosh
              (dist z
                (Metric.toGlueL
                  (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueLeft r R lam ε m))) =
          Real.cosh
              (dist z
                (Metric.toGlueL
                  (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueLeft r R lam ε a))) +
            Real.cosh
              (dist z
                (Metric.toGlueL
                  (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueLeft r R lam ε b))) := by
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Q := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨m, ham, hmb, _⟩ := exists_subtype_hyperbolic_midpoint_cosh
    hconv a b
  refine ⟨m, ham, hmb, ?_⟩
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  cases p with
  | inl x =>
      have ham' : dist a.1 m.1 = dist a.1 b.1 / 2 := by
        simpa only [Subtype.dist_eq] using ham
      have hmb' : dist m.1 b.1 = dist a.1 b.1 / 2 := by
        simpa only [Subtype.dist_eq] using hmb
      have h := hyperbolic_midpoint_cosh ham' hmb' x.1
      change 2 * Real.cosh (dist (L (I a)) (L (I b)) / 2) *
          Real.cosh (dist (L x) (L (I m))) =
        Real.cosh (dist (L x) (L (I a))) + Real.cosh (dist (L x) (L (I b)))
      rw [hLI.dist_eq (I a) (I b), hLI.dist_eq x (I m),
        hLI.dist_eq x (I a), hLI.dist_eq x (I b)]
      simpa [I, gluingCollarFiniteMetricGlueLeft, Subtype.dist_eq] using h
  | inr y =>
      have ham' : dist (gluingMirror a.1) (gluingMirror m.1) =
          dist (gluingMirror a.1) (gluingMirror b.1) / 2 := by
        rw [gluingMirror_isometry.dist_eq, gluingMirror_isometry.dist_eq]
        simpa only [Subtype.dist_eq] using ham
      have hmb' : dist (gluingMirror m.1) (gluingMirror b.1) =
          dist (gluingMirror a.1) (gluingMirror b.1) / 2 := by
        rw [gluingMirror_isometry.dist_eq, gluingMirror_isometry.dist_eq]
        simpa only [Subtype.dist_eq] using hmb
      have h := hyperbolic_midpoint_cosh ham' hmb' y.1
      have hcommA := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) a
      have hcommB := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) b
      have hcommM := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) m
      change L (I a) = Q (J a) at hcommA
      change L (I b) = Q (J b) at hcommB
      change L (I m) = Q (J m) at hcommM
      change 2 * Real.cosh (dist (L (I a)) (L (I b)) / 2) *
          Real.cosh (dist (Q y) (L (I m))) =
        Real.cosh (dist (Q y) (L (I a))) + Real.cosh (dist (Q y) (L (I b)))
      rw [hcommA, hcommB, hcommM]
      rw [hRI.dist_eq (J a) (J b), hRI.dist_eq y (J m),
        hRI.dist_eq y (J a), hRI.dist_eq y (J b)]
      simpa [J, gluingCollarFiniteMetricGlueRight, Subtype.dist_eq] using h

/-- Points represented in the right slab copy have an exact midpoint in the
metric gluing, inherited from the convex hyperbolic radial window. -/
theorem gluingCollarFiniteMetricGlue_right_midpoint
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x) m =
        dist
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      dist m
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 := by
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨m, hxm, hmy, _⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun a ha b hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  refine ⟨Rg m, ?_, ?_⟩
  · simpa only [Rg, hRI.dist_eq] using hxm
  · simpa only [Rg, hRI.dist_eq] using hmy

/-- Every pair of points in opposite slab copies has an exact metric
midpoint in the two-piece gluing. The cross-distance minimizer supplies the
seam point; constant-speed hyperbolic interpolation supplies the midpoint on
whichever segment contains the half-length location. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x) m =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      dist m
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      ∃ z : gluingCollarFiniteUpperFin r R lam ε,
        dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueLeft r R lam ε z)) +
          dist
            (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y)
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueLeft r R lam ε z)) =
          dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
            (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) ∧
        dist m
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueLeft r R lam ε z)) =
          |dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) -
            dist y (gluingCollarFiniteMetricGlueRight r R lam ε z)| / 2 := by
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨z, hdist⟩ := gluingCollarFiniteMetricGlue_cross_dist_attained
    (r := r) (R := R) (lam := lam) (ε := ε) hR hlam x y
  let u := gluingCollarFiniteMetricGlueLeft r R lam ε z
  let v := gluingCollarFiniteMetricGlueRight r R lam ε z
  have huv : L u = Rg v :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) z
  let d : ℝ := dist (L x) (Rg y)
  let a : ℝ := dist x u
  let b : ℝ := dist y v
  have hd : d = a + b := by
    simpa [d, a, b, u, v] using hdist
  have hseam : dist (L x) (L u) + dist (Rg y) (L u) = d := by
    calc
      dist (L x) (L u) + dist (Rg y) (L u) = dist x u + dist y v := by
        rw [hLI.dist_eq, dist_comm (Rg y) (L u), huv, hRI.dist_eq,
          dist_comm v y]
      _ = d := by simpa [a, b] using hd.symm
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hd_nonneg : 0 ≤ d := by rw [hd]; positivity
  by_cases hdpos : 0 < d
  · by_cases hba : b ≤ a
    · have ha_pos : 0 < a := by rw [hd] at hdpos; nlinarith
      let t : ℝ := d / (2 * a)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [t]; positivity
        · dsimp [t]
          have : d ≤ 2 * a := by rw [hd]; nlinarith
          exact (div_le_one (by positivity)).2 this
      obtain ⟨p, hxp, hpu⟩ :=
        exists_gluingFinFermiRadialWindow_interpolation hlam x u t ht
      have hmul : t * a = d / 2 := by
        dsimp [t]
        field_simp
      have hleft : dist (L x) (L p) = d / 2 := by
        rw [hLI.dist_eq, hxp, hmul]
      have hright_le : dist (L p) (Rg y) ≤ d / 2 := by
        calc
          dist (L p) (Rg y) ≤ dist (L p) (Rg v) + dist (Rg v) (Rg y) :=
            dist_triangle _ _ _
          _ = (1 - t) * a + b := by
            have hpz : dist (L p) (Rg v) = dist p u := by
              rw [← huv]
              exact hLI.dist_eq p u
            have hzy : dist (Rg v) (Rg y) = dist v y := hRI.dist_eq v y
            rw [hpz, hzy, dist_comm v y, hpu]
          _ = d / 2 := by nlinarith [hd, hmul]
      have hright_lower : d / 2 ≤ dist (L p) (Rg y) := by
        have htri := dist_triangle (L x) (L p) (Rg y)
        rw [hleft] at htri
        linarith [show dist (L x) (Rg y) = d from rfl]
      have hpm : dist (L p) (L u) = |a - b| / 2 := by
        rw [hLI.dist_eq, hpu]
        rw [abs_of_nonneg (sub_nonneg.mpr hba)]
        nlinarith [hd, hmul]
      exact ⟨L p, hleft, le_antisymm hright_le hright_lower,
        z, by simpa [d, u] using hseam,
        by simpa [u, a, b] using hpm⟩
    · have hab : a ≤ b := le_of_not_ge hba
      have hb_pos : 0 < b := by rw [hd] at hdpos; nlinarith
      let t : ℝ := d / (2 * b)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [t]; positivity
        · dsimp [t]
          have : d ≤ 2 * b := by rw [hd]; nlinarith
          exact (div_le_one (by positivity)).2 this
      obtain ⟨p, hyp, hpv⟩ :=
        exists_gluingFinFermiRadialWindow_interpolation hlam y v t ht
      have hmul : t * b = d / 2 := by
        dsimp [t]
        field_simp
      have hright : dist (Rg p) (Rg y) = d / 2 := by
        rw [hRI.dist_eq, dist_comm, hyp, hmul]
      have hleft_le : dist (L x) (Rg p) ≤ d / 2 := by
        calc
          dist (L x) (Rg p) ≤ dist (L x) (L u) + dist (L u) (Rg p) :=
            dist_triangle _ _ _
          _ = a + (1 - t) * b := by
            have hxu : dist (L x) (L u) = a := by
              simpa [a] using hLI.dist_eq x u
            have hzp : dist (L u) (Rg p) = dist v p := by
              rw [huv]
              exact hRI.dist_eq v p
            rw [hxu, hzp, dist_comm v p, hpv]
          _ = d / 2 := by nlinarith [hd, hmul]
      have hleft_lower : d / 2 ≤ dist (L x) (Rg p) := by
        have htri := dist_triangle (L x) (Rg p) (Rg y)
        rw [hright] at htri
        linarith [show dist (L x) (Rg y) = d from rfl]
      have hpm : dist (Rg p) (L u) = |a - b| / 2 := by
        rw [huv, hRI.dist_eq, hpv, abs_of_nonpos (sub_nonpos.mpr hab)]
        nlinarith [hd, hmul]
      exact ⟨Rg p, le_antisymm hleft_le hleft_lower, hright,
        z, by simpa [d, u] using hseam,
        by simpa [u, a, b] using hpm⟩
  · have hdzero : d = 0 := le_antisymm (le_of_not_gt hdpos) hd_nonneg
    have hxy : L x = Rg y := dist_eq_zero.mp hdzero
    have hzero : dist (L x) (Rg y) = 0 := by rw [hxy]; simp
    have ha0 : a = 0 := by rw [hd] at hdzero; nlinarith
    have hb0 : b = 0 := by rw [hd] at hdzero; nlinarith
    have hpm : dist (L x) (L u) = |a - b| / 2 := by
      rw [hLI.dist_eq]
      simp [u, a, b, ha0, hb0]
    refine ⟨L x, ?_⟩
    constructor
    · change dist (L x) (L x) = dist (L x) (Rg y) / 2
      rw [dist_self, hzero]
      norm_num
    constructor
    · change dist (L x) (Rg y) = dist (L x) (Rg y) / 2
      rw [hzero]
      norm_num
    refine ⟨z, ?_⟩
    constructor
    · simpa [d, u] using hseam
    · simpa [u, a, b] using hpm

/-- Construct a midpoint using a specified minimizing seam point. The third
component records its distance back to that seam, so the seam-test cosh
identity applies to this very minimizer rather than to another attainment
witness. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_of_seam
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hdecomp :
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε q)) :
    let I := gluingCollarFiniteMetricGlueLeft r R lam ε
    let J := gluingCollarFiniteMetricGlueRight r R lam ε
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Rg y) / 2 ∧
      (dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
        dist m (L (I q)) =
          |dist x (I q) - dist y (J q)| / 2) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  have huv : L (I q) = Rg (J q) :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  change L (I q) = Rg (J q) at huv
  let d := dist (L x) (Rg y)
  let a := dist x (I q)
  let b := dist y (J q)
  have hd : d = a + b := by simpa [d, a, b, I, J] using hdecomp
  have hxu : dist (L x) (L (I q)) = a := hLI.dist_eq x (I q)
  have huy : dist (L (I q)) (Rg y) = b := by
    calc
      dist (L (I q)) (Rg y) = dist (Rg (J q)) (Rg y) := by rw [huv]
      _ = dist (J q) y := hRI.dist_eq (J q) y
      _ = b := dist_comm _ _
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hd_nonneg : 0 ≤ d := by rw [hd]; positivity
  by_cases hdpos : 0 < d
  · by_cases hba : b ≤ a
    · have ha_pos : 0 < a := by rw [hd] at hdpos; nlinarith
      let t : ℝ := d / (2 * a)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [t]; positivity
        · dsimp [t]
          have hle : d ≤ 2 * a := by rw [hd]; nlinarith
          exact (div_le_one (by positivity)).2 hle
      obtain ⟨p, hxp, hpu⟩ :=
        exists_gluingFinFermiRadialWindow_interpolation hlam x (I q) t ht
      have hmul : t * a = d / 2 := by dsimp [t]; field_simp
      let m := L p
      have hxm : dist (L x) m = d / 2 := by
        change dist (L x) (L p) = d / 2
        rw [hLI.dist_eq, hxp, hmul]
      have hmy_le : dist m (Rg y) ≤ d / 2 := by
        calc
          dist m (Rg y) ≤ dist m (L (I q)) + dist (L (I q)) (Rg y) :=
            dist_triangle _ _ _
          _ = (1 - t) * a + b := by
            rw [hLI.dist_eq, hpu, huy]
          _ = d / 2 := by nlinarith [hd, hmul]
      have hmy_ge : d / 2 ≤ dist m (Rg y) := by
        have htri := dist_triangle (L x) m (Rg y)
        rw [hxm] at htri
        linarith [show dist (L x) (Rg y) = d from rfl]
      have hmq : dist m (L (I q)) = |a - b| / 2 := by
        change dist (L p) (L (I q)) = _
        rw [hLI.dist_eq, hpu, abs_of_nonneg (sub_nonneg.mpr hba)]
        nlinarith [hd, hmul]
      exact ⟨m, hxm, le_antisymm hmy_le hmy_ge, by simpa [a, b, I, J] using hmq⟩
    · have hab : a ≤ b := le_of_not_ge hba
      have hb_pos : 0 < b := by rw [hd] at hdpos; nlinarith
      let t : ℝ := d / (2 * b)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [t]; positivity
        · dsimp [t]
          have hle : d ≤ 2 * b := by rw [hd]; nlinarith
          exact (div_le_one (by positivity)).2 hle
      obtain ⟨p, hyp, hpv⟩ :=
        exists_gluingFinFermiRadialWindow_interpolation hlam y (J q) t ht
      have hmul : t * b = d / 2 := by dsimp [t]; field_simp
      let m := Rg p
      have hmy : dist m (Rg y) = d / 2 := by
        change dist (Rg p) (Rg y) = d / 2
        rw [hRI.dist_eq, dist_comm, hyp, hmul]
      have hxm_le : dist (L x) m ≤ d / 2 := by
        calc
          dist (L x) m ≤ dist (L x) (L (I q)) + dist (L (I q)) m :=
            dist_triangle _ _ _
          _ = a + (1 - t) * b := by
            have hzp : dist (L (I q)) (Rg p) = dist (J q) p := by
              rw [huv]
              exact hRI.dist_eq (J q) p
            rw [hxu, hzp, dist_comm (J q) p, hpv]
          _ = d / 2 := by nlinarith [hd, hmul]
      have hxm_ge : d / 2 ≤ dist (L x) m := by
        have htri := dist_triangle (L x) m (Rg y)
        rw [hmy] at htri
        linarith [show dist (L x) (Rg y) = d from rfl]
      have hmq : dist m (L (I q)) = |a - b| / 2 := by
        change dist (Rg p) (L (I q)) = _
        rw [huv, hRI.dist_eq, hpv,
          abs_of_nonpos (sub_nonpos.mpr hab)]
        nlinarith [hd, hmul]
      exact ⟨m, le_antisymm hxm_le hxm_ge, hmy,
        by simpa [a, b, I, J] using hmq⟩
  · have hdzero : d = 0 := le_antisymm (le_of_not_gt hdpos) hd_nonneg
    have ha0 : a = 0 := by rw [hd] at hdzero; nlinarith
    have hb0 : b = 0 := by rw [hd] at hdzero; nlinarith
    have hxy : L x = Rg y := dist_eq_zero.mp hdzero
    have hzero : dist (L x) (Rg y) = 0 := by rw [hxy]; simp
    have hmq : dist (L x) (L (I q)) = |a - b| / 2 := by
      rw [hxu]
      simp [ha0, hb0]
    refine ⟨L x, ?_, ?_, ?_⟩
    · change dist (L x) (L x) = dist (L x) (Rg y) / 2
      rw [dist_self, hzero]
      norm_num
    · change dist (L x) (Rg y) = dist (L x) (Rg y) / 2
      rw [hzero]
      norm_num
    · simpa [a, b, I, J] using hmq

private theorem cosh_sum_difference_half_identity (a b : ℝ) :
    2 * Real.cosh ((a + b) / 2) * Real.cosh (|a - b| / 2) =
      Real.cosh a + Real.cosh b := by
  let p : ℝ := (a + b) / 2
  let q : ℝ := (a - b) / 2
  have habs : |a - b| / 2 = |(a - b) / 2| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ha : a = p + q := by dsimp [p, q]; ring
  have hb : b = p - q := by dsimp [p, q]; ring
  calc
    2 * Real.cosh ((a + b) / 2) * Real.cosh (|a - b| / 2) =
        2 * Real.cosh p * Real.cosh q := by
      dsimp [p, q]
      rw [habs, Real.cosh_abs]
    _ = Real.cosh (p + q) + Real.cosh (p - q) := by
      rw [Real.cosh_add]
      rw [show p - q = p + -q by ring, Real.cosh_add,
        Real.cosh_neg, Real.sinh_neg]
      ring
    _ = Real.cosh a + Real.cosh b := by rw [← ha, ← hb]

/-- A specified seam minimizer is a valid test point for the midpoint
comparison: the midpoint is constructed along that same seam route and the
cosh identity follows from the sum/difference identity. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_at_given_seam
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hdecomp :
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
          dist y (gluingCollarFiniteMetricGlueRight r R lam ε q)) :
    let I := gluingCollarFiniteMetricGlueLeft r R lam ε
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Rg y) / 2 ∧
      (dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
        2 * Real.cosh (dist (L x) (Rg y) / 2) *
            Real.cosh (dist (L (I q)) m) =
          Real.cosh (dist (L (I q)) (L x)) +
            Real.cosh (dist (L (I q)) (Rg y))) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨m, hxm, hmy, hmq⟩ :=
    gluingCollarFiniteMetricGlue_cross_midpoint_of_seam
      (r := r) (R := R) (lam := lam) (ε := ε) hlam x y q hdecomp
  let a := dist x (I q)
  let b := dist y (J q)
  have hd : dist (L x) (Rg y) = a + b := by
    simpa [a, b, I, J] using hdecomp
  have htestx : dist (L (I q)) (L x) = a := by
    rw [hLI.dist_eq, dist_comm]
  have htesty : dist (L (I q)) (Rg y) = b := by
    rw [gluingCollarFiniteMetricGlue_seam_left_cross_dist_eq]
    dsimp [b, J, gluingCollarFiniteMetricGlueRight]
    calc
      dist q.1 (gluingMirror y.1) = dist (gluingMirror y.1) q.1 := dist_comm _ _
      _ = dist y.1 (gluingMirror q.1) := by
        calc
          dist (gluingMirror y.1) q.1 =
              dist (gluingMirror y.1) (gluingMirror (gluingMirror q.1)) := by
                rw [gluingMirror_involutive]
          _ = dist y.1 (gluingMirror q.1) :=
            gluingMirror_isometry.dist_eq y.1 (gluingMirror q.1)
  have hcosh := cosh_sum_difference_half_identity a b
  rw [← hd] at hcosh
  refine ⟨m, hxm, hmy, ?_⟩
  rw [dist_comm (L (I q)) m, hmq, htestx, htesty]
  exact hcosh

/-- In an opposite-copy pair, the minimizing seam point and the constructed
midpoint satisfy the exact hyperbolic cosh identity when tested at that seam
point. The equality uses the attained decomposition of cross-distance into
the two seam legs; it is a seam case of the comparison still needed for the
full CAT gluing theorem. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_at_seam
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      ∃ z : gluingCollarFiniteUpperFin r R lam ε,
        dist (L x) m = dist (L x) (Rg y) / 2 ∧
        dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
        dist (L x) (Rg y) =
          dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
            dist y (gluingCollarFiniteMetricGlueRight r R lam ε z) ∧
        2 * Real.cosh
            ((dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z) +
              dist y (gluingCollarFiniteMetricGlueRight r R lam ε z)) / 2) *
          Real.cosh
            (dist m (L (gluingCollarFiniteMetricGlueLeft r R lam ε z))) =
          Real.cosh (dist x (gluingCollarFiniteMetricGlueLeft r R lam ε z)) +
            Real.cosh (dist y (gluingCollarFiniteMetricGlueRight r R lam ε z)) := by
  dsimp
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨m, hxm, hmy, z, hseam, hzm⟩ :=
    gluingCollarFiniteMetricGlue_cross_midpoint
      (r := r) (R := R) (lam := lam) (ε := ε) hR hlam x y
  let u := gluingCollarFiniteMetricGlueLeft r R lam ε z
  let v := gluingCollarFiniteMetricGlueRight r R lam ε z
  have huv : L u = Rg v :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) z
  have hx : dist (L x) (L u) = dist x u := hLI.dist_eq x u
  have hy : dist (Rg y) (L u) = dist y v := by
    calc
      dist (Rg y) (L u) = dist (Rg y) (Rg v) := by rw [huv]
      _ = dist y v := hRI.dist_eq y v
  have htotal : dist (L x) (Rg y) = dist x u + dist y v := by
    calc
      dist (L x) (Rg y) = dist (L x) (L u) + dist (Rg y) (L u) := hseam.symm
      _ = dist x u + dist y v := by rw [hx, hy]
  have hzm' : dist m (L u) = |dist x u - dist y v| / 2 := by
    simpa [u, v] using hzm
  refine ⟨m, z, hxm, hmy, ?_, ?_⟩
  · simpa [u, v] using htotal
  · rw [hzm']
    exact cosh_sum_difference_half_identity (dist x u) (dist y v)

/-- Opposite-copy midpoint comparison against a common-fin test point when
the left leg is at least as long as the right leg. It consumes the first-
variation inequality and exact distance decomposition supplied together by
the attained seam-minimum bridge; it also records the midpoint's quotient
representative so its distances descend through the gluing. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_longer_seam_test
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (q z : gluingCollarFiniteUpperFin r R lam ε)
    (hvariation : 0 ≤
      geodInterpDistanceForwardDerivative q.1 z.1 x.1 +
        geodInterpDistanceForwardDerivative q.1 z.1 (gluingMirror y.1))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hqx : q.1 ≠ x.1) (hqy : q.1 ≠ gluingMirror y.1)
    (hqz : q.1 ≠ z.1)
    (hba : dist (gluingMirror y.1) q.1 ≤ dist x.1 q.1) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x) m =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      (dist m
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
        dist
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
          (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2 ∧
      2 * Real.cosh
          (dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
            (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2) *
        Real.cosh
          (dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueLeft r R lam ε z)) m) ≤
      Real.cosh
          (dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueLeft r R lam ε z))
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)) +
        Real.cosh
          (dist
            (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueLeft r R lam ε z))
            (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y))) := by
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Q := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let u := I q
  let v := J q
  let a : ℝ := dist x u
  let b : ℝ := dist y v
  let d : ℝ := dist (L x) (Q y)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  have hcommq := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hcommz := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) z
  change L u = Q v at hcommq
  change L (I z) = Q (J z) at hcommz
  have hmirror (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror w.1) = dist (gluingMirror y.1) w.1 := by
    calc
      dist y.1 (gluingMirror w.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror w.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror w.1)).symm
      _ = dist (gluingMirror y.1) w.1 := by rw [gluingMirror_involutive]
  have hcostq : dist x u + dist y v = dist x.1 q.1 +
      dist (gluingMirror y.1) q.1 := by
    dsimp [u, v, I, J, gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight]
    rw [Subtype.dist_eq, Subtype.dist_eq, hmirror q]
  have ha_eq : a = dist q.1 x.1 := by
    change dist x.1 q.1 = dist q.1 x.1
    exact dist_comm _ _
  have hb_eq : b = dist q.1 (gluingMirror y.1) := by
    change dist y.1 (gluingMirror q.1) = dist q.1 (gluingMirror y.1)
    calc
      dist y.1 (gluingMirror q.1) =
          dist (gluingMirror y.1) q.1 := hmirror q
      _ = dist q.1 (gluingMirror y.1) := dist_comm _ _
  have hsum : a + b = dist q.1 x.1 +
      dist q.1 (gluingMirror y.1) := by rw [ha_eq, hb_eq]
  have hd : d = a + b := by
    dsimp [d, a, b]
    rw [hdecomp, hcostq]
  have hba' : dist q.1 (gluingMirror y.1) ≤ dist q.1 x.1 := by
    simpa only [dist_comm] using hba
  obtain ⟨m', hprops⟩ := exists_hyperbolic_broken_geodesic_midpoint_cosh_le
    q.1 x.1 (gluingMirror y.1) z.1 hqx hqy hqz hba' hvariation
  have hmseg : m' ∈ Vendored.RiemannDynamics.geodSeg x.1 q.1 := hprops.1
  have hxm' : dist x.1 m' =
      (dist q.1 x.1 + dist q.1 (gluingMirror y.1)) / 2 := hprops.2.1
  have hmq' : dist m' q.1 =
      (dist q.1 x.1 - dist q.1 (gluingMirror y.1)) / 2 := hprops.2.2.1
  have hcosh' :
      2 * Real.cosh
          ((dist q.1 x.1 + dist q.1 (gluingMirror y.1)) / 2) *
        Real.cosh (dist z.1 m') ≤
      Real.cosh (dist z.1 x.1) +
        Real.cosh (dist z.1 (gluingMirror y.1)) := hprops.2.2.2
  have hmwin : m' ∈ gluingFinFermiRadialWindow lam R :=
    gluingFinFermiRadialWindow_geodSeg_subset hlam x.2 q.2.1 hmseg
  let p : gluingFinFermiRadialWindow lam R := ⟨m', hmwin⟩
  let m := L p
  have hxm : dist (L x) m = d / 2 := by
    change dist (L x) (L p) = d / 2
    rw [hLI.dist_eq]
    change dist x.1 m' = d / 2
    rw [hd, hsum]
    exact hxm'
  have hmq : dist m (L u) = (a - b) / 2 := by
    change dist (L p) (L u) = (a - b) / 2
    rw [hLI.dist_eq]
    change dist m' q.1 = (a - b) / 2
    rw [ha_eq, hb_eq]
    exact hmq'
  have huy : dist (L u) (Q y) = b := by
    calc
      dist (L u) (Q y) = dist (Q v) (Q y) := by rw [hcommq]
      _ = dist v y := hRI.dist_eq v y
      _ = dist y v := dist_comm _ _
      _ = b := rfl
  have hmy_le : dist m (Q y) ≤ d / 2 := by
    calc
      dist m (Q y) ≤ dist m (L u) + dist (L u) (Q y) := dist_triangle _ _ _
      _ = (a - b) / 2 + b := by rw [hmq, huy]
      _ = d / 2 := by rw [hd]; dsimp [a, b]; ring
  have hmy_ge : d / 2 ≤ dist m (Q y) := by
    have htri := dist_triangle (L x) m (Q y)
    rw [hxm] at htri
    dsimp [d] at htri
    linarith
  have htestx : dist (L (I z)) (L x) = dist z.1 x.1 := by
    rw [hLI.dist_eq]
    rfl
  have htesty : dist (L (I z)) (Q y) = dist z.1 (gluingMirror y.1) :=
    gluingCollarFiniteMetricGlue_seam_left_cross_dist_eq z y
  have htestm : dist (L (I z)) m = dist z.1 m' := by
    change dist (L (I z)) (L p) = dist z.1 m'
    rw [hLI.dist_eq]
    rfl
  have hcomparison :
      2 * Real.cosh (d / 2) * Real.cosh (dist (L (I z)) m) ≤
        Real.cosh (dist (L (I z)) (L x)) +
          Real.cosh (dist (L (I z)) (Q y)) := by
    rw [htestm, htestx, htesty, hd]
    have hcosh'' := hcosh'
    rw [← hsum] at hcosh''
    exact hcosh''
  refine ⟨m, ?_, ?_, ?_⟩
  · exact hxm
  · exact le_antisymm hmy_le hmy_ge
  · exact hcomparison

/-- Reflected opposite-copy midpoint comparison against a common-fin test
point when the right leg is at least as long as the left. Reflection places
the midpoint in the right copy, where its distance to the seam test point is
the corresponding unfolded hyperbolic distance. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_longer_seam_test
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (q z : gluingCollarFiniteUpperFin r R lam ε)
    (hvariation : 0 ≤
      geodInterpDistanceForwardDerivative q.1 z.1 x.1 +
        geodInterpDistanceForwardDerivative q.1 z.1 (gluingMirror y.1))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hqx : q.1 ≠ x.1) (hqy : q.1 ≠ gluingMirror y.1)
    (hqz : q.1 ≠ z.1)
    (hba : dist q.1 x.1 ≤ dist (gluingMirror y.1) q.1) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Q := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Q y) / 2 ∧
      (dist m (Q y) = dist (L x) (Q y) / 2 ∧
        2 * Real.cosh (dist (L x) (Q y) / 2) *
            Real.cosh (dist (L (gluingCollarFiniteMetricGlueLeft r R lam ε z)) m) ≤
          Real.cosh (dist (L (gluingCollarFiniteMetricGlueLeft r R lam ε z)) (L x)) +
            Real.cosh (dist (L (gluingCollarFiniteMetricGlueLeft r R lam ε z)) (Q y))) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Q := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  have hcommq := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hcommz := congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) z
  change L (I q) = Q (J q) at hcommq
  change L (I z) = Q (J z) at hcommz
  have hmirror (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror w.1) = dist (gluingMirror y.1) w.1 := by
    calc
      dist y.1 (gluingMirror w.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror w.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror w.1)).symm
      _ = dist (gluingMirror y.1) w.1 := by rw [gluingMirror_involutive]
  have hvar' : 0 ≤
      geodInterpDistanceForwardDerivative q.1 z.1 (gluingMirror y.1) +
        geodInterpDistanceForwardDerivative q.1 z.1 x.1 := by
    linarith [hvariation]
  have hba' : dist q.1 x.1 ≤ dist q.1 (gluingMirror y.1) := by
    simpa only [dist_comm] using hba
  obtain ⟨m', hmseg, hprops⟩ :=
    exists_hyperbolic_broken_geodesic_midpoint_cosh_le
      q.1 (gluingMirror y.1) x.1 z.1 hqy hqx hqz hba' hvar'
  have hmy' : dist (gluingMirror y.1) m' =
      (dist q.1 (gluingMirror y.1) + dist q.1 x.1) / 2 := hprops.1
  have hmq' : dist m' q.1 =
      (dist q.1 (gluingMirror y.1) - dist q.1 x.1) / 2 := hprops.2.1
  have hcosh' :
      2 * Real.cosh
          ((dist q.1 (gluingMirror y.1) + dist q.1 x.1) / 2) *
        Real.cosh (dist z.1 m') ≤
      Real.cosh (dist z.1 (gluingMirror y.1)) + Real.cosh (dist z.1 x.1) :=
    hprops.2.2
  have hmwin' : m' ∈ gluingFinFermiRadialWindow lam R :=
    gluingFinFermiRadialWindow_geodSeg_subset hlam
      (by
        change gluingFinFermiRadialCoord lam (gluingMirror y.1) ∈ Icc (-R) R
        rw [gluingFinFermiRadialCoord_mirror]
        exact y.2)
      q.2.1 hmseg
  have hmwin : gluingMirror m' ∈ gluingFinFermiRadialWindow lam R := by
    change gluingFinFermiRadialCoord lam (gluingMirror m') ∈ Icc (-R) R
    rw [gluingFinFermiRadialCoord_mirror]
    exact hmwin'
  let p : gluingFinFermiRadialWindow lam R := ⟨gluingMirror m', hmwin⟩
  let m := Q p
  have hsum : dist (L x) (Q y) =
      dist q.1 (gluingMirror y.1) + dist q.1 x.1 := by
    calc
      dist (L x) (Q y) = dist x.1 q.1 + dist (gluingMirror y.1) q.1 := hdecomp
      _ = dist q.1 (gluingMirror y.1) + dist q.1 x.1 := by
        rw [dist_comm x.1 q.1, dist_comm (gluingMirror y.1) q.1]
        ring
  have hmy : dist m (Q y) = dist (L x) (Q y) / 2 := by
    change dist (Q p) (Q y) = dist (L x) (Q y) / 2
    rw [hRI.dist_eq]
    calc
      dist p y = dist (gluingMirror p) (gluingMirror y.1) :=
        (gluingMirror_isometry.dist_eq p.1 y.1).symm
      _ = dist m' (gluingMirror y.1) := by simp [p, gluingMirror_involutive]
      _ = (dist q.1 (gluingMirror y.1) + dist q.1 x.1) / 2 := by
        rw [dist_comm]
        exact hmy'
      _ = dist (L x) (Q y) / 2 := by rw [hsum]
  have hmpq : dist m (Q (J q)) = (dist q.1 (gluingMirror y.1) -
      dist q.1 x.1) / 2 := by
    change dist (Q p) (Q (J q)) = _
    rw [hRI.dist_eq]
    calc
      dist p (J q) = dist (gluingMirror p.1) (gluingMirror (J q).1) :=
        (gluingMirror_isometry.dist_eq p.1 (J q).1).symm
      _ = dist m' q.1 := by simp [p, J, gluingCollarFiniteMetricGlueRight,
        gluingMirror_involutive]
      _ = _ := hmq'
  have hseamd : dist p (J q) = dist m (Q (J q)) := by
    calc
      dist p (J q) = dist (gluingMirror p.1) (gluingMirror (J q).1) :=
        (gluingMirror_isometry.dist_eq p.1 (J q).1).symm
      _ = dist m' q.1 := by simp [p, J, gluingCollarFiniteMetricGlueRight,
        gluingMirror_involutive]
      _ = (dist q.1 (gluingMirror y.1) - dist q.1 x.1) / 2 := hmq'
      _ = dist m (Q (J q)) := hmpq.symm
  have hmx_le : dist (L x) m ≤ dist (L x) (Q y) / 2 := by
    calc
      dist (L x) m ≤ dist (L x) (L (I q)) + dist (L (I q)) m :=
        dist_triangle _ _ _
      _ = dist x.1 q.1 + dist m (Q (J q)) := by
        rw [hLI.dist_eq, hcommq, hRI.dist_eq]
        rw [Subtype.dist_eq, dist_comm (J q) p, hseamd]
        rfl
      _ = dist (L x) (Q y) / 2 := by
        rw [dist_comm x.1 q.1, hmpq, hsum]
        ring
  have hmx_ge : dist (L x) (Q y) / 2 ≤ dist (L x) m := by
    have htri := dist_triangle (L x) m (Q y)
    rw [hmy] at htri
    linarith
  have htestx : dist (L (I z)) (L x) = dist z.1 x.1 := by
    rw [hLI.dist_eq]
    rfl
  have htesty : dist (L (I z)) (Q y) = dist z.1 (gluingMirror y.1) :=
    gluingCollarFiniteMetricGlue_seam_left_cross_dist_eq z y
  have htestm : dist (L (I z)) m = dist z.1 m' := by
    change dist (L (I z)) (Q p) = dist z.1 m'
    rw [gluingCollarFiniteMetricGlue_seam_left_cross_dist_eq]
    simp [p, gluingMirror_involutive]
  have hcomparison :
      2 * Real.cosh (dist (L x) (Q y) / 2) *
          Real.cosh (dist (L (I z)) m) ≤
        Real.cosh (dist (L (I z)) (L x)) +
          Real.cosh (dist (L (I z)) (Q y)) := by
    rw [htestm, htestx, htesty]
    have hcosh'' := hcosh'
    rw [← hsum] at hcosh''
    simpa only [add_comm] using hcosh''
  exact ⟨m, le_antisymm hmx_le hmx_ge, hmy, hcomparison⟩

/-- For a fixed nondegenerate seam minimizer, the two longer-leg arguments
combine into one comparison theorem against every common-fin test point. The
first-variation and distance-decomposition inputs are the paired outputs of
`gluingCollarFiniteMetricGlue_cross_seam_first_variation`. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_commonFin_test
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (q z : gluingCollarFiniteUpperFin r R lam ε)
    (hvariation : 0 ≤
      geodInterpDistanceForwardDerivative q.1 z.1 x.1 +
        geodInterpDistanceForwardDerivative q.1 z.1 (gluingMirror y.1))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hqx : q.1 ≠ x.1) (hqy : q.1 ≠ gluingMirror y.1)
    (hqz : q.1 ≠ z.1) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Q := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Q y) / 2 ∧
      (dist m (Q y) = dist (L x) (Q y) / 2 ∧
        2 * Real.cosh (dist (L x) (Q y) / 2) *
            Real.cosh (dist (L (gluingCollarFiniteMetricGlueLeft r R lam ε z)) m) ≤
          Real.cosh (dist (L (gluingCollarFiniteMetricGlueLeft r R lam ε z)) (L x)) +
            Real.cosh (dist (L (gluingCollarFiniteMetricGlueLeft r R lam ε z)) (Q y))) := by
  dsimp
  by_cases hleft : dist (gluingMirror y.1) q.1 ≤ dist x.1 q.1
  · exact gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_longer_seam_test
      (r := r) (R := R) (lam := lam) (ε := ε) hlam x y q z hvariation hdecomp
      hqx hqy hqz hleft
  · have hright : dist q.1 x.1 ≤ dist (gluingMirror y.1) q.1 := by
      have hle := le_of_not_ge hleft
      simpa only [dist_comm] using hle
    exact gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_longer_seam_test
      (r := r) (R := R) (lam := lam) (ε := ε) hlam x y q z hvariation hdecomp
      hqx hqy hqz hright

/-- Off-fin version for a left-side test point when the attained seam
minimizer lies in the interior of the fin and the midpoint lies on the left
leg. Local admissibility at the minimizer supplies the first-variation
condition; the unfolded-distance lower bound handles the cross-side term. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_interior_seam
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y z : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqInterior : q.1 ∈ interior
      (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane))
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hqx : q.1 ≠ x.1) (hqy : q.1 ≠ gluingMirror y.1)
    (hqz : q.1 ≠ z.1)
    (hba : dist (gluingMirror y.1) q.1 ≤ dist x.1 q.1) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Rg y) / 2 ∧
        (dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
          2 * Real.cosh (dist (L x) (Rg y) / 2) *
              Real.cosh (dist (L z) m) ≤
            Real.cosh (dist (L z) (L x)) + Real.cosh (dist (L z) (Rg y))) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hvariation := gluingCollarFiniteMetricGlue_cross_seam_first_variation_of_interior
    x y z q hqInterior hmin
  let a := dist x.1 q.1
  let b := dist (gluingMirror y.1) q.1
  let d := dist (L x) (Rg y)
  have hsum : d = dist q.1 x.1 + dist q.1 (gluingMirror y.1) := by
    calc
      d = dist x.1 q.1 + dist (gluingMirror y.1) q.1 := hdecomp
      _ = dist q.1 x.1 + dist q.1 (gluingMirror y.1) := by
        rw [dist_comm x.1 q.1, dist_comm (gluingMirror y.1) q.1]
  have hba' : dist q.1 (gluingMirror y.1) ≤ dist q.1 x.1 := by
    simpa only [dist_comm] using hba
  obtain ⟨m', hmseg, hprops⟩ :=
    exists_hyperbolic_broken_geodesic_midpoint_cosh_le
      q.1 x.1 (gluingMirror y.1) z.1 hqx hqy hqz hba' hvariation
  have hxm' : dist x.1 m' = d / 2 := by
    rw [hsum]
    exact hprops.1
  have hmq' : dist m' q.1 = (a - b) / 2 := by
    simpa [a, b, dist_comm] using hprops.2.1
  have hcosh' :
    2 * Real.cosh (d / 2) * Real.cosh (dist z.1 m') ≤
        Real.cosh (dist z.1 x.1) +
          Real.cosh (dist z.1 (gluingMirror y.1)) := by
    have h := hprops.2.2
    rw [← hsum] at h
    exact h
  have hmwin : m' ∈ gluingFinFermiRadialWindow lam R :=
    gluingFinFermiRadialWindow_geodSeg_subset hlam x.2 q.2.1 hmseg
  let p : gluingFinFermiRadialWindow lam R := ⟨m', hmwin⟩
  let m := L p
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  have hcommq : L (I q) = Rg (J q) :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hxm : dist (L x) m = d / 2 := by
    change dist (L x) (L p) = d / 2
    rw [hLI.dist_eq]
    exact hxm'
  have hmq : dist m (L (I q)) = (a - b) / 2 := by
    change dist (L p) (L (I q)) = _
    rw [hLI.dist_eq]
    change dist m' q.1 = _
    exact hmq'
  have huy : dist (L (I q)) (Rg y) = b := by
    calc
      dist (L (I q)) (Rg y) = dist (Rg (J q)) (Rg y) := by rw [hcommq]
      _ = dist (J q) y := hRI.dist_eq (J q) y
      _ = dist (gluingMirror q.1) y.1 := rfl
      _ = dist (gluingMirror q.1) (gluingMirror (gluingMirror y.1)) := by
        rw [gluingMirror_involutive]
      _ = dist q.1 (gluingMirror y.1) := gluingMirror_isometry.dist_eq _ _
      _ = dist (gluingMirror y.1) q.1 := dist_comm _ _
      _ = b := rfl
  have hmy_le : dist m (Rg y) ≤ d / 2 := by
    calc
      dist m (Rg y) ≤ dist m (L (I q)) + dist (L (I q)) (Rg y) :=
        dist_triangle _ _ _
      _ = (a - b) / 2 + b := by rw [hmq, huy]
      _ = d / 2 := by
        rw [hsum]
        dsimp [a, b]
        rw [dist_comm x.1 q.1, dist_comm (gluingMirror y.1) q.1]
        ring
  have hmy_ge : d / 2 ≤ dist m (Rg y) := by
    have htri := dist_triangle (L x) m (Rg y)
    rw [hxm] at htri
    linarith [show dist (L x) (Rg y) = d from rfl]
  have htestx : dist (L z) (L x) = dist z.1 x.1 := hLI.dist_eq z x
  have htestm : dist (L z) m = dist z.1 m' := by
    change dist (L z) (L p) = dist z.1 m'
    rw [hLI.dist_eq]
    rfl
  have htesty : dist z.1 (gluingMirror y.1) ≤ dist (L z) (Rg y) :=
    gluingCollarFiniteMetricGlue_unfolded_cross_dist_le
      (r := r) (R := R) (lam := lam) (ε := ε) z y
  have hcosh_test : Real.cosh (dist z.1 (gluingMirror y.1)) ≤
      Real.cosh (dist (L z) (Rg y)) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
    exact htesty
  have hcomparison :
      2 * Real.cosh (d / 2) * Real.cosh (dist (L z) m) ≤
        Real.cosh (dist (L z) (L x)) + Real.cosh (dist (L z) (Rg y)) := by
    rw [htestm, htestx]
    calc
      2 * Real.cosh (d / 2) * Real.cosh (dist z.1 m') ≤
          Real.cosh (dist z.1 x.1) +
            Real.cosh (dist z.1 (gluingMirror y.1)) := hcosh'
      _ ≤ Real.cosh (dist z.1 x.1) + Real.cosh (dist (L z) (Rg y)) :=
        add_le_add_right hcosh_test _
  exact ⟨m, hxm, le_antisymm hmy_le hmy_ge, hcomparison⟩

/-- The left-slab off-fin midpoint comparison also covers the case where
the minimizing seam point is the reflected right endpoint. Then the broken
path is a single hyperbolic segment, so the comparison is the exact
hyperbolic midpoint identity. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_interior_seam_or_right_endpoint
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y z : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqInterior : q.1 ∈ interior
      (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane))
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hqz : q.1 ≠ z.1)
    (hba : dist (gluingMirror y.1) q.1 ≤ dist x.1 q.1) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Rg y) / 2 ∧
        (dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
          2 * Real.cosh (dist (L x) (Rg y) / 2) *
              Real.cosh (dist (L z) m) ≤
            Real.cosh (dist (L z) (L x)) + Real.cosh (dist (L z) (Rg y))) := by
  dsimp
  by_cases hqx : q.1 = x.1
  · let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    have hmirror : gluingMirror y.1 = x.1 := by
      have hba' : dist (gluingMirror y.1) q.1 ≤ 0 := by
        simpa [hqx] using hba
      have hdist : dist (gluingMirror y.1) q.1 = 0 :=
        le_antisymm hba' dist_nonneg
      have hEq := dist_eq_zero.mp hdist
      rw [hqx] at hEq
      exact hEq
    have hzero : dist (L x) (Rg y) = 0 := by
      rw [hdecomp, hqx, hmirror]
      simp
    have hsame : L x = Rg y := dist_eq_zero.mp hzero
    refine ⟨L x, ?_, ?_, ?_⟩
    · rw [dist_self, hzero]
      norm_num
    · rw [hsame]
      rw [dist_self, hzero]
      norm_num
    · have htest : dist (L z) (Rg y) = dist (L z) (L x) :=
        congrArg (fun p => dist (L z) p) hsame.symm
      rw [hzero, htest]
      norm_num [Real.cosh_zero]
      linarith
  · by_cases hqy : q.1 = gluingMirror y.1
    · let I := gluingCollarFiniteMetricGlueLeft r R lam ε
      let J := gluingCollarFiniteMetricGlueRight r R lam ε
      let L := Metric.toGlueL
        (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
        (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
      let Rg := Metric.toGlueR
        (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
        (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
      have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
      have hJq : J q = y := by
        apply Subtype.ext
        dsimp [J, gluingCollarFiniteMetricGlueRight]
        rw [hqy, gluingMirror_involutive]
      have hcommq : L (I q) = Rg y := by
        rw [← hJq]
        exact congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
      let p0 : UpperHalfPlane :=
        Vendored.RiemannDynamics.geodInterp x.1 q.1 (1 / 2)
      have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hpseg : p0 ∈ Vendored.RiemannDynamics.geodSeg x.1 q.1 :=
        Vendored.RiemannDynamics.geodInterp_mem_geodSeg x.1 q.1 hhalf
      have hpwin : p0 ∈ gluingFinFermiRadialWindow lam R :=
        gluingFinFermiRadialWindow_geodSeg_subset hlam x.2 q.2.1 hpseg
      let p : gluingFinFermiRadialWindow lam R := ⟨p0, hpwin⟩
      let m : gluingCollarFiniteMetricGlueSpace r R lam ε := L p
      have htotal : dist (L x) (Rg y) = dist x.1 q.1 := by
        calc
          dist (L x) (Rg y) = dist (L x) (L (I q)) := by rw [hcommq]
          _ = dist x (I q) := hLI.dist_eq x (I q)
          _ = dist x.1 q.1 := rfl
      have hxm' : dist x.1 p0 = dist x.1 q.1 / 2 := by
        dsimp [p0]
        rw [Vendored.RiemannDynamics.dist_geodInterp_left x.1 q.1 hhalf]
        ring
      have hmq' : dist p0 q.1 = dist x.1 q.1 / 2 := by
        dsimp [p0]
        rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs x.1 q.1 (1 / 2)]
        rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [dist_comm x.1 q.1]
        ring
      have hxm : dist (L x) m = dist (L x) (Rg y) / 2 := by
        change dist (L x) (L p) = _
        rw [hLI.dist_eq, htotal]
        exact hxm'
      have hmy : dist m (Rg y) = dist (L x) (Rg y) / 2 := by
        calc
          dist m (Rg y) = dist (L p) (L (I q)) := by rw [hcommq]
          _ = dist p (I q) := hLI.dist_eq p (I q)
          _ = dist p0 q.1 := rfl
          _ = dist x.1 q.1 / 2 := hmq'
          _ = dist (L x) (Rg y) / 2 := by rw [htotal]
      have hcosh := hyperbolic_midpoint_cosh hxm' hmq' z.1
      have htestm : dist (L z) m = dist z.1 p0 := by
        change dist (L z) (L p) = _
        rw [hLI.dist_eq]
        rfl
      have htestx : dist (L z) (L x) = dist z.1 x.1 := hLI.dist_eq z x
      have htesty : dist (L z) (Rg y) = dist z.1 q.1 := by
        calc
          dist (L z) (Rg y) = dist (L z) (L (I q)) := by rw [hcommq]
          _ = dist z.1 q.1 := hLI.dist_eq z (I q)
      refine ⟨m, hxm, hmy, ?_⟩
      rw [htestm, htestx, htesty, htotal]
      exact le_of_eq hcosh
    · exact gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_interior_seam
        (r := r) (R := R) (lam := lam) (ε := ε) hlam x y z q hqInterior hmin
        hdecomp hqx hqy hqz hba

/-- Reflected off-fin case: an interior seam minimizer also gives the
midpoint comparison for a test point in the right slab, when the right leg is
the longer leg. Reflection exchanges the two model legs, while the unfolded
cross-distance lower bound controls the remaining quotient term. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_interior_seam
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y z : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqInterior : q.1 ∈ interior
      (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane))
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hqx : q.1 ≠ x.1) (hqy : q.1 ≠ gluingMirror y.1)
    (hba : dist x.1 q.1 ≤ dist (gluingMirror y.1) q.1) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (Rg y) m = dist (L x) (Rg y) / 2 ∧
        (dist m (L x) = dist (L x) (Rg y) / 2 ∧
          2 * Real.cosh (dist (L x) (Rg y) / 2) *
              Real.cosh (dist (Rg z) m) ≤
            Real.cosh (dist (Rg z) (L x)) + Real.cosh (dist (Rg z) (Rg y))) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  have hcommq : L (I q) = Rg (J q) :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hsum : dist (L x) (Rg y) = dist x.1 q.1 +
      dist (gluingMirror y.1) q.1 := hdecomp
  by_cases hqz : q.1 = gluingMirror z.1
  · have hJq : J q = z := by
      apply Subtype.ext
      dsimp [J, gluingCollarFiniteMetricGlueRight]
      rw [hqz, gluingMirror_involutive]
    have htest : Rg z = L (I q) := by rw [← hJq, hcommq]
    have hmirrorLeg : dist (gluingMirror y.1) q.1 =
        dist y.1 (gluingMirror q.1) := by
      calc
        dist (gluingMirror y.1) q.1 =
            dist (gluingMirror y.1) (gluingMirror (gluingMirror q.1)) := by
              rw [gluingMirror_involutive]
        _ = dist y.1 (gluingMirror q.1) :=
          gluingMirror_isometry.dist_eq y.1 (gluingMirror q.1)
    have hdecomp' : dist (L x) (Rg y) = dist x (I q) + dist y (J q) := by
      calc
        dist (L x) (Rg y) = dist x.1 q.1 + dist (gluingMirror y.1) q.1 := hdecomp
        _ = dist x (I q) + dist y (J q) := by
          simp only [I, J, gluingCollarFiniteMetricGlueLeft,
            gluingCollarFiniteMetricGlueRight, Subtype.dist_eq]
          rw [hmirrorLeg]
    obtain ⟨m, hxm, hmy, hcosh⟩ :=
      gluingCollarFiniteMetricGlue_cross_midpoint_cosh_at_given_seam
        (r := r) (R := R) (lam := lam) (ε := ε) hlam x y q hdecomp'
    refine ⟨m, ?_, ?_, ?_⟩
    · simpa only [dist_comm] using hmy
    · simpa only [dist_comm] using hxm
    · have htest' :
          Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) z =
            Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) (I q) := by
        simpa only [L, Rg] using htest
      rw [htest']
      exact hcosh.le
  · have hmin' : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (gluingMirror y.1) q.1 + dist x.1 q.1 ≤
            dist (gluingMirror y.1)
                (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
              dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) := by
      intro w t ht
      have h := hmin w t ht
      calc
        dist (gluingMirror y.1) q.1 + dist x.1 q.1 =
            dist x.1 q.1 + dist (gluingMirror y.1) q.1 := add_comm _ _
        _ ≤ dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) := h
        _ = dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) := add_comm _ _
    let my : gluingFinFermiRadialWindow lam R := ⟨gluingMirror y.1, by
      change gluingFinFermiRadialCoord lam (gluingMirror y.1) ∈ Icc (-R) R
      rw [gluingFinFermiRadialCoord_mirror]
      exact y.2⟩
    let mx : gluingFinFermiRadialWindow lam R := ⟨gluingMirror x.1, by
      change gluingFinFermiRadialCoord lam (gluingMirror x.1) ∈ Icc (-R) R
      rw [gluingFinFermiRadialCoord_mirror]
      exact x.2⟩
    let mz : gluingFinFermiRadialWindow lam R := ⟨gluingMirror z.1, by
      change gluingFinFermiRadialCoord lam (gluingMirror z.1) ∈ Icc (-R) R
      rw [gluingFinFermiRadialCoord_mirror]
      exact z.2⟩
    have hmin'' : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist my.1 q.1 + dist (gluingMirror mx.1) q.1 ≤
            dist my.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
              dist (gluingMirror mx.1)
                (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) := by
      intro w t ht
      simpa only [my, mx, gluingFinFermiRadialWindow, gluingMirror_involutive,
        Subtype.coe_eta] using hmin' w t ht
    have hvariation :=
      gluingCollarFiniteMetricGlue_cross_seam_first_variation_of_interior
        (r := r) (R := R) (lam := lam) (ε := ε)
        (x := my) (y := mx) (z := mz)
        q hqInterior hmin''
    have hvariation' :
        0 ≤ geodInterpDistanceForwardDerivative q.1 (gluingMirror z.1)
              (gluingMirror y.1) +
            geodInterpDistanceForwardDerivative q.1 (gluingMirror z.1) x.1 := by
      simpa only [my, mx, mz, gluingMirror_involutive] using hvariation
    have hqMirrorY : q.1 ≠ gluingMirror y.1 := hqy
    have hqX : q.1 ≠ x.1 := hqx
    have hqMirrorZ : q.1 ≠ gluingMirror z.1 := hqz
    have hlong : dist q.1 x.1 ≤ dist q.1 (gluingMirror y.1) := by
      simpa only [dist_comm] using hba
    obtain ⟨m', hmseg, hprops⟩ :=
      exists_hyperbolic_broken_geodesic_midpoint_cosh_le
        q.1 (gluingMirror y.1) x.1 (gluingMirror z.1)
        hqMirrorY hqX hqMirrorZ hlong hvariation'
    have hmWindow : m' ∈ gluingFinFermiRadialWindow lam R :=
      gluingFinFermiRadialWindow_geodSeg_subset hlam
        (by
          change gluingFinFermiRadialCoord lam (gluingMirror y.1) ∈ Icc (-R) R
          rw [gluingFinFermiRadialCoord_mirror]
          exact y.2)
        q.2.1 hmseg
    have hmirrorWindow : gluingMirror m' ∈ gluingFinFermiRadialWindow lam R := by
      change gluingFinFermiRadialCoord lam (gluingMirror m') ∈ Icc (-R) R
      rw [gluingFinFermiRadialCoord_mirror]
      exact hmWindow
    let p : gluingFinFermiRadialWindow lam R := ⟨gluingMirror m', hmirrorWindow⟩
    let m := Rg p
    let d := dist (L x) (Rg y)
    have hdlegs : dist q.1 (gluingMirror y.1) + dist q.1 x.1 = d := by
      change dist q.1 (gluingMirror y.1) + dist q.1 x.1 = dist (L x) (Rg y)
      rw [hdecomp, dist_comm x.1 q.1, dist_comm (gluingMirror y.1) q.1]
      ring
    have hfirst : dist (Rg y) m = d / 2 := by
      change dist (Rg y) (Rg p) = d / 2
      rw [hRI.dist_eq]
      change dist y.1 (gluingMirror m') = d / 2
      have hreflect : dist y.1 (gluingMirror m') = dist (gluingMirror y.1) m' := by
        calc
          dist y.1 (gluingMirror m') =
              dist (gluingMirror y.1) (gluingMirror (gluingMirror m')) :=
            (gluingMirror_isometry.dist_eq y.1 (gluingMirror m')).symm
          _ = dist (gluingMirror y.1) m' := by rw [gluingMirror_involutive]
      rw [hreflect, ← hdlegs]
      exact hprops.1
    have hseam : L (I q) = Rg (J q) := hcommq
    have hmq : dist m (L (I q)) = (dist q.1 (gluingMirror y.1) -
        dist q.1 x.1) / 2 := by
      calc
        dist m (L (I q)) = dist (Rg p) (Rg (J q)) := by rw [← hseam]
        _ = dist p (J q) := hRI.dist_eq _ _
        _ = dist (gluingMirror m') (gluingMirror q.1) := rfl
        _ = dist m' q.1 := gluingMirror_isometry.dist_eq _ _
        _ = _ := hprops.2.1
    have hseamx : dist (L (I q)) (L x) = dist q.1 x.1 := by
      simpa only [I, gluingCollarFiniteMetricGlueLeft, Subtype.dist_eq] using
        hLI.dist_eq (I q) x
    have hsecond_le : dist m (L x) ≤ d / 2 := by
      calc
        dist m (L x) ≤ dist m (L (I q)) + dist (L (I q)) (L x) :=
          dist_triangle _ _ _
        _ = (dist q.1 (gluingMirror y.1) - dist q.1 x.1) / 2 +
              dist q.1 x.1 := by rw [hmq, hseamx]
        _ = d / 2 := by rw [← hdlegs]; ring
    have hsecond_ge : d / 2 ≤ dist m (L x) := by
      have htotal : dist (Rg y) (L x) = d := by
        dsimp [d]
        exact dist_comm _ _
      have htri := dist_triangle (Rg y) m (L x)
      rw [htotal, hfirst] at htri
      linarith
    have hsecond : dist m (L x) = d / 2 := le_antisymm hsecond_le hsecond_ge
    have htestm : dist (Rg z) m = dist (gluingMirror z.1) m' := by
      change dist (Rg z) (Rg p) = _
      rw [hRI.dist_eq]
      change dist z.1 (gluingMirror m') = _
      calc
        dist z.1 (gluingMirror m') =
            dist (gluingMirror z.1) (gluingMirror (gluingMirror m')) :=
          (gluingMirror_isometry.dist_eq z.1 (gluingMirror m')).symm
        _ = _ := by rw [gluingMirror_involutive]
    have hcross : dist (gluingMirror z.1) x.1 ≤ dist (Rg z) (L x) := by
      simpa only [dist_comm] using
        (gluingCollarFiniteMetricGlue_unfolded_cross_dist_le
          (r := r) (R := R) (lam := lam) (ε := ε) x z)
    have hcoshCross : Real.cosh (dist (gluingMirror z.1) x.1) ≤
        Real.cosh (dist (Rg z) (L x)) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
      exact hcross
    have hcoshRight : Real.cosh (dist (gluingMirror z.1)
        (gluingMirror y.1)) = Real.cosh (dist (Rg z) (Rg y)) := by
      have hmirrorDist : dist (gluingMirror z.1) (gluingMirror y.1) =
          dist z.1 y.1 := gluingMirror_isometry.dist_eq _ _
      have hglueDist : dist (Rg z) (Rg y) = dist z.1 y.1 := by
        simpa only [Subtype.dist_eq] using hRI.dist_eq z y
      rw [hmirrorDist, hglueDist]
    have hcomparison : 2 * Real.cosh (d / 2) * Real.cosh (dist (Rg z) m) ≤
        Real.cosh (dist (Rg z) (L x)) + Real.cosh (dist (Rg z) (Rg y)) := by
      rw [htestm]
      have hhinge := hprops.2.2
      rw [hdlegs] at hhinge
      calc
        2 * Real.cosh (d / 2) * Real.cosh (dist (gluingMirror z.1) m') ≤
            Real.cosh (dist (gluingMirror z.1) (gluingMirror y.1)) +
              Real.cosh (dist (gluingMirror z.1) x.1) := hhinge
        _ ≤ Real.cosh (dist (gluingMirror z.1) (gluingMirror y.1)) +
              Real.cosh (dist (Rg z) (L x)) := by nlinarith [hcoshCross]
        _ = _ := by rw [hcoshRight, add_comm]
    exact ⟨m, hfirst, hsecond, hcomparison⟩

/-- The reflected right-slab comparison also covers the case where the
minimizing seam point is the left endpoint. The broken path then reduces to
one hyperbolic segment in the right copy, so its midpoint comparison is exact. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_interior_seam_or_left_endpoint
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y z : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hqInterior : q.1 ∈ interior
      (gluingCollarFiniteUpperFin r R lam ε : Set UpperHalfPlane))
    (hmin : ∀ w : gluingCollarFiniteUpperFin r R lam ε,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x.1 q.1 + dist (gluingMirror y.1) q.1 ≤
          dist x.1 (Vendored.RiemannDynamics.geodInterp q.1 w.1 t) +
            dist (gluingMirror y.1)
              (Vendored.RiemannDynamics.geodInterp q.1 w.1 t))
    (hdecomp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1)
    (hba : dist x.1 q.1 ≤ dist (gluingMirror y.1) q.1) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (Rg y) m = dist (L x) (Rg y) / 2 ∧
        (dist m (L x) = dist (L x) (Rg y) / 2 ∧
          2 * Real.cosh (dist (L x) (Rg y) / 2) *
              Real.cosh (dist (Rg z) m) ≤
            Real.cosh (dist (Rg z) (L x)) + Real.cosh (dist (Rg z) (Rg y))) := by
  dsimp
  by_cases hqx : q.1 = x.1
  · let I := gluingCollarFiniteMetricGlueLeft r R lam ε
    let J := gluingCollarFiniteMetricGlueRight r R lam ε
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
    have hIq : I q = x := Subtype.ext hqx
    have hseam : L x = Rg (J q) := by
      rw [← hIq]
      exact congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
    let p0 : UpperHalfPlane :=
      Vendored.RiemannDynamics.geodInterp (J q).1 y.1 (1 / 2)
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hpseg : p0 ∈ Vendored.RiemannDynamics.geodSeg (J q).1 y.1 :=
      Vendored.RiemannDynamics.geodInterp_mem_geodSeg (J q).1 y.1 hhalf
    have hpwin : p0 ∈ gluingFinFermiRadialWindow lam R :=
      gluingFinFermiRadialWindow_geodSeg_subset hlam (J q).2 y.2 hpseg
    let p : gluingFinFermiRadialWindow lam R := ⟨p0, hpwin⟩
    let m : gluingCollarFiniteMetricGlueSpace r R lam ε := Rg p
    have htotal : dist (L x) (Rg y) = dist (J q).1 y.1 := by
      calc
        dist (L x) (Rg y) = dist (Rg (J q)) (Rg y) := by rw [hseam]
        _ = dist (J q) y := hRI.dist_eq (J q) y
        _ = dist (J q).1 y.1 := rfl
    have hleft : dist (J q).1 p0 = dist (J q).1 y.1 / 2 := by
      dsimp [p0]
      rw [Vendored.RiemannDynamics.dist_geodInterp_left (J q).1 y.1 hhalf]
      ring
    have hright : dist p0 y.1 = dist (J q).1 y.1 / 2 := by
      dsimp [p0]
      rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs (J q).1 y.1 (1 / 2)]
      rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    have hfirst : dist (Rg y) m = dist (L x) (Rg y) / 2 := by
      change dist (Rg y) (Rg p) = _
      rw [hRI.dist_eq, htotal]
      change dist y.1 p0 = dist (J q).1 y.1 / 2
      rw [dist_comm]
      exact hright
    have hsecond : dist m (L x) = dist (L x) (Rg y) / 2 := by
      calc
        dist m (L x) = dist (Rg p) (Rg (J q)) := by rw [hseam]
        _ = dist p (J q) := hRI.dist_eq p (J q)
        _ = dist p0 (J q).1 := rfl
        _ = dist (J q).1 y.1 / 2 := by rw [dist_comm]; exact hleft
        _ = dist (L x) (Rg y) / 2 := by rw [htotal]
    have hcosh := hyperbolic_midpoint_cosh hleft hright z.1
    have htestm : dist (Rg z) m = dist z.1 p0 := by
      change dist (Rg z) (Rg p) = _
      rw [hRI.dist_eq]
      rfl
    have htestx : dist (Rg z) (L x) = dist z.1 (J q).1 := by
      calc
        dist (Rg z) (L x) = dist (Rg z) (Rg (J q)) := by rw [hseam]
        _ = dist z (J q) := hRI.dist_eq z (J q)
        _ = dist z.1 (J q).1 := rfl
    have htesty : dist (Rg z) (Rg y) = dist z.1 y.1 := by
      simpa only [Subtype.dist_eq] using hRI.dist_eq z y
    refine ⟨m, hfirst, hsecond, ?_⟩
    rw [htestm, htestx, htesty, htotal]
    exact le_of_eq hcosh
  · have hqy : q.1 ≠ gluingMirror y.1 := by
      intro hqmirror
      have hzero : dist x.1 q.1 = 0 := by
        have hle : dist x.1 q.1 ≤ 0 := by simpa [hqmirror] using hba
        exact le_antisymm hle dist_nonneg
      exact hqx (dist_eq_zero.mp hzero).symm
    exact gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_interior_seam
      (r := r) (R := R) (lam := lam) (ε := ε) hlam x y z q hqInterior hmin
      hdecomp hqx hqy hba

/-- Every common-fin test point admits the opposite-copy midpoint comparison.
The seam minimizer and its distance decomposition are constructed internally;
endpoint coincidences reduce to a one-piece comparison, a seam coincidence
uses the fixed-seam identity, and the remaining case uses the hinge lemmas. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_any_commonFin_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R)
    (z : gluingCollarFiniteUpperFin r R lam ε) :
    let I := gluingCollarFiniteMetricGlueLeft r R lam ε
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Rg y) / 2 ∧
      (dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
        2 * Real.cosh (dist (L x) (Rg y) / 2) *
            Real.cosh (dist (L (I z)) m) ≤
          Real.cosh (dist (L (I z)) (L x)) +
            Real.cosh (dist (L (I z)) (Rg y))) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  obtain ⟨q, hvariation, hdecomp⟩ :=
    gluingCollarFiniteMetricGlue_cross_seam_first_variation
      (r := r) (R := R) (lam := lam) (ε := ε) hR hlam hconv x y
  have hcommq : L (I q) = Rg (J q) :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hcommz : L (I z) = Rg (J z) :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) z
  have hcommz' :
      Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
        (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) (I z) =
      Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
        (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) (J z) := by
    simpa only [L, Rg] using hcommz
  have hmirror (w : gluingCollarFiniteUpperFin r R lam ε) :
      dist y.1 (gluingMirror w.1) = dist (gluingMirror y.1) w.1 := by
    calc
      dist y.1 (gluingMirror w.1) =
          dist (gluingMirror y.1) (gluingMirror (gluingMirror w.1)) :=
        (gluingMirror_isometry.dist_eq y.1 (gluingMirror w.1)).symm
      _ = dist (gluingMirror y.1) w.1 := by rw [gluingMirror_involutive]
  have hcostq : dist x (I q) + dist y (J q) =
      dist x.1 q.1 + dist (gluingMirror y.1) q.1 := by
    dsimp [I, J, gluingCollarFiniteMetricGlueLeft,
      gluingCollarFiniteMetricGlueRight]
    rw [Subtype.dist_eq, Subtype.dist_eq, hmirror q]
  have hdecomp' : dist (L x) (Rg y) = dist x (I q) + dist y (J q) := by
    rw [hdecomp, hcostq]
  by_cases hqx : q.1 = x.1
  · have hIq : I q = x := Subtype.ext hqx
    have hxcopy : L x = Rg (J q) := by rw [← hIq, hcommq]
    have hxcopy' :
        Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x =
        Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) (J q) := by
      simpa only [L, Rg] using hxcopy
    have hD : dist (L x) (Rg y) = dist (Rg (J q)) (Rg y) := by
      rw [hxcopy]
    obtain ⟨m, hxm, hmy, hcosh⟩ :=
      gluingCollarFiniteMetricGlue_right_midpoint_cosh
        (r := r) (R := R) (lam := lam) (ε := ε) hlam (J q) y (J z)
    refine ⟨m, ?_, ?_, ?_⟩
    · rw [hD, hxcopy']
      exact hxm
    · rw [hD]
      exact hmy
    · have hc := hcosh.le
      rw [← hcommz'] at hc
      rw [hD, hxcopy']
      exact hc
  · by_cases hqy : q.1 = gluingMirror y.1
    · have hJq : J q = y := by
        apply Subtype.ext
        dsimp [J, gluingCollarFiniteMetricGlueRight]
        rw [show q.1 = gluingMirror y.1 from hqy, gluingMirror_involutive]
      have hycopy : Rg y = L (I q) := by rw [← hJq, hcommq]
      have hycopy' :
          Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y =
          Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) (I q) := by
        simpa only [L, Rg] using hycopy
      have hD : dist (L x) (Rg y) = dist (L x) (L (I q)) := by
        rw [hycopy]
      obtain ⟨m, hxm, hmy, hcosh⟩ :=
        gluingCollarFiniteMetricGlue_left_midpoint_cosh
          (r := r) (R := R) (lam := lam) (ε := ε) hlam x (I q) (I z)
      refine ⟨m, ?_, ?_, ?_⟩
      · rw [hD]
        exact hxm
      · rw [hD, hycopy']
        exact hmy
      · rw [hD, hycopy']
        exact hcosh.le
    · by_cases hqz : q.1 = z.1
      · have hzq : z = q := Subtype.ext hqz.symm
        subst z
        obtain ⟨m, hxm, hmy, hcosh⟩ :=
          gluingCollarFiniteMetricGlue_cross_midpoint_cosh_at_given_seam
            (r := r) (R := R) (lam := lam) (ε := ε) hlam x y q hdecomp'
        exact ⟨m, hxm, hmy, hcosh.le⟩
      · have hvariationz : 0 ≤
            geodInterpDistanceForwardDerivative q.1 z.1 x.1 +
              geodInterpDistanceForwardDerivative q.1 z.1 (gluingMirror y.1) :=
          hvariation z
        exact gluingCollarFiniteMetricGlue_cross_midpoint_cosh_commonFin_test
          (r := r) (R := R) (lam := lam) (ε := ε) hlam x y q z
          hvariationz hdecomp hqx hqy hqz

/-- Every pair of points in the complete two-piece metric gluing has a
metric midpoint. Quotient induction reduces to hyperbolic midpoints inside
one slab or the attained-seam construction for opposite slabs. -/
theorem gluingCollarFiniteMetricGlueSpace_exists_midpoint
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingCollarFiniteMetricGlueSpace r R lam ε) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 := by
  refine Quotient.inductionOn x ?_
  intro px
  refine Quotient.inductionOn y ?_
  intro py
  cases px with
  | inl xl =>
    cases py with
    | inl yl =>
      obtain ⟨m, hxm, hmy⟩ :=
        gluingCollarFiniteMetricGlue_left_midpoint
          (r := r) (R := R) (lam := lam) (ε := ε) hlam xl yl
      exact ⟨m, by simpa [Metric.toGlueL, Metric.toGlueR] using hxm,
        by simpa [Metric.toGlueL, Metric.toGlueR] using hmy⟩
    | inr yr =>
      obtain ⟨m, hxm, hmy, _⟩ := gluingCollarFiniteMetricGlue_cross_midpoint
        (r := r) (R := R) (lam := lam) (ε := ε) hR hlam xl yr
      exact ⟨m, by simpa [Metric.toGlueL, Metric.toGlueR] using hxm,
        by simpa [Metric.toGlueL, Metric.toGlueR] using hmy⟩
  | inr xr =>
    cases py with
    | inl yl =>
      obtain ⟨m, hxm, hmy, _⟩ :=
        gluingCollarFiniteMetricGlue_cross_midpoint
          (r := r) (R := R) (lam := lam) (ε := ε) hR hlam yl xr
      refine ⟨m, ?_, ?_⟩
      · change dist (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr) m =
          dist (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr)
            (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) / 2
        calc
          dist (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr) m =
              dist m (Metric.toGlueR
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr) := dist_comm _ _
          _ = dist (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl)
                (Metric.toGlueR
                  (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr) / 2 := hmy
          _ = _ := by rw [dist_comm]
      · change dist m (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) =
          dist (Metric.toGlueR
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr)
            (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) / 2
        calc
          dist m (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) =
              dist (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) m := dist_comm _ _
          _ = dist (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε) 
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl)
                (Metric.toGlueR
                  (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                  (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr) / 2 := hxm
          _ = _ := by rw [dist_comm]
    | inr yr =>
      obtain ⟨m, hxm, hmy⟩ :=
        gluingCollarFiniteMetricGlue_right_midpoint
          (r := r) (R := R) (lam := lam) (ε := ε) hlam xr yr
      exact ⟨m, by simpa [Metric.toGlueL, Metric.toGlueR] using hxm,
        by simpa [Metric.toGlueL, Metric.toGlueR] using hmy⟩

/-- Completeness and the constructed all-pairs midpoints give an actual
isometric geodesic segment in the finite two-slab metric gluing. This is the
geodesic-space input needed before invoking a CAT comparison criterion. -/
theorem gluingCollarFiniteMetricGlueSpace_exists_isometric_segment
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingCollarFiniteMetricGlueSpace r R lam ε) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → gluingCollarFiniteMetricGlueSpace r R lam ε,
      Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  letI : CompleteSpace (gluingCollarFiniteMetricGlueSpace r R lam ε) :=
    gluingCollarFiniteMetricGlueSpace_completeSpace r R lam ε
  let m : gluingCollarFiniteMetricGlueSpace r R lam ε →
      gluingCollarFiniteMetricGlueSpace r R lam ε →
      gluingCollarFiniteMetricGlueSpace r R lam ε :=
    fun a b => (gluingCollarFiniteMetricGlueSpace_exists_midpoint hR hlam a b).choose
  have hm : ∀ a b,
      dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 := by
    intro a b
    exact (gluingCollarFiniteMetricGlueSpace_exists_midpoint hR hlam a b).choose_spec
  obtain ⟨γ, hγ⟩ := exists_midpoint_metric_path m hm x y
  exact metric_path_exists_isometric_interval γ hγ

/-- The finite upper gluing locus is closed in its hyperbolic slab. -/
theorem gluingCollarFiniteUpperFin_isClosed (r R lam ε : ℝ) :
    IsClosed (gluingCollarFiniteUpperFin r R lam ε) := by
  change IsClosed {z | gluingFinFermiRadialCoord lam z ∈ Icc (-R) R ∧
    ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam z) ≤
      gluingFinFermiTransverseCoord lam z}
  apply (isClosed_Icc.preimage (continuous_gluingFinFermiRadialCoord lam)).inter
  exact isClosed_le
    (continuous_const.mul
      ((gluingCollarWarp_continuous r).comp
        (continuous_gluingFinFermiRadialCoord lam)))
    (continuous_gluingFinFermiTransverseCoord lam)

/-- Each closed finite upper fin, with its induced metric, is complete. -/
theorem gluingCollarFiniteUpperFin_completeSpace (r R lam ε : ℝ) :
    CompleteSpace (gluingCollarFiniteUpperFin r R lam ε) :=
  (gluingCollarFiniteUpperFin_isClosed r R lam ε).completeSpace_coe

/-- The finite lower gluing locus is closed in its hyperbolic slab. -/
theorem gluingCollarFiniteLowerFin_isClosed (r R lam ε : ℝ) :
    IsClosed (gluingCollarFiniteLowerFin r R lam ε) := by
  change IsClosed {z | gluingFinFermiRadialCoord lam z ∈ Icc (-R) R ∧
    gluingFinFermiTransverseCoord lam z ≤
      -ε * gluingCollarWarp r (gluingFinFermiRadialCoord lam z)}
  apply (isClosed_Icc.preimage (continuous_gluingFinFermiRadialCoord lam)).inter
  exact isClosed_le
    (continuous_gluingFinFermiTransverseCoord lam)
    (continuous_const.mul
      ((gluingCollarWarp_continuous r).comp
        (continuous_gluingFinFermiRadialCoord lam)))

/-- Each closed finite lower fin, with its induced metric, is complete. -/
theorem gluingCollarFiniteLowerFin_completeSpace (r R lam ε : ℝ) :
    CompleteSpace (gluingCollarFiniteLowerFin r R lam ε) :=
  (gluingCollarFiniteLowerFin_isClosed r R lam ε).completeSpace_coe

/-- Reflection across the imaginary axis is exactly reflection of the
transverse Fermi coordinate, so it identifies the upper and lower fin copies. -/
theorem gluingFinFermiPoint_mirror (lam t u : ℝ) :
    gluingMirror (gluingFinFermiPoint lam t u) =
      gluingFinFermiPoint lam t (-u) := by
  apply UpperHalfPlane.ext_re_im
  · simp only [gluingMirror_re, gluingFinFermiPoint_re]
    rw [show lam * -u = -(lam * u) by ring, Real.tanh_neg]
    ring
  · simp [gluingFinFermiPoint_im, Real.cosh_neg]

/-- The canonical upper-to-lower fin identification preserves the exact
hyperbolic distance used by each finite slab. -/
theorem gluingFinFermiPoint_mirror_dist (lam t₁ u₁ t₂ u₂ : ℝ) :
    dist (gluingFinFermiPoint lam t₁ u₁) (gluingFinFermiPoint lam t₂ u₂) =
      dist (gluingFinFermiPoint lam t₁ (-u₁))
        (gluingFinFermiPoint lam t₂ (-u₂)) := by
  calc
    _ = dist (gluingMirror (gluingFinFermiPoint lam t₁ u₁))
        (gluingMirror (gluingFinFermiPoint lam t₂ u₂)) :=
      (gluingMirror_isometry.dist_eq _ _).symm
    _ = _ := by rw [gluingFinFermiPoint_mirror, gluingFinFermiPoint_mirror]

/-- Every generator of the finite fin quotient is realized by the actual
hyperbolic reflection identifying the upper and lower fin copies. -/
theorem gluingCollarFiniteFinRelation_fermi_eq_mirror
    {r ε : ℝ} {p q : ℤ × ℂ} (h : gluingCollarFiniteFinRelation r ε p q)
    (lam : ℝ) :
    gluingMirror (gluingFinFermiPoint lam p.2.re p.2.im) =
      gluingFinFermiPoint lam q.2.re q.2.im := by
  obtain ⟨_hindex, hre, him, _hfin⟩ := h
  have him' : q.2.im = -p.2.im := by linarith
  rw [gluingFinFermiPoint_mirror, ← hre, him']

/-- The quotient's actual fin-identification relation preserves pairwise
hyperbolic distance across the two attached copies. -/
theorem gluingCollarFiniteFinRelation_fermi_dist
    {r ε : ℝ} {p q p' q' : ℤ × ℂ}
    (hpq : gluingCollarFiniteFinRelation r ε p q)
    (hp'q' : gluingCollarFiniteFinRelation r ε p' q') (lam : ℝ) :
    dist (gluingFinFermiPoint lam p.2.re p.2.im)
      (gluingFinFermiPoint lam p'.2.re p'.2.im) =
    dist (gluingFinFermiPoint lam q.2.re q.2.im)
      (gluingFinFermiPoint lam q'.2.re q'.2.im) := by
  calc
    _ = dist (gluingMirror (gluingFinFermiPoint lam p.2.re p.2.im))
        (gluingMirror (gluingFinFermiPoint lam p'.2.re p'.2.im)) :=
      (gluingMirror_isometry.dist_eq _ _).symm
    _ = _ := by
      rw [gluingCollarFiniteFinRelation_fermi_eq_mirror hpq,
        gluingCollarFiniteFinRelation_fermi_eq_mirror hp'q']

/-- On every sufficiently fine dyadic model, each of the two actual fin
gluing loci is geodesically convex in its hyperbolic slab. This packages the
radial-window convexity together with the previously established upper- and
lower-fin inequalities, as required by the finite Reshetnyak gluing step. -/
theorem eventually_gluingCollarFiniteFins_geodSeg_subset
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (∀ a b : UpperHalfPlane,
        a ∈ gluingCollarFiniteUpperFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) →
        b ∈ gluingCollarFiniteUpperFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) →
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)) ∧
      (∀ a b : UpperHalfPlane,
        a ∈ gluingCollarFiniteLowerFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) →
        b ∈ gluingCollarFiniteLowerFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) →
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteLowerFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)) := by
  obtain ⟨Nu, hNu, hupper⟩ := eventually_gluingFinFermi_upperFin_geodInterp hr hR
  obtain ⟨Nl, hNl, hlower⟩ := eventually_gluingFinFermi_lowerFin_geodInterp hr hR
  refine ⟨max Nu Nl, le_trans hNu (Nat.le_max_left Nu Nl), ?_⟩
  intro n hn
  have hnU : Nu ≤ n := le_trans (Nat.le_max_left Nu Nl) hn
  have hnL : Nl ≤ n := le_trans (Nat.le_max_right Nu Nl) hn
  have hn2 : 2 ≤ n := le_trans (le_trans hNu (Nat.le_max_left Nu Nl)) hn
  have hlam : 0 < Real.sqrt (1 - (1 / 2 : ℝ) ^ n) := by
    apply Real.sqrt_pos.2
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    norm_num at hpow
    nlinarith
  constructor
  · intro a b ha hb
    change gluingFinFermiRadialCoord _ a ∈ Icc (-R) R ∧ _ at ha
    change gluingFinFermiRadialCoord _ b ∈ Icc (-R) R ∧ _ at hb
    intro q hq
    rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hq
    rcases hq with ⟨s, hs, hq⟩
    rw [← hq]
    constructor
    · exact gluingFinFermiRadialCoord_geodInterp_mem_Icc hlam ha.1 hb.1 hs
    · exact hupper n hnU a b ha.1 hb.1 ha.2 hb.2 s hs
  · intro a b ha hb
    change gluingFinFermiRadialCoord _ a ∈ Icc (-R) R ∧ _ at ha
    change gluingFinFermiRadialCoord _ b ∈ Icc (-R) R ∧ _ at hb
    intro q hq
    rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hq
    rcases hq with ⟨s, hs, hq⟩
    rw [← hq]
    constructor
    · exact gluingFinFermiRadialCoord_geodInterp_mem_Icc hlam ha.1 hb.1 hs
    · exact hlower n hnL a b ha.1 hb.1 ha.2 hb.2 s hs

/-- On every sufficiently fine dyadic finite model, each cross-copy pair has
an attained common-fin minimizer satisfying the full one-sided first-variation
condition in every direction that remains in that fin. -/
theorem eventually_gluingCollarFiniteCrossSeam_first_variation
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ x y : gluingFinFermiRadialWindow
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) R,
        ∃ q : gluingCollarFiniteUpperFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
          ∀ w : gluingCollarFiniteUpperFin r R
              (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
              0 ≤ geodInterpDistanceForwardDerivative q.1 w.1 x.1 +
                geodInterpDistanceForwardDerivative q.1 w.1
                  (gluingMirror y.1) := by
  obtain ⟨N, hN, hconv⟩ :=
    eventually_gluingCollarFiniteFins_geodSeg_subset hr hR
  refine ⟨N, hN, ?_⟩
  intro n hn x y
  have hn2 : 2 ≤ n := le_trans hN hn
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
  have hlam : 0 < Real.sqrt (1 - (1 / 2 : ℝ) ^ n) := by
    apply Real.sqrt_pos.2
    norm_num at hpow
    nlinarith
  letI : Nonempty (gluingCollarFiniteUpperFin r R
      (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)) :=
    gluingCollarFiniteUpperFin_nonempty hR hlam
  have hconvUpper : ∀ a ∈ gluingCollarFiniteUpperFin r R
      (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
      ∀ b ∈ gluingCollarFiniteUpperFin r R
        (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) := by
    intro a ha b hb
    exact (hconv n hn).1 a b ha hb
  obtain ⟨q, hvariation, _hdecomp⟩ :=
    gluingCollarFiniteMetricGlue_cross_seam_first_variation
    (r := r) (R := R) (lam := Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
    (ε := (1 / 2 : ℝ) ^ n) hR hlam hconvUpper x y
  exact ⟨q, hvariation⟩

/-- Both actual finite gluing loci inherit the hyperbolic midpoint-cosh
comparison in their induced metrics. This is a pointwise comparison bridge
for the finite curvature argument: it supplies an in-piece midpoint and the
exact ambient identity for every comparison point in that same piece. -/
theorem eventually_gluingCollarFiniteFins_midpoint_cosh
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (∀ a b : {z : UpperHalfPlane // z ∈ gluingCollarFiniteUpperFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)},
        ∃ m : {z : UpperHalfPlane // z ∈ gluingCollarFiniteUpperFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)},
          dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
            ∀ x, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist x m) =
              Real.cosh (dist x a) + Real.cosh (dist x b)) ∧
      (∀ a b : {z : UpperHalfPlane // z ∈ gluingCollarFiniteLowerFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)},
        ∃ m : {z : UpperHalfPlane // z ∈ gluingCollarFiniteLowerFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)},
          dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
            ∀ x, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist x m) =
              Real.cosh (dist x a) + Real.cosh (dist x b)) := by
  obtain ⟨N, hN, hconv⟩ := eventually_gluingCollarFiniteFins_geodSeg_subset hr hR
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨hupper, hlower⟩ := hconv n hn
  constructor
  · intro a b
    have hconvUpper : ∀ z ∈ gluingCollarFiniteUpperFin r R
        (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
        ∀ w ∈ gluingCollarFiniteUpperFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
          Vendored.RiemannDynamics.geodSeg z w ⊆ gluingCollarFiniteUpperFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) := by
      intro z hz w hw
      exact hupper z w hz hw
    exact exists_subtype_hyperbolic_midpoint_cosh
      (S := gluingCollarFiniteUpperFin r R
        (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)) hconvUpper a b
  · intro a b
    have hconvLower : ∀ z ∈ gluingCollarFiniteLowerFin r R
        (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
        ∀ w ∈ gluingCollarFiniteLowerFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
          Vendored.RiemannDynamics.geodSeg z w ⊆ gluingCollarFiniteLowerFin r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n) := by
      intro z hz w hw
      exact hlower z w hz hw
    exact exists_subtype_hyperbolic_midpoint_cosh
      (S := gluingCollarFiniteLowerFin r R
        (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)) hconvLower a b

/-- Ambient Fermi path distance on the bounded radial slab. No constraint on
the transverse coordinate excludes a fin excursion. -/
noncomputable def gluingCollarFiniteFermiEDist (R lam : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (β : ℝ → ℂ) (_h0 : β 0 = z) (_h1 : β 1 = w)
    (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K β (Icc (0 : ℝ) 1))
    (_hWindow : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc (-R) R),
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)

/-- The same endpoint lower bound descends through the actual infimum over
all ambient Fermi competitors in the radial window. -/
theorem gluingCollarFiniteFermiEDist_lower_bound
    {R lam : ℝ} (hlam : lam ≠ 0) (z w : ℂ) :
    ENNReal.ofReal (dist (gluingFinFermiPoint lam z.re z.im)
      (gluingFinFermiPoint lam w.re w.im)) ≤
      ENNReal.ofReal |lam| * gluingCollarFiniteFermiEDist R lam z w := by
  have hscale : ENNReal.ofReal |lam| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hlam)
  unfold gluingCollarFiniteFermiEDist
  simp only [ENNReal.mul_iInf_of_ne hscale ENNReal.ofReal_ne_top]
  refine le_iInf fun β => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hLip => le_iInf fun hWindow => ?_
  obtain ⟨K, hK⟩ := hLip
  have hcurve := gluingCollarFiniteFermiCurve_endpoint_dist_le_cost lam hK
  rw [h0, h1] at hcurve
  exact hcurve

/-- The finite ambient Fermi distance has the matching upper bound: the
hyperbolic segment, written in Fermi coordinates, is a Lipschitz competitor
and stays inside the radial window. -/
theorem gluingCollarFiniteFermiEDist_scaled_upper_bound
    {R lam : ℝ} (hlam : 0 < lam) {z w : ℂ}
    (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    ENNReal.ofReal lam * gluingCollarFiniteFermiEDist R lam z w ≤
      ENNReal.ofReal (dist
        (gluingFinFermiPoint lam z.re z.im)
        (gluingFinFermiPoint lam w.re w.im)) := by
  let Z : UpperHalfPlane := gluingFinFermiPoint lam z.re z.im
  let W : UpperHalfPlane := gluingFinFermiPoint lam w.re w.im
  obtain ⟨α, hα, hpos, h0, h1, hspeed, hdist⟩ :=
    exists_hyperbolic_constantSpeed_segment Z W
  let P : ℝ → UpperHalfPlane := fun t => UpperHalfPlane.ofComplex (α t)
  let β : ℝ → ℂ := gluingFinFermiCoordPath lam α
  have hP0 : P 0 = Z := by
    simp [P, h0, Z, UpperHalfPlane.ofComplex_apply]
  have hP1 : P 1 = W := by
    simp [P, h1, W, UpperHalfPlane.ofComplex_apply]
  have hradZ : gluingFinFermiRadialCoord lam Z = z.re := by
    simpa [Z] using (gluingFinFermiRadialCoord_point hlam)
  have htransZ : gluingFinFermiTransverseCoord lam Z = z.im := by
    simpa [Z] using (gluingFinFermiTransverseCoord_point hlam)
  have hradW : gluingFinFermiRadialCoord lam W = w.re := by
    simpa [W] using (gluingFinFermiRadialCoord_point hlam)
  have htransW : gluingFinFermiTransverseCoord lam W = w.im := by
    simpa [W] using (gluingFinFermiTransverseCoord_point hlam)
  have hβ0 : β 0 = z := by
    apply Complex.ext
    · simp only [β, gluingFinFermiCoordPath, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        zero_mul, mul_zero, sub_zero, add_zero]
      rw [h0]
      change gluingFinFermiRadialCoord lam Z = z.re
      exact hradZ
    · simp only [β, gluingFinFermiCoordPath, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_zero, zero_add, mul_one, add_zero]
      rw [h0]
      change gluingFinFermiTransverseCoord lam Z = z.im
      exact htransZ
  have hβ1 : β 1 = w := by
    apply Complex.ext
    · simp only [β, gluingFinFermiCoordPath, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        zero_mul, mul_zero, sub_zero, add_zero]
      rw [h1]
      change gluingFinFermiRadialCoord lam W = w.re
      exact hradW
    · simp only [β, gluingFinFermiCoordPath, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_zero, zero_add, mul_one, add_zero]
      rw [h1]
      change gluingFinFermiTransverseCoord lam W = w.im
      exact htransW
  obtain ⟨K, hβLip⟩ := exists_gluingFinFermiCoordPath_lipschitz lam hα hpos
  have hPdist (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist Z (P t) = t * dist Z W := by
    rw [← hP0]
    simpa [P, h0, abs_of_nonneg ht.1] using hdist 0 t
  have hPdist' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (P t) W = (1 - t) * dist Z W := by
    rw [← hP1]
    simpa [P, h1, abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0)] using
      hdist t 1
  have hPmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      P t ∈ Vendored.RiemannDynamics.geodSeg Z W := by
    rw [Vendored.RiemannDynamics.mem_geodSeg, hPdist t ht, hPdist' t ht]
    ring
  have hPinterp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      P t = Vendored.RiemannDynamics.geodInterp Z W t :=
    Vendored.RiemannDynamics.eq_of_mem_geodSeg_of_dist_eq
      (hPmem t ht)
      (Vendored.RiemannDynamics.geodInterp_mem_geodSeg Z W ht)
      ((hPdist t ht).trans
        (Vendored.RiemannDynamics.dist_geodInterp_left Z W ht).symm)
  have hβwindow (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (β t).re ∈ Icc (-R) R := by
    have hrad : (β t).re = gluingFinFermiRadialCoord lam (P t) := by
      simp only [β, gluingFinFermiCoordPath, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        zero_mul, mul_zero, sub_zero, add_zero]
      simp [P, gluingFinFermiRadialCoord,
        UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t)]
    rw [hrad, hPinterp t ht]
    exact gluingFinFermiRadialCoord_geodInterp_mem_Icc hlam
      (by simpa [hradZ] using hz) (by simpa [hradW] using hw) ht
  have hpath (t : ℝ) :
      gluingFinFermiLift lam ((β t).re, (β t).im) = α t :=
    gluingFinFermiCoordPath_reconstruct hlam hpos t
  have hscaledCost : ENNReal.ofReal lam *
      (∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)) =
      ENNReal.ofReal (dist Z W) := by
    have hcost := gluingCollarFiniteFermiCurve_cost_eq_scaled_poincare lam
      (a := 0) (b := 1) (K := K) (β := β) (by norm_num) hβLip
    rw [abs_of_pos hlam] at hcost
    have hspeed' (t : ℝ) :
        ‖deriv (fun s => gluingFinFermiLift lam ((β s).re, (β s).im)) t‖ /
            (gluingFinFermiPoint lam (β t).re (β t).im).im =
          ‖deriv α t‖ / (α t).im := by
      rw [show (fun s => gluingFinFermiLift lam ((β s).re, (β s).im)) = α from
        funext hpath]
      congr 1
      change (gluingFinFermiLift lam ((β t).re, (β t).im)).im = (α t).im
      exact congrArg Complex.im (hpath t)
    calc
      _ = ∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (‖deriv α t‖ / (α t).im) := by
        rw [hcost]
        apply lintegral_congr_ae
        filter_upwards with t
        rw [hspeed' t]
      _ = ENNReal.ofReal (dist Z W) := by
        simp_rw [hspeed]
        simp [Real.volume_Icc]
  have hcompetitor : gluingCollarFiniteFermiEDist R lam z w ≤
      ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t) := by
    unfold gluingCollarFiniteFermiEDist
    exact iInf_le_of_le β (iInf_le_of_le hβ0 (iInf_le_of_le hβ1
      (iInf_le_of_le ⟨K, hβLip⟩ (iInf_le_of_le hβwindow le_rfl))))
  calc
    _ ≤ ENNReal.ofReal lam *
        (∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)) := by
      exact mul_le_mul_of_nonneg_left hcompetitor (by positivity)
    _ = ENNReal.ofReal (dist Z W) := hscaledCost
    _ = _ := by simp [Z, W]

/-- Exact identification of the finite ambient Fermi path infimum with the
scaled hyperbolic distance between its Fermi images. -/
theorem gluingCollarFiniteFermiEDist_scaled_eq
    {R lam : ℝ} (hlam : 0 < lam) {z w : ℂ}
    (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    ENNReal.ofReal lam * gluingCollarFiniteFermiEDist R lam z w =
      ENNReal.ofReal (dist
        (gluingFinFermiPoint lam z.re z.im)
        (gluingFinFermiPoint lam w.re w.im)) := by
  apply le_antisymm
  · exact gluingCollarFiniteFermiEDist_scaled_upper_bound hlam hz hw
  · simpa only [abs_of_pos hlam] using
      gluingCollarFiniteFermiEDist_lower_bound (ne_of_gt hlam) z w

theorem gluingCollarFiniteFermiEDist_le_stripEDist
    (r R lam ε : ℝ) (z w : ℂ) :
    gluingCollarFiniteFermiEDist R lam z w ≤
      gluingCollarFiniteStripEDist r R lam ε z w := by
  refine le_iInf fun β => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hLip => le_iInf fun hWindow => le_iInf fun _hStrip => ?_
  exact iInf_le_of_le β (iInf_le_of_le h0 (iInf_le_of_le h1
    (iInf_le_of_le hLip (iInf_le_of_le hWindow le_rfl))))

/-- Clipping every actual ambient Fermi competitor gives a strip competitor
with at most the proved multiplicative length distortion. -/
theorem gluingCollarFiniteStripEDist_clamp_le_fermi
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) (z w : ℂ) :
    gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinStripClamp r ε z) (gluingCollarFinStripClamp r ε w) ≤
      ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
        gluingCollarFiniteFermiEDist R lam z w := by
  have hDpos : 0 < 1 + ε * Real.cosh (|r| + R) := by positivity
  unfold gluingCollarFiniteFermiEDist
  simp only [ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_ne_zero_iff.mpr hDpos) ENNReal.ofReal_ne_top]
  refine le_iInf fun β => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hLip => le_iInf fun hWindow => ?_
  obtain ⟨K, hK⟩ := hLip
  let α : ℝ → ℂ := fun t => gluingCollarFinStripClamp r ε (β t)
  have hα := (gluingCollarFinStripClamp_lipschitzOnWith r hR hε).comp hK hWindow
  have hα0 : α 0 = gluingCollarFinStripClamp r ε z := by simp only [α, h0]
  have hα1 : α 1 = gluingCollarFinStripClamp r ε w := by simp only [α, h1]
  have hαWindow : ∀ t ∈ Icc 0 1, (α t).re ∈ Icc (-R) R := hWindow
  have hαStrip : ∀ t ∈ Icc 0 1, |(α t).im| ≤ ε * gluingCollarWarp r (α t).re :=
    fun t _ => gluingCollarFinStripClamp_mem_strip hr hε (β t)
  have htarget : gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinStripClamp r ε z) (gluingCollarFinStripClamp r ε w) ≤
      ∫⁻ t in Icc 0 1, ENNReal.ofReal (gluingCollarFiniteStripSpeed lam α t) := by
    unfold gluingCollarFiniteStripEDist
    exact iInf_le_of_le α (iInf_le_of_le hα0 (iInf_le_of_le hα1
      (iInf_le_of_le ⟨_, hα⟩ (iInf_le_of_le hαWindow (iInf_le_of_le hαStrip le_rfl)))))
  exact htarget.trans (gluingCollarFinStripClamp_length_le hr hR hε hK hWindow)

/-- A fin excursion cannot create an uncontrolled source shortcut: the
clipped inverse bounds native collar distance by the ambient Fermi distance,
with the product of clipping and inverse-strip distortion factors. -/
theorem gluingCollarModelEDist_clippedInverse_le_fermi
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) (c : ℝ)
    {z w : ℂ} (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    gluingCollarModelEDist hr
      (gluingCollarFinClippedInverse r c ε z) (gluingCollarFinClippedInverse r c ε w) ≤
      ENNReal.ofReal ((1 + ε * Real.cosh (|r| + R)) ^ 2) *
        gluingCollarFiniteFermiEDist R lam z w := by
  have hD : 0 ≤ 1 + ε * Real.cosh (|r| + R) := by positivity
  calc
    _ ≤ ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
        gluingCollarFiniteStripEDist r R lam ε
          (gluingCollarFinStripClamp r ε z) (gluingCollarFinStripClamp r ε w) :=
      gluingCollarModelEDist_inverse_le_strip hr hR hε c hz hw
        (gluingCollarFinStripClamp_mem_strip hr hε z)
        (gluingCollarFinStripClamp_mem_strip hr hε w)
    _ ≤ ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
        (ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
          gluingCollarFiniteFermiEDist R lam z w) :=
      mul_le_mul_right (gluingCollarFiniteStripEDist_clamp_le_fermi hr hR hε z w) _
    _ = _ := by simp only [pow_two, ENNReal.ofReal_mul hD, mul_assoc]

/-- Finite walks through ambient Fermi copies with whole-fin identifications.
Unlike a strip walk, every step permits the full radial slab. -/
inductive GluingCollarFiniteFinChainPath (r R lam ε : ℝ) :
    gluingCollarFiniteFinTarget r ε → gluingCollarFiniteFinTarget r ε →
      ℝ≥0∞ → Prop
  | refl (p) : GluingCollarFiniteFinChainPath r R lam ε p p 0
  | fermi (n : ℤ) (z w : ℂ)
      (hzWindow : z.re ∈ Icc (-R) R) (hwWindow : w.re ∈ Icc (-R) R) :
      GluingCollarFiniteFinChainPath r R lam ε
        (Quotient.mk _ (n, z)) (Quotient.mk _ (n, w))
        (gluingCollarFiniteFermiEDist R lam z w)
  | symm {p q A} : GluingCollarFiniteFinChainPath r R lam ε p q A →
      GluingCollarFiniteFinChainPath r R lam ε q p A
  | trans {p q s A B} : GluingCollarFiniteFinChainPath r R lam ε p q A →
      GluingCollarFiniteFinChainPath r R lam ε q s B →
      GluingCollarFiniteFinChainPath r R lam ε p s (A + B)

noncomputable def gluingCollarFiniteFinChainEDist (r R lam ε : ℝ)
    (p q : gluingCollarFiniteFinTarget r ε) : ℝ≥0∞ :=
  ⨅ A : ℝ≥0∞, ⨅ _h : GluingCollarFiniteFinChainPath r R lam ε p q A, A

theorem gluingCollarFiniteFinChainEDist_le_cost
    {r R lam ε : ℝ} {p q : gluingCollarFiniteFinTarget r ε} {A : ℝ≥0∞}
    (h : GluingCollarFiniteFinChainPath r R lam ε p q A) :
    gluingCollarFiniteFinChainEDist r R lam ε p q ≤ A :=
  iInf_le_of_le A (iInf_le_of_le h le_rfl)

@[simp] theorem gluingCollarFiniteFinChainEDist_self (r R lam ε : ℝ)
    (p : gluingCollarFiniteFinTarget r ε) :
    gluingCollarFiniteFinChainEDist r R lam ε p p = 0 :=
  le_antisymm
    (gluingCollarFiniteFinChainEDist_le_cost (GluingCollarFiniteFinChainPath.refl p)) bot_le

theorem gluingCollarFiniteFinChainEDist_comm (r R lam ε : ℝ)
    (p q : gluingCollarFiniteFinTarget r ε) :
    gluingCollarFiniteFinChainEDist r R lam ε p q =
      gluingCollarFiniteFinChainEDist r R lam ε q p := by
  have h (p q : gluingCollarFiniteFinTarget r ε) :
      gluingCollarFiniteFinChainEDist r R lam ε p q ≤
        gluingCollarFiniteFinChainEDist r R lam ε q p := by
    exact le_iInf fun A => le_iInf fun hqp =>
      gluingCollarFiniteFinChainEDist_le_cost hqp.symm
  exact (h p q).antisymm (h q p)

theorem gluingCollarFiniteFinChainEDist_triangle (r R lam ε : ℝ)
    (p q s : gluingCollarFiniteFinTarget r ε) :
    gluingCollarFiniteFinChainEDist r R lam ε p s ≤
      gluingCollarFiniteFinChainEDist r R lam ε p q +
        gluingCollarFiniteFinChainEDist r R lam ε q s :=
  ENNReal.le_iInf₂_add_iInf₂ fun _A hpq _B hqs =>
    gluingCollarFiniteFinChainEDist_le_cost (hpq.trans hqs)

theorem gluingCollarFiniteFinChainEDist_le_fermi
    {r R lam ε : ℝ} (n : ℤ) {z w : ℂ}
    (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    gluingCollarFiniteFinChainEDist r R lam ε
        (Quotient.mk _ (n, z)) (Quotient.mk _ (n, w)) ≤
      gluingCollarFiniteFermiEDist R lam z w :=
  gluingCollarFiniteFinChainEDist_le_cost
    (GluingCollarFiniteFinChainPath.fermi n z w hz hw)

/-- A genuine strip walk remains a competitor after the fin interiors are
added. Its ambient Fermi costs can only decrease. -/
theorem gluingCollarFiniteFinChainEDist_le_strip_cost
    {r R lam ε : ℝ} {p q : gluingCollarFiniteBandTarget r ε} {A : ℝ≥0∞}
    (h : GluingCollarFiniteChainPath r R lam ε p q A) :
    gluingCollarFiniteFinChainEDist r R lam ε
      (gluingCollarFiniteFinTargetOfStrip r ε p)
      (gluingCollarFiniteFinTargetOfStrip r ε q) ≤ A := by
  induction h with
  | refl p => simp only [gluingCollarFiniteFinChainEDist_self, le_refl]
  | strip n z w hz hw _hzs _hws =>
      simp only [gluingCollarFiniteFinTargetOfStrip_mk]
      exact (gluingCollarFiniteFinChainEDist_le_fermi n hz hw).trans
        (gluingCollarFiniteFermiEDist_le_stripEDist r R lam ε z w)
  | symm h ih => simpa only [gluingCollarFiniteFinChainEDist_comm] using ih
  | trans hpq hqs ihpq ihqs =>
      exact (gluingCollarFiniteFinChainEDist_triangle r R lam ε _ _ _).trans
        (add_le_add ihpq ihqs)

theorem gluingCollarFiniteFinChainEDist_le_strip_chain
    (r R lam ε : ℝ) (p q : gluingCollarFiniteBandTarget r ε) :
    gluingCollarFiniteFinChainEDist r R lam ε
      (gluingCollarFiniteFinTargetOfStrip r ε p)
      (gluingCollarFiniteFinTargetOfStrip r ε q) ≤
        gluingCollarFiniteChainEDist r R lam ε p q :=
  le_iInf fun _A => le_iInf fun h => gluingCollarFiniteFinChainEDist_le_strip_cost h

/-- The forward whole-chain distance estimate already holds in the actual
augmented fin target, permitting all ambient fin excursions. -/
theorem gluingCollarFiniteFinChainEDist_forward_le_native
    {r R c lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlam : 0 ≤ lam) (hε : 0 < ε) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    gluingCollarFiniteFinChainEDist r R lam ε
        (gluingCollarFiniteFinTargetMap r c ε hε x)
        (gluingCollarFiniteFinTargetMap r c ε hε y) ≤
      ENNReal.ofReal (1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
        ε * Real.cosh (|r| + R))) * gluingCollarModelEDist hr x y :=
  (gluingCollarFiniteFinChainEDist_le_strip_chain r R lam ε _ _).trans
    (gluingCollarFiniteChainEDist_forward_le_native hr hR hlam hε hx hy)

/-- Distances between embedded source points stay finite even when fin
excursions are permitted. This is the finiteness needed for the real-valued
distance squeeze, not a reverse-distance or curvature claim. -/
theorem gluingCollarFiniteFinChainEDist_map_lt_top
    {r R c lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlam : 0 ≤ lam) (hε : 0 < ε) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    gluingCollarFiniteFinChainEDist r R lam ε
      (gluingCollarFiniteFinTargetMap r c ε hε x)
      (gluingCollarFiniteFinTargetMap r c ε hε y) < ⊤ :=
  (gluingCollarFiniteFinChainEDist_forward_le_native hr hR hlam hε hx hy).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (gluingCollarModelEDist_lt_top hr x y))

/-- Every finite walk in the whole-fin quotient pulls back to a native
distance bound. All fin-interior identifications respect the clipped inverse. -/
theorem gluingCollarFiniteFinChain_inverse_le_cost
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) (c : ℝ)
    {p q : gluingCollarFiniteFinTarget r ε} {A : ℝ≥0∞}
    (h : GluingCollarFiniteFinChainPath r R lam ε p q A) :
    gluingCollarModelEDist hr
      (gluingCollarFiniteFinTargetInverse hr hε c p)
      (gluingCollarFiniteFinTargetInverse hr hε c q) ≤
      ENNReal.ofReal ((1 + ε * Real.cosh (|r| + R)) ^ 2) * A := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  have hed (x y : ℂ) : gluingCollarModelEDist hr x y = edist x y :=
    (gluingCollarModelMetricSpace_edist hr x y).symm
  induction h with
  | refl p => simp only [hed, edist_self, mul_zero, le_refl]
  | fermi n z w hz hw =>
      simpa only [gluingCollarFiniteFinTargetInverse_mk] using
        gluingCollarModelEDist_clippedInverse_le_fermi hr hR hε
          (c + 2 * (n : ℝ) * ε) hz hw
  | symm h ih => simpa only [hed, edist_comm] using ih
  | trans hpq hqs ihpq ihqs =>
      calc
        _ ≤ gluingCollarModelEDist hr _ _ + gluingCollarModelEDist hr _ _ := by
          simp only [hed]
          exact edist_triangle _ _ _
        _ ≤ _ := add_le_add ihpq ihqs
        _ = _ := (mul_add _ _ _).symm

/-- The reverse native-distance comparison holds for the actual augmented
fin metric, including arbitrary finite walks and all exterior fin excursions. -/
theorem gluingCollarModelEDist_inverse_le_finChain
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) (c : ℝ)
    (p q : gluingCollarFiniteFinTarget r ε) :
    gluingCollarModelEDist hr
      (gluingCollarFiniteFinTargetInverse hr hε c p)
      (gluingCollarFiniteFinTargetInverse hr hε c q) ≤
      ENNReal.ofReal ((1 + ε * Real.cosh (|r| + R)) ^ 2) *
        gluingCollarFiniteFinChainEDist r R lam ε p q := by
  have hDpos : 0 < (1 + ε * Real.cosh (|r| + R)) ^ 2 := by positivity
  unfold gluingCollarFiniteFinChainEDist
  simp only [ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_ne_zero_iff.mpr hDpos) ENNReal.ofReal_ne_top]
  exact le_iInf fun A => le_iInf fun h =>
    gluingCollarFiniteFinChain_inverse_le_cost hr hR hε c h

/-- A minimizing broken hyperbolic route has a single ambient distance
support on the other side of its bend. Its distance agrees at the endpoint,
and it is no farther from any admissible seam point than the other endpoint.
The point is allowed outside the slab: it is used only for model comparison. -/
theorem exists_hyperbolic_broken_geodesic_distance_support
    (S : Set UpperHalfPlane) (q m z : UpperHalfPlane)
    (hvariation : ∀ w ∈ S,
      0 ≤ geodInterpDistanceForwardDerivative q w m +
        geodInterpDistanceForwardDerivative q w z) :
    ∃ v : UpperHalfPlane,
      dist v m = dist q m + dist q z ∧
      ∀ w ∈ S, dist v w ≤ dist z w := by
  classical
  by_cases hqm : q = m
  · subst m
    refine ⟨z, ?_, ?_⟩
    · simp [dist_comm]
    · intro w hw
      exact le_rfl
  by_cases hqz : q = z
  · subst z
    refine ⟨q, ?_, ?_⟩
    · simp
    · intro w hw
      exact le_rfl
  let a : ℝ := dist q z
  let b : ℝ := dist q m
  have ha : 0 < a := dist_pos.mpr hqz
  have hb : 0 < b := dist_pos.mpr hqm
  have has : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hbs : 0 < Real.sinh b := Real.sinh_pos_iff.mpr hb
  let t : ℝ := -a / b
  let v := Vendored.RiemannDynamics.geodInterp q m t
  have ht : t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hb.le
  have htb : t * b = -a := by
    dsimp [t]
    field_simp
  have hrtb : (1 - t) * b = b + a := by
    rw [sub_mul, one_mul, htb]
    ring
  have hvm : dist v m = b + a := by
    dsimp [v]
    rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs,
      abs_of_nonneg (by linarith)]
    exact hrtb
  have hvq : dist v q = a := by
    rw [dist_comm]
    dsimp [v]
    rw [Vendored.RiemannDynamics.dist_geodInterp_left_abs,
      abs_of_nonpos ht]
    change -t * b = a
    rw [neg_mul, htb, neg_neg]
  refine ⟨v, hvm, ?_⟩
  intro w hw
  by_cases hqw : q = w
  · subst w
    rw [hvq]
    exact (dist_comm q z).le
  let c : ℝ := dist q w
  let M : ℝ := Real.cosh (dist w m)
  let Z : ℝ := Real.cosh (dist w z)
  have hc : 0 < c := dist_pos.mpr hqw
  have hcs : 0 < Real.sinh c := Real.sinh_pos_iff.mpr hc
  have hdm : geodInterpDistanceForwardDerivative q w m =
      (c / Real.sinh c) *
        ((M - Real.cosh c * Real.cosh b) / Real.sinh b) := by
    simp [geodInterpDistanceForwardDerivative, c, b, M,
      Ne.symm hqm, dist_comm]
    ring
  have hdz : geodInterpDistanceForwardDerivative q w z =
      (c / Real.sinh c) *
        ((Z - Real.cosh c * Real.cosh a) / Real.sinh a) := by
    simp [geodInterpDistanceForwardDerivative, c, a, Z,
      Ne.symm hqz, dist_comm]
    ring
  have hnormalized : 0 ≤
      (M - Real.cosh c * Real.cosh b) / Real.sinh b +
        (Z - Real.cosh c * Real.cosh a) / Real.sinh a := by
    have hscaled : 0 ≤ (c / Real.sinh c) *
        ((M - Real.cosh c * Real.cosh b) / Real.sinh b +
          (Z - Real.cosh c * Real.cosh a) / Real.sinh a) := by
      simpa [hdm, hdz, mul_add] using hvariation w hw
    exact nonneg_of_mul_nonneg_right hscaled (div_pos hc hcs)
  have hnum : 0 ≤ Real.sinh a * M + Real.sinh b * Z -
      Real.sinh (a + b) * Real.cosh c := by
    have hmul : 0 ≤ Real.sinh a * Real.sinh b *
        ((M - Real.cosh c * Real.cosh b) / Real.sinh b +
          (Z - Real.cosh c * Real.cosh a) / Real.sinh a) :=
      mul_nonneg (mul_nonneg has.le hbs.le) hnormalized
    have hidentity : Real.sinh a * M + Real.sinh b * Z -
        Real.sinh (a + b) * Real.cosh c =
        Real.sinh a * Real.sinh b *
          ((M - Real.cosh c * Real.cosh b) / Real.sinh b +
            (Z - Real.cosh c * Real.cosh a) / Real.sinh a) := by
      field_simp [ne_of_gt has, ne_of_gt hbs]
      rw [Real.sinh_add]
      ring
    rw [hidentity]
    exact hmul
  have hinterp : Real.sinh b * Real.cosh (dist w v) =
      Real.sinh (a + b) * Real.cosh c - Real.sinh a * M := by
    have h := geodInterp_sinh_cosh_interpolation q m w t
    change Real.sinh b * Real.cosh (dist w v) =
      Real.sinh ((1 - t) * b) * Real.cosh (dist w q) +
        Real.sinh (t * b) * Real.cosh (dist w m) at h
    rw [hrtb, htb, Real.sinh_neg] at h
    simpa only [add_comm b a, ← dist_comm q w, c, M, sub_eq_add_neg,
      neg_mul] using h
  have hscaled : Real.sinh b * Real.cosh (dist w v) ≤ Real.sinh b * Z := by
    rw [hinterp]
    linarith only [hnum]
  have hcosh : Real.cosh (dist v w) ≤ Real.cosh (dist z w) := by
    have h : Real.cosh (dist w v) ≤ Z := by
      nlinarith only [hscaled, hbs]
    simpa only [Z, dist_comm] using h
  have h := Real.cosh_le_cosh.mp hcosh
  simpa only [abs_of_nonneg dist_nonneg] using h

/-- The actual cross-copy distance from a fixed right point has an ambient
hyperbolic distance support at every left point. The support dominates no
cross distance: its model distances are LOWER bounds and agree at that point. -/
theorem gluingCollarFiniteMetricGlue_exists_left_cross_distance_support
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (m z : gluingFinFermiRadialWindow lam R) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ v : UpperHalfPlane,
      dist v m.1 = dist (L m) (Rg z) ∧
      ∀ w : gluingFinFermiRadialWindow lam R,
        dist v w.1 ≤ dist (L w) (Rg z) := by
  dsimp
  obtain ⟨q, hvariation, hdecomp⟩ :=
    gluingCollarFiniteMetricGlue_cross_seam_first_variation hR hlam hconv m z
  have hvariation' : ∀ w ∈ gluingCollarFiniteUpperFin r R lam ε,
      0 ≤ geodInterpDistanceForwardDerivative q.1 w m.1 +
        geodInterpDistanceForwardDerivative q.1 w (gluingMirror z.1) := by
    intro w hw
    exact hvariation ⟨w, hw⟩
  obtain ⟨v, hvm, hsupport⟩ := exists_hyperbolic_broken_geodesic_distance_support
    (gluingCollarFiniteUpperFin r R lam ε) q.1 m.1 (gluingMirror z.1) hvariation'
  refine ⟨v, ?_, ?_⟩
  · rw [hdecomp]
    simpa only [dist_comm] using hvm
  · intro w
    rw [gluingCollarFiniteMetricGlue_cross_dist]
    apply le_ciInf
    intro p
    have hp := hsupport p.1 p.2
    change dist v w.1 ≤ dist w.1 p.1 + dist z.1 (gluingMirror p.1)
    have hmirror : dist (gluingMirror z.1) p.1 =
        dist z.1 (gluingMirror p.1) := by
      calc
        dist (gluingMirror z.1) p.1 =
            dist (gluingMirror z.1) (gluingMirror (gluingMirror p.1)) := by
          rw [gluingMirror_involutive]
        _ = dist z.1 (gluingMirror p.1) := gluingMirror_isometry.dist_eq _ _
    calc
      dist v w.1 ≤ dist v p.1 + dist p.1 w.1 := dist_triangle _ _ _
      _ ≤ dist (gluingMirror z.1) p.1 + dist p.1 w.1 := by
        linarith only [hp]
      _ = dist w.1 p.1 + dist z.1 (gluingMirror p.1) := by
        rw [hmirror, dist_comm p.1 w.1]
        ring

/-- Arbitrary quotient test points satisfy midpoint-cosh comparison for
every left-copy endpoint pair, including the formerly missing off-fin
midpoint/opposite-copy test case. Convexity is that of the actual gluing fin. -/
theorem gluingCollarFiniteMetricGlue_left_midpoint_cosh_all_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (L y) / 2 ∧
      dist m (L y) = dist (L x) (L y) / 2 ∧
      ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
        2 * Real.cosh (dist (L x) (L y) / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z (L x)) + Real.cosh (dist z (L y)) := by
  dsimp
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  obtain ⟨p, hxp, hpy, hcosh⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun a ha b hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  have hxp' : dist x.1 p.1 = dist x.1 y.1 / 2 := hxp
  have hpy' : dist p.1 y.1 = dist x.1 y.1 / 2 := hpy
  refine ⟨L p, ?_, ?_, ?_⟩
  · change dist (L x) (L p) = dist (L x) (L y) / 2
    rw [hLI.dist_eq, hLI.dist_eq]
    exact hxp
  · change dist (L p) (L y) = dist (L x) (L y) / 2
    rw [hLI.dist_eq, hLI.dist_eq]
    exact hpy
  · intro z
    refine Quotient.inductionOn z ?_
    intro c
    cases c with
    | inl w =>
      change 2 * Real.cosh (dist (L x) (L y) / 2) *
        Real.cosh (dist (L w) (L p)) ≤
        Real.cosh (dist (L w) (L x)) + Real.cosh (dist (L w) (L y))
      rw [hLI.dist_eq, hLI.dist_eq, hLI.dist_eq, hLI.dist_eq]
      exact (hcosh w).le
    | inr w =>
      change 2 * Real.cosh (dist (L x) (L y) / 2) *
        Real.cosh (dist (Rg w) (L p)) ≤
        Real.cosh (dist (Rg w) (L x)) + Real.cosh (dist (Rg w) (L y))
      obtain ⟨v, hvp, hvbound⟩ :=
        gluingCollarFiniteMetricGlue_exists_left_cross_distance_support hR hlam hconv p w
      have hdist : dist (Rg w) (L p) = dist v p.1 := by
        rw [dist_comm]
        exact hvp.symm
      have hcosh_bound (a : gluingFinFermiRadialWindow lam R) :
          Real.cosh (dist v a.1) ≤ Real.cosh (dist (Rg w) (L a)) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg, dist_comm (Rg w)]
        exact hvbound a
      rw [hLI.dist_eq, hdist]
      calc
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist v p.1) =
            Real.cosh (dist v x.1) + Real.cosh (dist v y.1) :=
          hyperbolic_midpoint_cosh hxp' hpy' v
        _ ≤ Real.cosh (dist (Rg w) (L x)) + Real.cosh (dist (Rg w) (L y)) :=
          add_le_add (hcosh_bound x) (hcosh_bound y)

/-- Reflecting the same distance-support construction gives a model support
for cross distances from a fixed left point to every right-copy point. -/
theorem gluingCollarFiniteMetricGlue_exists_right_cross_distance_support
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (m z : gluingFinFermiRadialWindow lam R) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ v : UpperHalfPlane,
      dist v m.1 = dist (L z) (Rg m) ∧
      ∀ w : gluingFinFermiRadialWindow lam R,
        dist v w.1 ≤ dist (L z) (Rg w) := by
  dsimp
  obtain ⟨q, hvariation, hdecomp⟩ :=
    gluingCollarFiniteMetricGlue_cross_seam_first_variation hR hlam hconv z m
  have hvariation' : ∀ w ∈ gluingCollarFiniteUpperFin r R lam ε,
      0 ≤ geodInterpDistanceForwardDerivative q.1 w (gluingMirror m.1) +
        geodInterpDistanceForwardDerivative q.1 w z.1 := by
    intro w hw
    simpa only [add_comm] using hvariation ⟨w, hw⟩
  obtain ⟨v, hvm, hsupport⟩ := exists_hyperbolic_broken_geodesic_distance_support
    (gluingCollarFiniteUpperFin r R lam ε) q.1 (gluingMirror m.1) z.1 hvariation'
  have hmirror (a b : UpperHalfPlane) : dist (gluingMirror a) b =
      dist a (gluingMirror b) := by
    calc
      dist (gluingMirror a) b =
          dist (gluingMirror a) (gluingMirror (gluingMirror b)) := by
        rw [gluingMirror_involutive]
      _ = dist a (gluingMirror b) := gluingMirror_isometry.dist_eq _ _
  refine ⟨gluingMirror v, ?_, ?_⟩
  · rw [hmirror, hvm, hdecomp]
    rw [dist_comm q.1 (gluingMirror m.1), dist_comm q.1 z.1]
    ring
  · intro w
    rw [gluingCollarFiniteMetricGlue_cross_dist]
    apply le_ciInf
    intro p
    have hp := hsupport p.1 p.2
    change dist (gluingMirror v) w.1 ≤
      dist z.1 p.1 + dist w.1 (gluingMirror p.1)
    rw [hmirror]
    calc
      dist v (gluingMirror w.1) ≤ dist v p.1 + dist p.1 (gluingMirror w.1) :=
        dist_triangle _ _ _
      _ ≤ dist z.1 p.1 + dist p.1 (gluingMirror w.1) := by
        linarith only [hp]
      _ = dist z.1 p.1 + dist w.1 (gluingMirror p.1) := by
        rw [← hmirror p.1 w.1, dist_comm (gluingMirror p.1) w.1]

/-- Every right-copy endpoint pair has a midpoint satisfying comparison
against all points of the actual quotient, including off-fin left tests. -/
theorem gluingCollarFiniteMetricGlue_right_midpoint_cosh_all_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R) :
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (Rg x) m = dist (Rg x) (Rg y) / 2 ∧
      dist m (Rg y) = dist (Rg x) (Rg y) / 2 ∧
      ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
        2 * Real.cosh (dist (Rg x) (Rg y) / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z (Rg x)) + Real.cosh (dist z (Rg y)) := by
  dsimp
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨p, hxp, hpy, hcosh⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun a ha b hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  have hxp' : dist x.1 p.1 = dist x.1 y.1 / 2 := hxp
  have hpy' : dist p.1 y.1 = dist x.1 y.1 / 2 := hpy
  refine ⟨Rg p, ?_, ?_, ?_⟩
  · change dist (Rg x) (Rg p) = dist (Rg x) (Rg y) / 2
    rw [hRI.dist_eq, hRI.dist_eq]
    exact hxp
  · change dist (Rg p) (Rg y) = dist (Rg x) (Rg y) / 2
    rw [hRI.dist_eq, hRI.dist_eq]
    exact hpy
  · intro z
    refine Quotient.inductionOn z ?_
    intro c
    cases c with
    | inl w =>
      change 2 * Real.cosh (dist (Rg x) (Rg y) / 2) *
        Real.cosh (dist (L w) (Rg p)) ≤
        Real.cosh (dist (L w) (Rg x)) + Real.cosh (dist (L w) (Rg y))
      obtain ⟨v, hvp, hvbound⟩ :=
        gluingCollarFiniteMetricGlue_exists_right_cross_distance_support hR hlam hconv p w
      have hcosh_bound (a : gluingFinFermiRadialWindow lam R) :
          Real.cosh (dist v a.1) ≤ Real.cosh (dist (L w) (Rg a)) := by
        apply Real.cosh_le_cosh.mpr
        simpa only [abs_of_nonneg dist_nonneg] using hvbound a
      rw [hRI.dist_eq, ← hvp]
      calc
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist v p.1) =
            Real.cosh (dist v x.1) + Real.cosh (dist v y.1) :=
          hyperbolic_midpoint_cosh hxp' hpy' v
        _ ≤ Real.cosh (dist (L w) (Rg x)) + Real.cosh (dist (L w) (Rg y)) :=
          add_le_add (hcosh_bound x) (hcosh_bound y)
    | inr w =>
      change 2 * Real.cosh (dist (Rg x) (Rg y) / 2) *
        Real.cosh (dist (Rg w) (Rg p)) ≤
        Real.cosh (dist (Rg w) (Rg x)) + Real.cosh (dist (Rg w) (Rg y))
      rw [hRI.dist_eq, hRI.dist_eq, hRI.dist_eq, hRI.dist_eq]
      exact (hcosh w).le

#print axioms exists_hyperbolic_broken_geodesic_distance_support
#print axioms gluingCollarFiniteMetricGlue_exists_left_cross_distance_support
#print axioms gluingCollarFiniteMetricGlue_left_midpoint_cosh_all_test
#print axioms gluingCollarFiniteMetricGlue_exists_right_cross_distance_support
#print axioms gluingCollarFiniteMetricGlue_right_midpoint_cosh_all_test

#print axioms gluingCollarFiniteFermiEDist_le_stripEDist
#print axioms gluingCollarFiniteFermiCurve_speed_eq
#print axioms gluingCollarFiniteFermiCurve_speed_eq_ae
#print axioms gluingCollarFiniteFermiCurve_cost_eq_scaled_poincare
#print axioms gluingCollarFiniteFermiCurve_image_lipschitz
#print axioms gluingFinFermiCoordPath_contDiff
#print axioms exists_gluingFinFermiCoordPath_lipschitz
#print axioms gluingFinFermiCoordPath_reconstruct
#print axioms gluingCollarFiniteFermiCurve_endpoint_dist_le_cost
#print axioms gluingFinFermiRadialCoord_geodInterp_mem_Icc
#print axioms gluingFinFermiRadialWindow_isClosed
#print axioms gluingFinFermiRadialWindow_completeSpace
#print axioms gluingFinFermiRadialWindow_geodSeg_subset
#print axioms gluingCollarFiniteUpperFin_isClosed
#print axioms gluingCollarFiniteUpperFin_completeSpace
#print axioms gluingCollarFiniteLowerFin_isClosed
#print axioms gluingCollarFiniteLowerFin_completeSpace
#print axioms gluingFinFermiPoint_mirror
#print axioms gluingFinFermiPoint_mirror_dist
#print axioms gluingCollarFiniteFinRelation_fermi_eq_mirror
#print axioms gluingCollarFiniteFinRelation_fermi_dist
#print axioms gluingCollarFiniteUpperLowerEquiv_isometry
#print axioms gluingCollarFiniteUpperFin_nonempty
#print axioms gluingCollarFiniteMetricGlue_commute
#print axioms gluingCollarFiniteMetricGlueLeft_toGlue_isometry
#print axioms gluingCollarFiniteMetricGlueRight_toGlue_isometry
#print axioms gluingCollarFiniteMetricGlueSpace_completeSpace
#print axioms exists_isMinOn_closed_of_distance_lower_bound
#print axioms gluingCollarFiniteMetricGlue_cross_dist
#print axioms gluingCollarFiniteMetricGlue_unfolded_cross_dist_le
#print axioms gluingCollarFiniteMetricGlue_seam_left_cross_dist_eq
#print axioms gluingCollarFiniteMetricGlue_cross_dist_attained
#print axioms gluingCollarFiniteMetricGlue_cross_seam_geodesic_minimum
#print axioms gluingCollarFiniteMetricGlue_cross_seam_first_variation
#print axioms gluingCollarFiniteUpperFin_interior_or_boundary
#print axioms gluingCollarFiniteUpperFin_minimizer_ne_upper_radial_cap
#print axioms gluingCollarFiniteLowerFin_minimizer_ne_lower_radial_cap
#print axioms gluingCollarFiniteMetricGlue_cross_dist_attained_below_upper_cap
#print axioms gluingCollarFiniteMetricGlue_cross_dist_attained_radially_interior
#print axioms gluingCollarFiniteMetricGlue_cross_seam_first_variation_radially_interior
#print axioms gluingCollarFiniteMetricGlue_cross_seam_first_variation_of_interior
#print axioms gluingFinFermiSeamCoshDist_hasDerivAt
#print axioms gluingFinFermiSeamGraph_dist_hasDerivAt
#print axioms gluingFinFermiSeamGraph_distanceSum_stationary
#print axioms isLocalMin_hasDerivWithinAt_nonneg_Ici
#print axioms isLocalMin_hasDerivWithinAt_nonpos_Iic
#print axioms gluingFinFermiSeamGraph_dist_hasDerivWithinAt_of_coshDist
#print axioms gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_right
#print axioms gluingFinFermiSeamGraph_dist_hasDerivWithinAt_zero_left
#print axioms gluingFinFermiSeamGraph_distanceSum_center_subgradient
#print axioms gluingCollarFiniteMetricGlue_seamGraph_isLocalMin
#print axioms gluingCollarFiniteMetricGlue_centerSeam_isLocalMin
#print axioms gluingCollarFiniteMetricGlue_centerSeam_subgradient
#print axioms gluingCollarFiniteMetricGlue_seamGraph_tangential_stationary
#print axioms exists_gluingFinFermiRadialWindow_interpolation
#print axioms gluingCollarFiniteMetricGlue_left_midpoint
#print axioms gluingCollarFiniteMetricGlue_left_midpoint_cosh
#print axioms gluingCollarFiniteMetricGlue_right_midpoint_cosh
#print axioms gluingCollarFiniteMetricGlue_commonFin_midpoint_cosh
#print axioms gluingCollarFiniteMetricGlue_right_midpoint
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_of_seam
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_at_seam
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_at_given_seam
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_longer_seam_test
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_longer_seam_test
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_commonFin_test
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_any_commonFin_test
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_interior_seam
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_interior_seam_or_right_endpoint
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_interior_seam
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_interior_seam_or_left_endpoint
#print axioms gluingCollarFiniteMetricGlueSpace_exists_midpoint
#print axioms gluingCollarFiniteMetricGlueSpace_exists_isometric_segment
#print axioms eventually_gluingCollarFiniteFins_geodSeg_subset
#print axioms eventually_gluingCollarFiniteCrossSeam_first_variation
#print axioms eventually_gluingCollarFiniteFins_midpoint_cosh
#print axioms gluingCollarFiniteFermiEDist_lower_bound
#print axioms gluingCollarFiniteFermiEDist_scaled_upper_bound
#print axioms gluingCollarFiniteFermiEDist_scaled_eq
#print axioms gluingCollarFiniteFinChainEDist_triangle
#print axioms gluingCollarFiniteFinChainEDist_le_strip_chain
#print axioms gluingCollarFiniteFinChainEDist_forward_le_native
#print axioms gluingCollarFiniteFinChainEDist_map_lt_top
#print axioms gluingCollarFiniteStripEDist_clamp_le_fermi
#print axioms gluingCollarModelEDist_clippedInverse_le_fermi
#print axioms gluingCollarFiniteFinChain_inverse_le_cost
#print axioms gluingCollarModelEDist_inverse_le_finChain

/-- If an actual cross-copy midpoint is represented on the left, its cosh
comparison holds against every left test point, without any interior-seam
condition. The exact midpoint equalities force the model support at the
original left endpoint to have this very midpoint. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_left_midpoint
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y p : gluingFinFermiRadialWindow lam R)
    (hxp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) p) =
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2)
    (hpy : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) p)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∀ z : gluingFinFermiRadialWindow lam R,
      2 * Real.cosh (dist (L x) (Rg y) / 2) * Real.cosh (dist (L z) (L p)) ≤
        Real.cosh (dist (L z) (L x)) + Real.cosh (dist (L z) (Rg y)) := by
  dsimp
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let d := dist (L x) (Rg y)
  have hLI := gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε
  obtain ⟨v, hvx, hvbound⟩ :=
    gluingCollarFiniteMetricGlue_exists_left_cross_distance_support hR hlam hconv x y
  change dist v x.1 = d at hvx
  have hxp' : dist x.1 p.1 = d / 2 := by
    change dist (L x) (L p) = d / 2 at hxp
    rw [hLI.dist_eq] at hxp
    exact hxp
  have hvp_le : dist v p.1 ≤ d / 2 := by
    have h := hvbound p
    change dist v p.1 ≤ dist (L p) (Rg y) at h
    rw [hpy] at h
    exact h
  have hvp_ge : d / 2 ≤ dist v p.1 := by
    have htri := dist_triangle v p.1 x.1
    rw [hvx, dist_comm p.1 x.1, hxp'] at htri
    linarith only [htri]
  have hpv : dist p.1 v = dist x.1 v / 2 := by
    rw [dist_comm p.1 v, dist_comm x.1 v, hvx]
    exact le_antisymm hvp_le hvp_ge
  have hxp_model : dist x.1 p.1 = dist x.1 v / 2 := by
    rw [dist_comm x.1 v, hvx]
    exact hxp'
  intro z
  change 2 * Real.cosh (d / 2) * Real.cosh (dist (L z) (L p)) ≤
    Real.cosh (dist (L z) (L x)) + Real.cosh (dist (L z) (Rg y))
  have hcosh_bound : Real.cosh (dist z.1 v) ≤
      Real.cosh (dist (L z) (Rg y)) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, dist_comm z.1 v] using hvbound z
  rw [hLI.dist_eq, hLI.dist_eq]
  calc
    2 * Real.cosh (d / 2) * Real.cosh (dist z.1 p.1) =
        Real.cosh (dist z.1 x.1) + Real.cosh (dist z.1 v) := by
      have h := hyperbolic_midpoint_cosh hxp_model hpv z.1
      rw [dist_comm x.1 v, hvx] at h
      exact h
    _ ≤ Real.cosh (dist z.1 x.1) + Real.cosh (dist (L z) (Rg y)) := by
      linarith only [hcosh_bound]

/-- Reflected own-copy test case: every right test point satisfies comparison
at an actual cross-copy midpoint represented in the right slab, including
seam-graph and radial-cap minimizing seams. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_right_midpoint
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y p : gluingFinFermiRadialWindow lam R)
    (hxp : dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) p) =
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2)
    (hpy : dist
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) p)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist
        (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) / 2) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∀ z : gluingFinFermiRadialWindow lam R,
      2 * Real.cosh (dist (L x) (Rg y) / 2) * Real.cosh (dist (Rg z) (Rg p)) ≤
        Real.cosh (dist (Rg z) (L x)) + Real.cosh (dist (Rg z) (Rg y)) := by
  dsimp
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let d := dist (L x) (Rg y)
  have hRI := gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε
  obtain ⟨v, hvy, hvbound⟩ :=
    gluingCollarFiniteMetricGlue_exists_right_cross_distance_support hR hlam hconv y x
  change dist v y.1 = d at hvy
  have hpy' : dist p.1 y.1 = d / 2 := by
    change dist (Rg p) (Rg y) = d / 2 at hpy
    rw [hRI.dist_eq] at hpy
    exact hpy
  have hvp_le : dist v p.1 ≤ d / 2 := by
    have h := hvbound p
    change dist v p.1 ≤ dist (L x) (Rg p) at h
    rw [hxp] at h
    exact h
  have hvp_ge : d / 2 ≤ dist v p.1 := by
    have htri := dist_triangle v p.1 y.1
    rw [hvy, hpy'] at htri
    linarith only [htri]
  have hyp : dist y.1 p.1 = dist y.1 v / 2 := by
    rw [dist_comm y.1 p.1, hpy', dist_comm y.1 v, hvy]
  have hpv : dist p.1 v = dist y.1 v / 2 := by
    rw [dist_comm p.1 v, dist_comm y.1 v, hvy]
    exact le_antisymm hvp_le hvp_ge
  intro z
  change 2 * Real.cosh (d / 2) * Real.cosh (dist (Rg z) (Rg p)) ≤
    Real.cosh (dist (Rg z) (L x)) + Real.cosh (dist (Rg z) (Rg y))
  have hcosh_bound : Real.cosh (dist z.1 v) ≤
      Real.cosh (dist (Rg z) (L x)) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, dist_comm] using hvbound z
  rw [hRI.dist_eq, hRI.dist_eq]
  calc
    2 * Real.cosh (d / 2) * Real.cosh (dist z.1 p.1) =
        Real.cosh (dist z.1 y.1) + Real.cosh (dist z.1 v) := by
      have h := hyperbolic_midpoint_cosh hyp hpv z.1
      rw [dist_comm y.1 v, hvy] at h
      exact h
    _ ≤ Real.cosh (dist (Rg z) (L x)) + Real.cosh (dist z.1 y.1) := by
      linarith only [hcosh_bound]

/-- An all-test-point midpoint comparison determines its midpoint uniquely.
This transports a constructed comparison midpoint to the specified midpoint
of an actual constant-speed metric path. -/
theorem midpoint_eq_of_midpoint_cosh_all_test
    {M : Type*} [MetricSpace M] {x y n m : M}
    (hcomparison : ∀ z : M,
      2 * Real.cosh (dist x y / 2) * Real.cosh (dist z n) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hxm : dist x m = dist x y / 2)
    (hmy : dist m y = dist x y / 2) : m = n := by
  have h := hcomparison m
  rw [dist_comm m x, hxm, hmy] at h
  have hfactor : 0 < 2 * Real.cosh (dist x y / 2) := by positivity
  have hcosh : Real.cosh (dist m n) ≤ 1 := by
    nlinarith only [h, hfactor]
  have hcosh' : Real.cosh (dist m n) ≤ Real.cosh 0 := by simpa using hcosh
  have hd : dist m n ≤ 0 := by
    simpa only [abs_of_nonneg dist_nonneg, abs_zero] using Real.cosh_le_cosh.mp hcosh'
  exact dist_eq_zero.mp (le_antisymm hd dist_nonneg)

#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_left_midpoint
#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_right_midpoint
#print axioms midpoint_eq_of_midpoint_cosh_all_test

end SystolicGrowth
