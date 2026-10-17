module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarRiemannian
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-!
# Conformal coordinates for the original circular-seam collar

The actual radial primitive of the reciprocal warp is a genuine open
coordinate, including at the nonsmooth seam. Its inverse has derivative
equal to the original positive warp. The literal collar tangent form becomes
a conformal Euclidean form under this coordinate change.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace SystolicGrowth

/-- The actual conformal radial coordinate, based at the original seam. -/
noncomputable def gluingCollarConformalRadius (r t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (gluingCollarWarp r s)⁻¹

@[simp] theorem gluingCollarConformalRadius_zero (r : ℝ) :
    gluingCollarConformalRadius r 0 = 0 := by
  simp [gluingCollarConformalRadius]

/-- **Math.** Continuity of the native positive warp suffices for a strict
derivative, even at the seam; no differentiability of the warp is assumed. -/
theorem gluingCollarConformalRadius_hasStrictDerivAt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasStrictDerivAt (gluingCollarConformalRadius r) (gluingCollarWarp r t)⁻¹ t := by
  exact ((gluingCollarWarp_continuous r).inv₀
    (fun s => (gluingCollarWarp_pos hr s).ne')).integral_hasStrictDerivAt 0 t

theorem gluingCollarConformalRadius_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (gluingCollarConformalRadius r) :=
  continuous_iff_continuousAt.mpr fun t =>
    (gluingCollarConformalRadius_hasStrictDerivAt hr t).hasDerivAt.continuousAt

theorem gluingCollarConformalRadius_strictMono {r : ℝ} (hr : 0 < r) :
    StrictMono (gluingCollarConformalRadius r) := by
  apply strictMono_of_hasDerivAt_pos
    (fun t => (gluingCollarConformalRadius_hasStrictDerivAt hr t).hasDerivAt)
  intro t
  exact inv_pos.mpr (gluingCollarWarp_pos hr t)

theorem gluingCollarConformalRadius_isOpenEmbedding {r : ℝ} (hr : 0 < r) :
    Topology.IsOpenEmbedding (gluingCollarConformalRadius r) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (gluingCollarConformalRadius_continuous hr)
    (gluingCollarConformalRadius_strictMono hr).injective
  exact isOpenMap_of_hasStrictDerivAt
    (gluingCollarConformalRadius_hasStrictDerivAt hr)
    (fun t => inv_ne_zero (gluingCollarWarp_pos hr t).ne')

/-- The original radial line, homeomorphic to its actual open conformal
range. The inverse is constructed by the proved open embedding. -/
noncomputable def gluingCollarConformalRadialChart {r : ℝ} (hr : 0 < r) :
    OpenPartialHomeomorph ℝ ℝ :=
  (gluingCollarConformalRadius_isOpenEmbedding hr).toOpenPartialHomeomorph
    (gluingCollarConformalRadius r)

@[simp] theorem gluingCollarConformalRadialChart_apply {r : ℝ} (hr : 0 < r) (t : ℝ) :
    gluingCollarConformalRadialChart hr t = gluingCollarConformalRadius r t := rfl

@[simp] theorem gluingCollarConformalRadialChart_source {r : ℝ} (hr : 0 < r) :
    (gluingCollarConformalRadialChart hr).source = univ := rfl

@[simp] theorem gluingCollarConformalRadialChart_left_inv {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (gluingCollarConformalRadialChart hr).symm (gluingCollarConformalRadius r t) = t :=
  (gluingCollarConformalRadialChart hr).left_inv (mem_univ t)

/-- **Math.** The genuine inverse radial derivative equals the actual warp
at the inverse point, with no hidden inverse-function premise. -/
theorem gluingCollarConformalRadialChart_symm_hasStrictDerivAt {r : ℝ}
    (hr : 0 < r) {u : ℝ} (hu : u ∈ (gluingCollarConformalRadialChart hr).target) :
    HasStrictDerivAt (gluingCollarConformalRadialChart hr).symm
      (gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm u)) u := by
  simpa only [inv_inv] using
    (gluingCollarConformalRadialChart hr).hasStrictDerivAt_symm hu
      (inv_ne_zero (gluingCollarWarp_pos hr _).ne')
      (gluingCollarConformalRadius_hasStrictDerivAt hr _)

/-- The actual two-dimensional coordinate change, leaving the original
angular coordinate unchanged. Its source includes the entire collar model. -/
noncomputable def gluingCollarConformalChart {r : ℝ} (hr : 0 < r) :
    OpenPartialHomeomorph GluingCollarModel GluingCollarModel :=
  (gluingCollarConformalRadialChart hr).prod (OpenPartialHomeomorph.refl ℝ)

@[simp] theorem gluingCollarConformalChart_apply {r : ℝ} (hr : 0 < r)
    (p : GluingCollarModel) :
    gluingCollarConformalChart hr p = (gluingCollarConformalRadius r p.1, p.2) := rfl

@[simp] theorem gluingCollarConformalChart_source {r : ℝ} (hr : 0 < r) :
    (gluingCollarConformalChart hr).source = univ := by
  simp [gluingCollarConformalChart]

/-- The actual derivative of the conformal coordinate map. -/
noncomputable def gluingCollarConformalDerivative (r : ℝ) (p : GluingCollarModel) :
    GluingCollarModel →L[ℝ] GluingCollarModel :=
  ((gluingCollarWarp r p.1)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem gluingCollarConformalDerivative_apply (r : ℝ)
    (p v : GluingCollarModel) :
    gluingCollarConformalDerivative r p v = (v.1 / gluingCollarWarp r p.1, v.2) := by
  simp [gluingCollarConformalDerivative, div_eq_mul_inv, mul_comm]

theorem gluingCollarConformalChart_hasFDerivAt {r : ℝ} (hr : 0 < r)
    (p : GluingCollarModel) :
    HasFDerivAt (gluingCollarConformalChart hr)
      (gluingCollarConformalDerivative r p) p := by
  change HasFDerivAt (fun q : ℝ × ℝ => (gluingCollarConformalRadius r q.1, q.2))
    (gluingCollarConformalDerivative r p) p
  have heq :
      ((ContinuousLinearMap.toSpanSingleton ℝ (gluingCollarWarp r p.1)⁻¹).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) =
      gluingCollarConformalDerivative r p := by
    ext <;> simp [gluingCollarConformalDerivative, mul_comm]
  rw [← heq]
  exact ((gluingCollarConformalRadius_hasStrictDerivAt hr p.1).hasDerivAt.hasFDerivAt.comp p
    hasFDerivAt_fst).prodMk hasFDerivAt_snd

/-- **Math.** The original continuous tangent form is exactly conformal
Euclidean in the constructed coordinates, including the seam point. -/
theorem gluingCollarTangentForm_eq_conformal {r : ℝ} (hr : 0 < r)
    (p v w : GluingCollarModel) :
    gluingCollarTangentForm r p v w = (gluingCollarWarp r p.1) ^ 2 *
      ((gluingCollarConformalDerivative r p v).1 *
          (gluingCollarConformalDerivative r p w).1 +
        (gluingCollarConformalDerivative r p v).2 *
          (gluingCollarConformalDerivative r p w).2) := by
  simp only [gluingCollarTangentForm_apply, gluingCollarConformalDerivative_apply]
  field_simp [(gluingCollarWarp_pos hr p.1).ne']

#print axioms gluingCollarConformalRadialChart_symm_hasStrictDerivAt
#print axioms gluingCollarConformalChart_hasFDerivAt
#print axioms gluingCollarTangentForm_eq_conformal

end SystolicGrowth
