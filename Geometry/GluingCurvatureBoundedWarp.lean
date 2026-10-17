module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLocalizedSmoothWarp
public import Geometry.GluingWarpedGaussianCurvature
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Normalized positive forcing for a curvature-controlled seam warp

The compactly supported bump is normalized so that its weighted mass exactly
replaces the positive derivative jump of the native seam warp. This is the
source term for the smooth ODE profile whose curvature defect is nonnegative.
-/

open MeasureTheory
open scoped ContDiff Topology

namespace SystolicGrowth

/-- The positive `cosh`-weighted mass available in the plateau of a genuine
compactly supported seam cutoff. -/
noncomputable def gluingCurvatureForcingMass (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  ∫ t in (0 : ℝ)..δ,
    Real.cosh t * gluingCollarSmoothingCutoff δ hδ t ∂volume

/-- The cutoff has strictly positive weighted mass because it is identically
one on the inner half of its support. -/
theorem gluingCurvatureForcingMass_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < gluingCurvatureForcingMass δ hδ := by
  let b := gluingCollarSmoothingCutoff δ hδ
  have hcont : Continuous (fun t : ℝ => Real.cosh t * b t) :=
    Real.continuous_cosh.mul b.continuous
  have hfirst : 0 < ∫ t in (0 : ℝ)..(δ / 2), Real.cosh t * b t ∂volume := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _)
    · intro t ht
      have habs : |t| ≤ b.rIn := by
        change |t| ≤ δ / 2
        rw [abs_of_pos ht.1]
        exact le_of_lt ht.2
      have hb : b t = 1 := b.one_of_mem_closedBall (by
        simpa [Real.dist_eq] using habs)
      rw [hb]
      simpa using Real.cosh_pos t
    · linarith
  have hlast : 0 ≤ ∫ t in (δ / 2)..δ, Real.cosh t * b t ∂volume := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact mul_nonneg (Real.cosh_pos t).le b.nonneg
  have hsplit :
      (∫ t in (0 : ℝ)..(δ / 2), Real.cosh t * b t ∂volume) +
        ∫ t in (δ / 2)..δ, Real.cosh t * b t ∂volume =
          ∫ t in (0 : ℝ)..δ, Real.cosh t * b t ∂volume := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) _ _)
      (hcont.intervalIntegrable (μ := volume) _ _)
  unfold gluingCurvatureForcingMass
  change 0 < ∫ t in (0 : ℝ)..δ, Real.cosh t * b t ∂volume
  rw [← hsplit]
  linarith

/-- Scale the cutoff to replace exactly the native seam derivative jump. -/
noncomputable def gluingCurvatureForcingScale (r δ : ℝ) (hδ : 0 < δ) : ℝ :=
  Real.cosh r / gluingCurvatureForcingMass δ hδ

/-- The smooth nonnegative source term, supported in the seam strip. -/
noncomputable def gluingCurvatureForcing (r δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  fun t => gluingCurvatureForcingScale r δ hδ * gluingCollarSmoothingCutoff δ hδ t

theorem gluingCurvatureForcingScale_pos (r δ : ℝ) (hδ : 0 < δ) :
    0 < gluingCurvatureForcingScale r δ hδ :=
  div_pos (Real.cosh_pos r) (gluingCurvatureForcingMass_pos hδ)

theorem gluingCurvatureForcing_nonneg (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ gluingCurvatureForcing r δ hδ t :=
  mul_nonneg (gluingCurvatureForcingScale_pos r δ hδ).le
    (gluingCollarSmoothingCutoff δ hδ).nonneg

theorem gluingCurvatureForcing_even (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureForcing r δ hδ (-t) = gluingCurvatureForcing r δ hδ t := by
  simp only [gluingCurvatureForcing]
  rw [(gluingCollarSmoothingCutoff δ hδ).neg]

/-- The total weighted forcing is exactly `cosh r`, which cancels the native
positive derivative jump at the seam. -/
theorem gluingCurvatureForcing_normalized (r δ : ℝ) (hδ : 0 < δ) :
    ∫ t in (0 : ℝ)..δ,
      Real.cosh t * gluingCurvatureForcing r δ hδ t ∂volume = Real.cosh r := by
  let b := gluingCollarSmoothingCutoff δ hδ
  have hm : 0 < gluingCurvatureForcingMass δ hδ := gluingCurvatureForcingMass_pos hδ
  have hfun : (fun t : ℝ => Real.cosh t * gluingCurvatureForcing r δ hδ t) =
      fun t => gluingCurvatureForcingScale r δ hδ * (Real.cosh t * b t) := by
    funext t
    simp only [gluingCurvatureForcing, b]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  change gluingCurvatureForcingScale r δ hδ *
    gluingCurvatureForcingMass δ hδ = Real.cosh r
  rw [gluingCurvatureForcingScale]
  exact div_mul_cancel₀ _ hm.ne'

theorem gluingCurvatureForcing_contDiff (r δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (gluingCurvatureForcing r δ hδ) := by
  unfold gluingCurvatureForcing
  have hb : ContDiff ℝ ∞ (gluingCollarSmoothingCutoff δ hδ) :=
    (gluingCollarSmoothingCutoff δ hδ).contDiff (n := ⊤)
  exact contDiff_const.mul hb

/-- The weighted even primitive of the normalized forcing. -/
noncomputable def gluingCurvatureForcingC (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  ∫ s in (0 : ℝ)..t, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume

/-- The odd-weighted primitive of the normalized forcing. -/
noncomputable def gluingCurvatureForcingS (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  ∫ s in (0 : ℝ)..t, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume

theorem gluingCurvatureForcingC_hasDerivAt (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (gluingCurvatureForcingC r δ hδ)
      (Real.cosh t * gluingCurvatureForcing r δ hδ t) t := by
  have hF : ContDiff ℝ ∞ (gluingCurvatureForcing r δ hδ) :=
    gluingCurvatureForcing_contDiff r δ hδ
  have hcont : Continuous (fun s : ℝ => Real.cosh s * gluingCurvatureForcing r δ hδ s) :=
    Real.continuous_cosh.mul hF.continuous
  change HasDerivAt
    (fun u : ℝ => ∫ s in (0 : ℝ)..u,
      Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume) _ _
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable (μ := volume) _ _)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

theorem gluingCurvatureForcingS_hasDerivAt (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (gluingCurvatureForcingS r δ hδ)
      (Real.sinh t * gluingCurvatureForcing r δ hδ t) t := by
  have hF : ContDiff ℝ ∞ (gluingCurvatureForcing r δ hδ) :=
    gluingCurvatureForcing_contDiff r δ hδ
  have hcont : Continuous (fun s : ℝ => Real.sinh s * gluingCurvatureForcing r δ hδ s) :=
    Real.continuous_sinh.mul hF.continuous
  change HasDerivAt
    (fun u : ℝ => ∫ s in (0 : ℝ)..u,
      Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume) _ _
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable (μ := volume) _ _)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

theorem gluingCurvatureForcingC_contDiff (r δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (gluingCurvatureForcingC r δ hδ) := by
  rw [contDiff_infty_iff_deriv]
  have hderiv : deriv (gluingCurvatureForcingC r δ hδ) =
      fun t => Real.cosh t * gluingCurvatureForcing r δ hδ t := by
    funext t
    exact (gluingCurvatureForcingC_hasDerivAt r δ hδ t).deriv
  have hdiff : Differentiable ℝ (gluingCurvatureForcingC r δ hδ) := by
    intro t
    exact (gluingCurvatureForcingC_hasDerivAt r δ hδ t).differentiableAt
  refine ⟨hdiff, ?_⟩
  rw [hderiv]
  exact Real.contDiff_cosh.mul (gluingCurvatureForcing_contDiff r δ hδ)

theorem gluingCurvatureForcingS_contDiff (r δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (gluingCurvatureForcingS r δ hδ) := by
  rw [contDiff_infty_iff_deriv]
  have hderiv : deriv (gluingCurvatureForcingS r δ hδ) =
      fun t => Real.sinh t * gluingCurvatureForcing r δ hδ t := by
    funext t
    exact (gluingCurvatureForcingS_hasDerivAt r δ hδ t).deriv
  have hdiff : Differentiable ℝ (gluingCurvatureForcingS r δ hδ) := by
    intro t
    exact (gluingCurvatureForcingS_hasDerivAt r δ hδ t).differentiableAt
  refine ⟨hdiff, ?_⟩
  rw [hderiv]
  exact Real.contDiff_sinh.mul (gluingCurvatureForcing_contDiff r δ hδ)

/-- The exact even warp obtained by solving `f'' - f = forcing` and matching
the native positive-side solution at the outer edge of the seam strip. -/
noncomputable def gluingCurvatureBoundedWarp (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  (Real.sinh r + gluingCurvatureForcingS r δ hδ δ) * Real.cosh t +
    Real.sinh t * gluingCurvatureForcingC r δ hδ t -
      Real.cosh t * gluingCurvatureForcingS r δ hδ t

/-- The candidate derivative of the ODE warp. -/
noncomputable def gluingCurvatureBoundedWarpSlope
    (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) : ℝ :=
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  (Real.sinh r + gluingCurvatureForcingS r δ hδ δ) * Real.sinh t +
    Real.cosh t * gluingCurvatureForcingC r δ hδ t -
      Real.sinh t * gluingCurvatureForcingS r δ hδ t

theorem gluingCurvatureBoundedWarp_contDiff (r δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (gluingCurvatureBoundedWarp r δ hδ) := by
  unfold gluingCurvatureBoundedWarp
  have hC := gluingCurvatureForcingC_contDiff r δ hδ
  have hS := gluingCurvatureForcingS_contDiff r δ hδ
  fun_prop

theorem gluingCurvatureForcingC_neg (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureForcingC r δ hδ (-t) = -gluingCurvatureForcingC r δ hδ t := by
  let q : ℝ → ℝ := fun s => Real.cosh s * gluingCurvatureForcing r δ hδ s
  have hq : ∀ s, q (-s) = q s := by
    intro s
    simp [q, Real.cosh_neg, gluingCurvatureForcing_even]
  have hcomp : (∫ s in (-t)..(0 : ℝ), q s ∂volume) =
      ∫ s in (0 : ℝ)..t, q (-s) ∂volume := by
    simpa only [neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := q) (a := (0 : ℝ)) (b := t)).symm
  calc
    gluingCurvatureForcingC r δ hδ (-t) =
        -∫ s in (-t)..(0 : ℝ), q s ∂volume := by
      change (∫ s in (0 : ℝ)..(-t), q s ∂volume) = _
      rw [intervalIntegral.integral_symm]
    _ = -∫ s in (0 : ℝ)..t, q (-s) ∂volume := by rw [hcomp]
    _ = -∫ s in (0 : ℝ)..t, q s ∂volume := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact hq s
    _ = -gluingCurvatureForcingC r δ hδ t := rfl

theorem gluingCurvatureForcingS_neg (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureForcingS r δ hδ (-t) = gluingCurvatureForcingS r δ hδ t := by
  let q : ℝ → ℝ := fun s => Real.sinh s * gluingCurvatureForcing r δ hδ s
  have hq : ∀ s, q (-s) = -q s := by
    intro s
    simp [q, Real.sinh_neg, gluingCurvatureForcing_even]
  have hcomp : (∫ s in (-t)..(0 : ℝ), q s ∂volume) =
      ∫ s in (0 : ℝ)..t, q (-s) ∂volume := by
    simpa only [neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := q) (a := (0 : ℝ)) (b := t)).symm
  calc
    gluingCurvatureForcingS r δ hδ (-t) =
        -∫ s in (-t)..(0 : ℝ), q s ∂volume := by
      change (∫ s in (0 : ℝ)..(-t), q s ∂volume) = _
      rw [intervalIntegral.integral_symm]
    _ = -∫ s in (0 : ℝ)..t, q (-s) ∂volume := by rw [hcomp]
    _ = -∫ s in (0 : ℝ)..t, -q s ∂volume := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact hq s
    _ = ∫ s in (0 : ℝ)..t, q s ∂volume := by rw [intervalIntegral.integral_neg, neg_neg]
    _ = gluingCurvatureForcingS r δ hδ t := rfl

theorem gluingCurvatureBoundedWarp_even (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureBoundedWarp r δ hδ (-t) = gluingCurvatureBoundedWarp r δ hδ t := by
  simp only [gluingCurvatureBoundedWarp, Real.cosh_neg, Real.sinh_neg,
    gluingCurvatureForcingC_neg, gluingCurvatureForcingS_neg]
  ring

theorem gluingCurvatureForcingC_split (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureForcingC r δ hδ t +
      ∫ s in t..δ, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume =
        gluingCurvatureForcingC r δ hδ δ := by
  change (∫ s in (0 : ℝ)..t,
      Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume) +
    ∫ s in t..δ, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume =
      ∫ s in (0 : ℝ)..δ,
        Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume
  exact intervalIntegral.integral_add_adjacent_intervals
    ((Real.continuous_cosh.mul
      (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)
    ((Real.continuous_cosh.mul
      (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)

theorem gluingCurvatureForcingS_split (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureForcingS r δ hδ t +
      ∫ s in t..δ, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume =
        gluingCurvatureForcingS r δ hδ δ := by
  change (∫ s in (0 : ℝ)..t,
      Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume) +
    ∫ s in t..δ, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume =
      ∫ s in (0 : ℝ)..δ,
        Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume
  exact intervalIntegral.integral_add_adjacent_intervals
    ((Real.continuous_sinh.mul
      (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)
    ((Real.continuous_sinh.mul
      (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)

theorem gluingCurvatureForcingC_delta (r δ : ℝ) (hδ : 0 < δ) :
    gluingCurvatureForcingC r δ hδ δ = Real.cosh r :=
  gluingCurvatureForcing_normalized r δ hδ

/-- Inside the strip, the new warp exceeds the native cusp warp by the
positive Green-kernel integral of the forcing. -/
theorem gluingCurvatureBoundedWarp_sub_native_eq_integral
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) :
    gluingCurvatureBoundedWarp r δ hδ t - gluingCollarWarp r t =
      ∫ s in t..δ, Real.sinh (s - t) * gluingCurvatureForcing r δ hδ s ∂volume := by
  have hCsplit := gluingCurvatureForcingC_split r δ hδ t
  have hSsplit := gluingCurvatureForcingS_split r δ hδ t
  have hCδ := gluingCurvatureForcingC_delta r δ hδ
  have hCtail : gluingCurvatureForcingC r δ hδ δ -
      gluingCurvatureForcingC r δ hδ t =
        ∫ s in t..δ, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume := by
    linarith
  have hStail : gluingCurvatureForcingS r δ hδ δ -
      gluingCurvatureForcingS r δ hδ t =
        ∫ s in t..δ, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume := by
    linarith
  calc
    gluingCurvatureBoundedWarp r δ hδ t - gluingCollarWarp r t =
        Real.cosh t * (gluingCurvatureForcingS r δ hδ δ -
          gluingCurvatureForcingS r δ hδ t) -
        Real.sinh t * (gluingCurvatureForcingC r δ hδ δ -
          gluingCurvatureForcingC r δ hδ t) := by
      unfold gluingCurvatureBoundedWarp
      rw [gluingCollarWarp_eq_of_nonneg r ht, Real.sinh_add, ← hCδ]
      ring
    _ = Real.cosh t * (∫ s in t..δ,
          Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume) -
        Real.sinh t * (∫ s in t..δ,
          Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume) := by
      rw [hStail, hCtail]
    _ = ∫ s in t..δ,
        (Real.cosh t * (Real.sinh s * gluingCurvatureForcing r δ hδ s) -
          Real.sinh t * (Real.cosh s * gluingCurvatureForcing r δ hδ s)) ∂volume := by
      have hg : Continuous (gluingCurvatureForcing r δ hδ) :=
        (gluingCurvatureForcing_contDiff r δ hδ).continuous
      have hf1 : IntervalIntegrable
          (fun s => Real.cosh t * (Real.sinh s * gluingCurvatureForcing r δ hδ s))
          volume t δ :=
        (continuous_const.mul (Real.continuous_sinh.mul hg)).intervalIntegrable _ _
      have hf2 : IntervalIntegrable
          (fun s => Real.sinh t * (Real.cosh s * gluingCurvatureForcing r δ hδ s))
          volume t δ :=
        (continuous_const.mul (Real.continuous_cosh.mul hg)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hf1 hf2]
    _ = ∫ s in t..δ,
        Real.sinh (s - t) * gluingCurvatureForcing r δ hδ s ∂volume := by
      apply intervalIntegral.integral_congr
      intro s _
      change Real.cosh t * (Real.sinh s * gluingCurvatureForcing r δ hδ s) -
          Real.sinh t * (Real.cosh s * gluingCurvatureForcing r δ hδ s) =
            Real.sinh (s - t) * gluingCurvatureForcing r δ hδ s
      rw [Real.sinh_sub]
      ring

theorem gluingCurvatureBoundedWarp_ge_native
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) (htδ : t ≤ δ) :
    gluingCollarWarp r t ≤ gluingCurvatureBoundedWarp r δ hδ t := by
  rw [← sub_nonneg]
  rw [gluingCurvatureBoundedWarp_sub_native_eq_integral r δ hδ ht]
  apply intervalIntegral.integral_nonneg htδ
  intro s hs
  apply mul_nonneg
  · exact Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hs.1)
  · exact gluingCurvatureForcing_nonneg r δ hδ s

theorem gluingCurvatureForcingC_tail_zero
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (hδt : δ ≤ t) :
    ∫ s in δ..t, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume = 0 := by
  let b := gluingCollarSmoothingCutoff δ hδ
  calc
    ∫ s in δ..t, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume =
        ∫ s in δ..t, (0 : ℝ) ∂volume := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hδt] at hs
      have hδs : b.rOut ≤ |s| := by
        change δ ≤ |s|
        rw [abs_of_nonneg (le_trans hδ.le hs.1)]
        exact hs.1
      have hb : b s = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq] using hδs)
      have hb' : gluingCollarSmoothingCutoff δ hδ s = 0 := by simpa [b] using hb
      simp [gluingCurvatureForcing, hb']
    _ = 0 := by simp

theorem gluingCurvatureForcingS_tail_zero
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (hδt : δ ≤ t) :
    ∫ s in δ..t, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume = 0 := by
  let b := gluingCollarSmoothingCutoff δ hδ
  calc
    ∫ s in δ..t, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume =
        ∫ s in δ..t, (0 : ℝ) ∂volume := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hδt] at hs
      have hδs : b.rOut ≤ |s| := by
        change δ ≤ |s|
        rw [abs_of_nonneg (le_trans hδ.le hs.1)]
        exact hs.1
      have hb : b s = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq] using hδs)
      have hb' : gluingCollarSmoothingCutoff δ hδ s = 0 := by simpa [b] using hb
      simp [gluingCurvatureForcing, hb']
    _ = 0 := by simp

theorem gluingCurvatureForcingC_eq_delta_of_ge
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (hδt : δ ≤ t) :
    gluingCurvatureForcingC r δ hδ t = gluingCurvatureForcingC r δ hδ δ := by
  have hsplit : gluingCurvatureForcingC r δ hδ δ +
      ∫ s in δ..t, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume =
        gluingCurvatureForcingC r δ hδ t := by
    change (∫ s in (0 : ℝ)..δ,
        Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume) +
      ∫ s in δ..t, Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume =
        ∫ s in (0 : ℝ)..t,
          Real.cosh s * gluingCurvatureForcing r δ hδ s ∂volume
    exact intervalIntegral.integral_add_adjacent_intervals
      ((Real.continuous_cosh.mul
        (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)
      ((Real.continuous_cosh.mul
        (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)
  rw [gluingCurvatureForcingC_tail_zero r δ hδ hδt] at hsplit
  linarith

theorem gluingCurvatureForcingS_eq_delta_of_ge
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (hδt : δ ≤ t) :
    gluingCurvatureForcingS r δ hδ t = gluingCurvatureForcingS r δ hδ δ := by
  have hsplit : gluingCurvatureForcingS r δ hδ δ +
      ∫ s in δ..t, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume =
        gluingCurvatureForcingS r δ hδ t := by
    change (∫ s in (0 : ℝ)..δ,
        Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume) +
      ∫ s in δ..t, Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume =
        ∫ s in (0 : ℝ)..t,
          Real.sinh s * gluingCurvatureForcing r δ hδ s ∂volume
    exact intervalIntegral.integral_add_adjacent_intervals
      ((Real.continuous_sinh.mul
        (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)
      ((Real.continuous_sinh.mul
        (gluingCurvatureForcing_contDiff r δ hδ).continuous).intervalIntegrable _ _)
  rw [gluingCurvatureForcingS_tail_zero r δ hδ hδt] at hsplit
  linarith

theorem gluingCurvatureBoundedWarp_eq_native_of_ge_strip
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (hδt : δ ≤ t) :
    gluingCurvatureBoundedWarp r δ hδ t = gluingCollarWarp r t := by
  unfold gluingCurvatureBoundedWarp
  rw [gluingCurvatureForcingC_eq_delta_of_ge r δ hδ hδt,
    gluingCurvatureForcingS_eq_delta_of_ge r δ hδ hδt,
    gluingCurvatureForcingC_delta]
  rw [gluingCollarWarp_eq_of_nonneg r (le_trans hδ.le hδt), Real.sinh_add]
  ring

private theorem gluingCollarWarp_even (r t : ℝ) :
    gluingCollarWarp r (-t) = gluingCollarWarp r t := by
  rw [gluingCollarWarp_eq_sinh_cosh_abs, gluingCollarWarp_eq_sinh_cosh_abs]
  simp [Real.cosh_neg, Real.sinh_neg]

/-- The curvature-controlled seam warp dominates the native coefficient on
the entire real line, using reflection on the negative half-line. -/
theorem gluingCurvatureBoundedWarp_ge_native_all
    (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCollarWarp r t ≤ gluingCurvatureBoundedWarp r δ hδ t := by
  by_cases ht : 0 ≤ t
  · by_cases hstrip : t ≤ δ
    · exact gluingCurvatureBoundedWarp_ge_native r δ hδ ht hstrip
    · have hδt : δ ≤ t := le_of_not_ge hstrip
      rw [gluingCurvatureBoundedWarp_eq_native_of_ge_strip r δ hδ hδt]
  · have htneg : t < 0 := lt_of_not_ge ht
    have hpos : 0 ≤ -t := le_of_lt (neg_pos.mpr htneg)
    have hnonneg : gluingCollarWarp r (-t) ≤ gluingCurvatureBoundedWarp r δ hδ (-t) := by
      by_cases hstrip : -t ≤ δ
      · exact gluingCurvatureBoundedWarp_ge_native r δ hδ hpos hstrip
      · have hδt : δ ≤ -t := le_of_not_ge hstrip
        rw [gluingCurvatureBoundedWarp_eq_native_of_ge_strip r δ hδ hδt]
    calc
      gluingCollarWarp r t = gluingCollarWarp r (-t) :=
        (gluingCollarWarp_even r t).symm
      _ ≤ gluingCurvatureBoundedWarp r δ hδ (-t) := hnonneg
      _ = gluingCurvatureBoundedWarp r δ hδ t :=
        gluingCurvatureBoundedWarp_even r δ hδ t

/-- The even seam warp agrees with the native metric coefficient outside the
full two-sided seam strip. -/
theorem gluingCurvatureBoundedWarp_eq_native_of_abs_ge_strip
    (r δ : ℝ) (hδ : 0 < δ) {t : ℝ} (hδt : δ ≤ |t|) :
    gluingCurvatureBoundedWarp r δ hδ t = gluingCollarWarp r t := by
  by_cases ht : 0 ≤ t
  · have hstrip : δ ≤ t := by simpa [abs_of_nonneg ht] using hδt
    exact gluingCurvatureBoundedWarp_eq_native_of_ge_strip r δ hδ hstrip
  · have htneg : t < 0 := lt_of_not_ge ht
    have hstrip : δ ≤ -t := by simpa [abs_of_neg htneg] using hδt
    calc
      gluingCurvatureBoundedWarp r δ hδ t =
          gluingCurvatureBoundedWarp r δ hδ (-t) :=
            (gluingCurvatureBoundedWarp_even r δ hδ t).symm
      _ = gluingCollarWarp r (-t) :=
        gluingCurvatureBoundedWarp_eq_native_of_ge_strip r δ hδ hstrip
      _ = gluingCollarWarp r t := gluingCollarWarp_even r t

/-- Positivity of the new warp follows globally from native positivity and
the all-line domination theorem. -/
theorem gluingCurvatureBoundedWarp_pos {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (t : ℝ) :
    0 < gluingCurvatureBoundedWarp r δ hδ t :=
  lt_of_lt_of_le (gluingCollarWarp_pos hr t)
    (gluingCurvatureBoundedWarp_ge_native_all r δ hδ t)

theorem gluingCurvatureBoundedWarp_deriv_eq_slope
    (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (gluingCurvatureBoundedWarp r δ hδ) t =
      gluingCurvatureBoundedWarpSlope r δ hδ t := by
  unfold gluingCurvatureBoundedWarp gluingCurvatureBoundedWarpSlope
  have hCdiff : Differentiable ℝ (gluingCurvatureForcingC r δ hδ) :=
    (gluingCurvatureForcingC_contDiff r δ hδ).differentiable (by norm_num)
  have hSdiff : Differentiable ℝ (gluingCurvatureForcingS r δ hδ) :=
    (gluingCurvatureForcingS_contDiff r δ hδ).differentiable (by norm_num)
  rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul _ (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [Real.deriv_cosh, Real.deriv_sinh,
    (gluingCurvatureForcingC_hasDerivAt r δ hδ t).deriv,
    (gluingCurvatureForcingS_hasDerivAt r δ hδ t).deriv]
  ring

theorem gluingCurvatureBoundedWarpSlope_deriv
    (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (gluingCurvatureBoundedWarpSlope r δ hδ) t =
      (Real.sinh r + gluingCurvatureForcingS r δ hδ δ) * Real.cosh t +
        Real.sinh t * gluingCurvatureForcingC r δ hδ t +
          Real.cosh t ^ 2 * gluingCurvatureForcing r δ hδ t -
        Real.cosh t * gluingCurvatureForcingS r δ hδ t -
          Real.sinh t ^ 2 * gluingCurvatureForcing r δ hδ t := by
  unfold gluingCurvatureBoundedWarpSlope
  have hCdiff : Differentiable ℝ (gluingCurvatureForcingC r δ hδ) :=
    (gluingCurvatureForcingC_contDiff r δ hδ).differentiable (by norm_num)
  have hSdiff : Differentiable ℝ (gluingCurvatureForcingS r δ hδ) :=
    (gluingCurvatureForcingS_contDiff r δ hδ).differentiable (by norm_num)
  rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul _ (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [Real.deriv_sinh, Real.deriv_cosh,
    (gluingCurvatureForcingC_hasDerivAt r δ hδ t).deriv,
    (gluingCurvatureForcingS_hasDerivAt r δ hδ t).deriv]
  ring

theorem gluingCurvatureBoundedWarp_deriv_sub_eq_forcing
    (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t -
      gluingCurvatureBoundedWarp r δ hδ t = gluingCurvatureForcing r δ hδ t := by
  have hfirst : deriv (gluingCurvatureBoundedWarp r δ hδ) =
      gluingCurvatureBoundedWarpSlope r δ hδ := by
    funext s
    exact gluingCurvatureBoundedWarp_deriv_eq_slope r δ hδ s
  rw [hfirst, gluingCurvatureBoundedWarpSlope_deriv r δ hδ t]
  unfold gluingCurvatureBoundedWarp
  rw [Real.cosh_sq]
  ring

theorem gluingCurvatureBoundedWarpSlope_neg
    (r δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    gluingCurvatureBoundedWarpSlope r δ hδ (-t) =
      -gluingCurvatureBoundedWarpSlope r δ hδ t := by
  unfold gluingCurvatureBoundedWarpSlope
  rw [Real.sinh_neg, Real.cosh_neg,
    gluingCurvatureForcingC_neg, gluingCurvatureForcingS_neg]
  ring

theorem gluingCurvatureBoundedWarpSlope_delta
    (r δ : ℝ) (hδ : 0 < δ) :
    gluingCurvatureBoundedWarpSlope r δ hδ δ = Real.cosh (r + δ) := by
  unfold gluingCurvatureBoundedWarpSlope
  rw [gluingCurvatureForcingC_delta]
  rw [Real.cosh_add]
  ring

/-- The ODE collar has the same exact signed radial curvature mass as the
localized smoothing: its actual curvature density is `-f''`, and integration
over the full seam strip is determined by the two matched endpoint slopes. -/
theorem gluingCurvatureBoundedWarp_signed_radial_curvature_mass
    (r δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ in Set.Icc (-δ) δ,
      -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t) =
        -2 * Real.cosh (r + δ) := by
  have hδpos : 0 < δ := hδ
  have hW : ContDiff ℝ 2 (gluingCurvatureBoundedWarp r δ hδ) := by
    have hindex : (2 : ℕ∞ω) ≤ ∞ := by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    exact (gluingCurvatureBoundedWarp_contDiff r δ hδ).of_le hindex
  have hW' : ContDiff ℝ 1 (deriv (gluingCurvatureBoundedWarp r δ hδ)) := hW.deriv'
  have hleft :
      deriv (gluingCurvatureBoundedWarp r δ hδ) (-δ) = -Real.cosh (r + δ) := by
    rw [gluingCurvatureBoundedWarp_deriv_eq_slope,
      gluingCurvatureBoundedWarpSlope_neg,
      gluingCurvatureBoundedWarpSlope_delta]
  have hright :
      deriv (gluingCurvatureBoundedWarp r δ hδ) δ = Real.cosh (r + δ) := by
    rw [gluingCurvatureBoundedWarp_deriv_eq_slope,
      gluingCurvatureBoundedWarpSlope_delta]
  have hradial :
      (∫ t : ℝ in Set.Icc (-δ) δ,
        deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t) =
          2 * Real.cosh (r + δ) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -δ ≤ δ by linarith),
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show -δ ≤ δ by linarith) hW'.continuous.continuousOn
        (fun t _ => (hW.differentiable_deriv_two t).hasDerivAt)
        (hW'.continuous_deriv_one.intervalIntegrable (-δ) δ),
      hright, hleft]
    ring
  rw [integral_neg, hradial]
  ring

theorem gluingCurvatureBoundedWarp_signed_radial_curvature_mass_Ioo
    (r δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ in Set.Ioo (-δ) δ,
      -deriv (deriv (gluingCurvatureBoundedWarp r δ hδ)) t) =
        -2 * Real.cosh (r + δ) := by
  rw [← integral_Icc_eq_integral_Ioo]
  exact gluingCurvatureBoundedWarp_signed_radial_curvature_mass r δ hδ

/-- The actual Gaussian curvature of the ODE collar metric is at most `-1`:
the forcing identity gives `f'' ≥ f`, and the already-proved global positivity
permits division by the warp. -/
theorem gluingCurvatureBoundedWarp_gaussianCurvature_le_neg_one
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (x : ℝ × ℝ) :
    gluingWarpedGaussianCurvature (gluingCurvatureBoundedWarp r δ hδ) x ≤ -1 := by
  have hpos : 0 < gluingCurvatureBoundedWarp r δ hδ x.1 :=
    gluingCurvatureBoundedWarp_pos hr hδ x.1
  have hindex : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hW : ContDiff ℝ 2 (gluingCurvatureBoundedWarp r δ hδ) :=
    (gluingCurvatureBoundedWarp_contDiff r δ hδ).of_le hindex
  have hcurv := gluingWarpedGaussianCurvature_eq hW hpos (x := x)
  rw [hcurv]
  apply (div_le_iff₀ hpos).2
  have hODE := gluingCurvatureBoundedWarp_deriv_sub_eq_forcing r δ hδ x.1
  have hforcing := gluingCurvatureForcing_nonneg r δ hδ x.1
  nlinarith [hODE]

/-- The new seam tensor dominates the native tensor on every tangent vector;
the radial coefficient is unchanged and the angular coefficient increases. -/
theorem gluingCurvatureBoundedWarp_metricForm_self_ge_native
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (t θ : ℝ) (v : Fin 2 → ℝ) :
    gluingWarpedMetricForm (fun s => gluingCollarWarp r s) (t, θ) v v ≤
      gluingWarpedMetricForm (gluingCurvatureBoundedWarp r δ hδ) (t, θ) v v := by
  rw [gluingWarpedMetricForm_apply, gluingWarpedMetricForm_apply]
  have hcoeff : gluingCollarWarp r t ^ 2 ≤
      gluingCurvatureBoundedWarp r δ hδ t ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self (gluingCollarWarp_pos hr t).le
        (gluingCurvatureBoundedWarp_ge_native_all r δ hδ t))
  nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (sq_nonneg (v 1))]

/-- Pointwise Riemannian speed increases under the collar replacement. -/
theorem gluingCurvatureBoundedWarp_speed_ge_native
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (t θ : ℝ) (v : Fin 2 → ℝ) :
    Real.sqrt (gluingWarpedMetricForm (fun s => gluingCollarWarp r s)
      (t, θ) v v) ≤
      Real.sqrt (gluingWarpedMetricForm (gluingCurvatureBoundedWarp r δ hδ)
        (t, θ) v v) :=
  Real.sqrt_le_sqrt
    (gluingCurvatureBoundedWarp_metricForm_self_ge_native hr hδ t θ v)

#print axioms gluingCurvatureForcingMass_pos
#print axioms gluingCurvatureForcing_normalized
#print axioms gluingCurvatureForcing_contDiff
#print axioms gluingCurvatureForcingC_contDiff
#print axioms gluingCurvatureBoundedWarp_contDiff
#print axioms gluingCurvatureBoundedWarp_even
#print axioms gluingCurvatureBoundedWarp_deriv_sub_eq_forcing
#print axioms gluingCurvatureBoundedWarp_signed_radial_curvature_mass
#print axioms gluingCurvatureBoundedWarp_signed_radial_curvature_mass_Ioo
#print axioms gluingCurvatureBoundedWarp_gaussianCurvature_le_neg_one
#print axioms gluingCurvatureBoundedWarp_metricForm_self_ge_native
#print axioms gluingCurvatureBoundedWarp_speed_ge_native

end SystolicGrowth
