module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainBoundedCurvatureCurvature
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Connection.ChartChristoffel
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality
public import Geometry.CurvatureTwoDimensional

@[expose] public section

/-!
# The glued metric Gram matrix in the model-space basis

The seam chart metric is diagonal in the real/imaginary coordinates, whereas
DoCarmoLib's chart Christoffel symbols use `Module.finBasis ℝ ℂ`. This file
records the actual Gram entries in that chosen basis without identifying it
with `Complex.basisOneI`.
-/

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** In a seam chart that is the chart at `α`, the chart Gram matrix of
the actual patched Riemannian metric is the warped metric evaluated on the
real/imaginary coordinates of the arbitrary chosen model-space basis vectors.
In particular, this statement does not assume that `Module.finBasis ℝ ℂ` is
`Complex.basisOneI`.
-/
theorem gluedCurvatureBoundedSeam_chartGramOnE_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (i j : Fin (Module.finrank ℝ ℂ))
    (hother : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.thinSeamCollar l) :
    Riemannian.chartGramOnE
        (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α i j y =
      (Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re +
        gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos y.re ^ 2 *
            (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let q : P.GluedCarrier := (extChartAt I α).symm y
  let e : OpenPartialHomeomorph P.GluedCarrier ℂ := P.seamAngularComplexChart k θ
  let atlasChart : atlas ℂ P.GluedCarrier := ⟨e, Or.inr ⟨k, θ, rfl⟩⟩
  have hqsource : q ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hqseam : q ∈ e.source := by
    dsimp only [e]
    rw [hchart]
    exact hqsource
  have hatlasChart : atlasChart = achart ℂ α := by
    apply Subtype.ext
    change e = chartAt ℂ α
    exact hchart
  have htriv : trivializationAt ℂ (TangentSpace I) α =
      (tangentBundleCore I P.GluedCarrier).localTriv atlasChart := by
    rw [TangentBundle.trivializationAt_eq_localTriv, hatlasChart]
    rfl
  have hqbase : q ∈ atlasChart.1.source := by
    change q ∈ e.source
    dsimp only [e]
    rw [hchart]
    exact hqsource
  have hvec : ∀ a : Fin (Module.finrank ℝ ℂ),
      Riemannian.Tensor.chartBasisVecFiber (I := I) α a q =
        ((tangentBundleCore I P.GluedCarrier).localTriv atlasChart).symmL ℝ q
          ((Module.finBasis ℝ ℂ) a) := by
    intro a
    rw [Riemannian.Tensor.chartBasisVecFiber, htriv]
    symm
    have hqtriv : q ∈ ((tangentBundleCore I P.GluedCarrier).localTriv atlasChart).baseSet := by
      rw [tangentBundleCore_localTriv_baseSet]
      exact hqbase
    exact (Bundle.Trivialization.symmL_apply
      ((tangentBundleCore I P.GluedCarrier).localTriv atlasChart)
      hqtriv
      ((Module.finBasis ℝ ℂ) a))
  have hmetric := P.gluedCurvatureBoundedSmoothMetric_seam_chart
    k θ q hqseam hother
  rw [Riemannian.chartGramOnE_def,
    Riemannian.Tensor.chartGramMatrix_apply, hvec i, hvec j]
  rw [hmetric.2 ((Module.finBasis ℝ ℂ) i) ((Module.finBasis ℝ ℂ) j)]
  rw [gluingComplexCurvatureBoundedTangentForm_apply]
  have hcoord : e q = y := by
    have hq' : q ∈ (extChartAt I α).source := by
      rw [extChartAt_source I α]
      exact hqsource
    calc
      e q = (extChartAt I α) q := by
        rw [extChartAt_coe]
        change e q = I ((chartAt ℂ α) q)
        rw [← hchart, modelWithCornersSelf_coe]
        rfl
      _ = y := (extChartAt I α).right_inv hy
  rw [hcoord]

/-- **Math.** In the seam chart, the chart Gram inner product of arbitrary
model vectors is the warped product form, not merely its matrix entries on the
chosen basis. -/
theorem gluedCurvatureBoundedSeam_chartMetricInner_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (u v : ℂ)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α y u v =
      u.re * v.re + gluingCurvatureBoundedWarp (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re ^ 2 * u.im * v.im := by
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  have hentry (i j : Fin (Module.finrank ℝ ℂ)) :
      Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
          P.gluedCurvatureBoundedSmoothRiemannianMetric α i j y =
        (Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re +
          W y.re ^ 2 * (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im := by
    exact P.gluedCurvatureBoundedSeam_chartGramOnE_eq k θ α hchart hy i j
      (fun l hl hthin => hotherClosed l hl
        (P.thinSeamCollar_subset_closedThinSeamCollar l hthin))
  have hsum_re (z : ℂ) :
      (∑ i, (Module.finBasis ℝ ℂ i).re *
        Riemannian.Geodesic.chartCoord (E := ℂ) i z) = z.re := by
    have h := congrArg Complex.reCLM ((Module.finBasis ℝ ℂ).sum_repr z)
    simpa only [map_sum, map_smul, Complex.reCLM_apply,
      Riemannian.Geodesic.chartCoord_def, smul_eq_mul, mul_comm] using h
  have hsum_im (z : ℂ) :
      (∑ i, (Module.finBasis ℝ ℂ i).im *
        Riemannian.Geodesic.chartCoord (E := ℂ) i z) = z.im := by
    have h := congrArg Complex.imCLM ((Module.finBasis ℝ ℂ).sum_repr z)
    simpa only [map_sum, map_smul, Complex.imCLM_apply,
      Riemannian.Geodesic.chartCoord_def, smul_eq_mul, mul_comm] using h
  have hsum_im' (z : ℂ) :
      (∑ i, Riemannian.Geodesic.chartCoord (E := ℂ) i z *
        (Module.finBasis ℝ ℂ i).im) = z.im := by
    calc
      _ = ∑ i, (Module.finBasis ℝ ℂ i).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) i z := by
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
      _ = z.im := hsum_im z
  have hreal :
      (∑ i, ∑ j,
        (Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re *
          Riemannian.Geodesic.chartCoord (E := ℂ) i u *
            Riemannian.Geodesic.chartCoord (E := ℂ) j v) = u.re * v.re := by
    calc
      _ = (∑ i, (Module.finBasis ℝ ℂ i).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) i u) *
          (∑ j, (Module.finBasis ℝ ℂ j).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
          calc
            _ = ∑ i, ∑ j,
                ((Module.finBasis ℝ ℂ i).re *
                  Riemannian.Geodesic.chartCoord (E := ℂ) i u) *
                ((Module.finBasis ℝ ℂ j).re *
                  Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = _ := (Fintype.sum_mul_sum _ _).symm
      _ = u.re * v.re := by rw [hsum_re u, hsum_re v]
  have himag :
      (∑ i, ∑ j,
        (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im *
          Riemannian.Geodesic.chartCoord (E := ℂ) i u *
            Riemannian.Geodesic.chartCoord (E := ℂ) j v) = u.im * v.im := by
    calc
      _ = (∑ i, (Module.finBasis ℝ ℂ i).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) i u) *
          (∑ j, (Module.finBasis ℝ ℂ j).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
          calc
            _ = ∑ i, ∑ j,
                ((Module.finBasis ℝ ℂ i).im *
                  Riemannian.Geodesic.chartCoord (E := ℂ) i u) *
                ((Module.finBasis ℝ ℂ j).im *
                  Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = _ := (Fintype.sum_mul_sum _ _).symm
      _ = u.im * v.im := by rw [hsum_im u, hsum_im v]
  have hweighted :
      (∑ i, ∑ j, W y.re ^ 2 * (Module.finBasis ℝ ℂ i).im *
        (Module.finBasis ℝ ℂ j).im *
          Riemannian.Geodesic.chartCoord (E := ℂ) i u *
            Riemannian.Geodesic.chartCoord (E := ℂ) j v) =
        W y.re ^ 2 * (u.im * v.im) := by
    calc
      _ = (∑ i, W y.re ^ 2 * ((Module.finBasis ℝ ℂ i).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) i u)) *
          (∑ j, (Module.finBasis ℝ ℂ j).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
          calc
            _ = ∑ i, ∑ j,
                (W y.re ^ 2 * ((Module.finBasis ℝ ℂ i).im *
                  Riemannian.Geodesic.chartCoord (E := ℂ) i u)) *
                ((Module.finBasis ℝ ℂ j).im *
                  Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = _ := (Fintype.sum_mul_sum _ _).symm
      _ = W y.re ^ 2 * (u.im * v.im) := by
          rw [← Finset.mul_sum, hsum_im u, hsum_im v]
          ring
  rw [Riemannian.chartMetricInner_def]
  simp_rw [hentry]
  calc
    _ = (∑ i, ∑ j,
          (Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) i u *
              Riemannian.Geodesic.chartCoord (E := ℂ) j v) +
        (∑ i, ∑ j, W y.re ^ 2 * (Module.finBasis ℝ ℂ i).im *
          (Module.finBasis ℝ ℂ j).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) i u *
              Riemannian.Geodesic.chartCoord (E := ℂ) j v) := by
          simp_rw [add_mul, Finset.sum_add_distrib]
    _ = _ := by
      rw [hreal, hweighted]
      ring

/-
/-- **Math.** The directional derivative of the seam Gram tensor, contracted
against three arbitrary model vectors, is the radial derivative of the warped
coefficient times their real/imaginary components. This is the metric-derivative
input to the coordinate Koszul formula. -/
theorem gluedCurvatureBoundedSeam_gramDirectionalDerivative_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (u v w : ℂ)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    (∑ i, ∑ j,
      (∑ a, Riemannian.Geodesic.chartCoord (E := ℂ) a u *
        Riemannian.partialDeriv (E := ℂ) a
          (Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
            P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) y) *
        Riemannian.Geodesic.chartCoord (E := ℂ) i v *
          Riemannian.Geodesic.chartCoord (E := ℂ) j w) =
      2 * gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos y.re *
        deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re *
        u.re * v.im * w.im := by
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  let c : ℝ := 2 * W y.re * deriv W y.re
  have hsum_re (z : ℂ) :
      (∑ i, (Module.finBasis ℝ ℂ i).re *
        Riemannian.Geodesic.chartCoord (E := ℂ) i z) = z.re := by
    have h := congrArg Complex.reCLM ((Module.finBasis ℝ ℂ).sum_repr z)
    simpa only [map_sum, map_smul, Complex.reCLM_apply,
      Riemannian.Geodesic.chartCoord_def, smul_eq_mul, mul_comm] using h
  have hsum_im (z : ℂ) :
      (∑ i, (Module.finBasis ℝ ℂ i).im *
        Riemannian.Geodesic.chartCoord (E := ℂ) i z) = z.im := by
    have h := congrArg Complex.imCLM ((Module.finBasis ℝ ℂ).sum_repr z)
    simpa only [map_sum, map_smul, Complex.imCLM_apply,
      Riemannian.Geodesic.chartCoord_def, smul_eq_mul, mul_comm] using h
  have hsum3 (f h z : Fin (Module.finrank ℝ ℂ) → ℝ) :
      (∑ i, ∑ j, ∑ a, f i * h j * z a) =
        (∑ i, f i) * (∑ j, h j) * (∑ a, z a) := by
    calc
      _ = ∑ i, ∑ j, f i * h j * (∑ a, z a) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        calc
          _ = ∑ a, z a * (f i * h j) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
          _ = (∑ a, z a) * (f i * h j) := (Finset.sum_mul _ _ _).symm
          _ = f i * h j * (∑ a, z a) := by ring
      _ = (∑ i, f i) * (∑ j, h j) * (∑ a, z a) := by
        calc
          _ = (∑ i, f i) * (∑ j, h j * (∑ a, z a)) := by
            calc
              _ = ∑ i, ∑ j, f i * (h j * (∑ a, z a)) := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                ring
              _ = _ := (Fintype.sum_mul_sum _ _).symm
          _ = (∑ i, f i) * ((∑ j, h j) * (∑ a, z a)) := by
            congr 1
            exact (Finset.sum_mul Finset.univ (fun j => h j) (∑ a, z a)).symm
          _ = _ := by ring
  have hscaled_re (z : ℂ) :
      (∑ a, c * Riemannian.Geodesic.chartCoord (E := ℂ) a z *
        (Module.finBasis ℝ ℂ a).re) = c * z.re := by
    calc
      _ = ∑ a, c * ((Module.finBasis ℝ ℂ a).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) a z) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              ring
      _ = c * ∑ a, (Module.finBasis ℝ ℂ a).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) a z := by
              symm
              exact Finset.mul_sum Finset.univ
                (fun a => (Module.finBasis ℝ ℂ a).re *
                  Riemannian.Geodesic.chartCoord (E := ℂ) a z) c
      _ = c * z.re := by rw [hsum_re]
  have hexpanded :
      (∑ i, ∑ j,
        (∑ a, Riemannian.Geodesic.chartCoord (E := ℂ) a u *
          Riemannian.partialDeriv (E := ℂ) a
            (Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
              P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) y) *
          Riemannian.Geodesic.chartCoord (E := ℂ) i v *
            Riemannian.Geodesic.chartCoord (E := ℂ) j w) =
        ∑ i, ∑ j, ∑ a,
          (Riemannian.Geodesic.chartCoord (E := ℂ) i v *
              (Module.finBasis ℝ ℂ i).im) *
            (Riemannian.Geodesic.chartCoord (E := ℂ) j w *
              (Module.finBasis ℝ ℂ j).im) *
            (c * Riemannian.Geodesic.chartCoord (E := ℂ) a u *
              (Module.finBasis ℝ ℂ a).re) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [P.gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
      k θ α hchart hy i j a hotherClosed]
    dsimp [c, W]
    ring
  rw [hexpanded, hsum3]
  rw [hsum_im' v, hsum_im' w, hscaled_re u]
  dsimp [c, W]
  ring
-/

/-
/-- **Math.** The actual seam-chart Christoffel contraction on arbitrary
coordinate vectors is the Levi-Civita connection of
`dx ^ 2 + W(x) ^ 2 dy ^ 2`. The proof characterizes the output by its metric
pairing, using metric compatibility, torsion-freeness, and the computed
directional Gram derivative. It does not choose or identify a preferred basis
of `ℂ` over `ℝ`. -/
theorem gluedCurvatureBoundedSeam_chartChristoffelBilin_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (u v : ℂ)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.Jacobi.chartChristoffelBilin
        (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α y u v =
      Complex.mk
        (-gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
          deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re * u.im * v.im)
        ((deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re /
          gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re) *
          (u.re * v.im + u.im * v.re)) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  let Γ : ℂ → ℂ → ℂ :=
    Riemannian.Jacobi.chartChristoffelBilin (I := I) metric α y
  let K : ℂ → ℂ → ℂ := fun a b =>
    Complex.mk (-W y.re * deriv W y.re * a.im * b.im)
      ((deriv W y.re / W y.re) * (a.re * b.im + a.im * b.re))
  let D : ℂ → ℂ → ℂ → ℝ := fun a b c =>
    ∑ i, ∑ j,
      (∑ d, Riemannian.Geodesic.chartCoord (E := ℂ) d a *
        Riemannian.partialDeriv (E := ℂ) d
          (Riemannian.chartGramOnE (I := I) metric α i j) y) *
        Riemannian.Geodesic.chartCoord (E := ℂ) i b *
          Riemannian.Geodesic.chartCoord (E := ℂ) j c
  have hbase : (extChartAt I α).symm y ∈
      (trivializationAt ℂ (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hWpos : 0 < W y.re := by
    dsimp [W]
    exact gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos y.re
  have hD (a b c : ℂ) :
      D a b c = 2 * W y.re * deriv W y.re * a.re * b.im * c.im := by
    dsimp [D]
    exact P.gluedCurvatureBoundedSeam_gramDirectionalDerivative_eq
      k θ α hchart hy a b c hotherClosed
  have hbalance (a b c : ℂ) :
      D a b c = Riemannian.Jacobi.chartMetricInner (I := I) metric α y
          (Γ a b) c +
        Riemannian.Jacobi.chartMetricInner (I := I) metric α y b (Γ a c) := by
    simpa only [D, Γ, Riemannian.Jacobi.chartChristoffelBilin_apply] using
      (Riemannian.Jacobi.chartMetricInner_gram_deriv_balance
        (I := I) metric α y a b c hbase)
  have hΓsymm (a b : ℂ) : Γ a b = Γ b a := by
    simpa only [Γ] using
      (Riemannian.Jacobi.chartChristoffelBilin_symm
        (I := I) metric α y a b)
  have hkoszul (a b c : ℂ) :
      2 * Riemannian.Jacobi.chartMetricInner (I := I) metric α y
          (Γ a b) c = D a b c + D b a c - D c a b := by
    have h₁ := hbalance a b c
    have h₂ := hbalance b a c
    have h₃ := hbalance c a b
    rw [hΓsymm b a] at h₂
    rw [hΓsymm c a, hΓsymm c b] at h₃
    rw [Riemannian.Jacobi.chartMetricInner_symm
      (I := I) metric α y (Γ a c) b] at h₃
    linarith [h₁, h₂, h₃]
  have hpair (a b c : ℂ) :
      Riemannian.Jacobi.chartMetricInner (I := I) metric α y (Γ a b) c =
        W y.re * deriv W y.re *
          (c.im * (a.re * b.im + a.im * b.re) -
            c.re * a.im * b.im) := by
    have h := hkoszul a b c
    rw [hD a b c, hD b a c, hD c a b] at h
    nlinarith [h]
  have hKpair (a b c : ℂ) :
      Riemannian.Jacobi.chartMetricInner (I := I) metric α y (K a b) c =
        W y.re * deriv W y.re *
          (c.im * (a.re * b.im + a.im * b.re) -
            c.re * a.im * b.im) := by
    rw [P.gluedCurvatureBoundedSeam_chartMetricInner_eq
      k θ α hchart hy (K a b) c hotherClosed]
    dsimp [K, W]
    field_simp [ne_of_gt hWpos]
    ring
  have hinner (a b c : ℂ) :
      Riemannian.Jacobi.chartMetricInner (I := I) metric α y (Γ a b) c =
        Riemannian.Jacobi.chartMetricInner (I := I) metric α y (K a b) c := by
    rw [hpair a b c, hKpair a b c]
  have hΓeq (a b : ℂ) : Γ a b = K a b := by
    apply Complex.ext
    · have h := hinner a b 1
      rw [P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (Γ a b) 1 hotherClosed,
          P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (K a b) 1 hotherClosed] at h
      simpa using h
    · have h := hinner a b Complex.I
      rw [P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (Γ a b) Complex.I hotherClosed,
          P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (K a b) Complex.I hotherClosed] at h
      have hmul : W y.re ^ 2 * (Γ a b).im = W y.re ^ 2 * (K a b).im := by
        simpa [Complex.I_re, Complex.I_im] using h
      exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hWpos)) hmul
  simpa only [Γ, K, W] using hΓeq u v
-/

/-- **Math.** The coordinate partial of the actual patched seam Gram entry is
the derivative of the warped coefficient in the radial component of the
chosen `Module.finBasis ℝ ℂ` vector. The neighborhood argument uses separation
from every other closed seam collar, so this remains valid at the boundary of
the active smoothing strip. -/
theorem gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (i j a : Fin (Module.finrank ℝ ℂ))
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.partialDeriv (E := ℂ) a
        (Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
          P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) y =
      2 * gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
        deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re *
        (Module.finBasis ℝ ℂ a).re * (Module.finBasis ℝ ℂ i).im *
          (Module.finBasis ℝ ℂ j).im := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let q : P.GluedCarrier := (extChartAt I α).symm y
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  have hsymmCont : ContinuousAt (extChartAt I α).symm y :=
    (continuousOn_extChartAt_symm (I := I) α).continuousAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hother : ∀ᶠ z in 𝓝 y, ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt I α).symm z ∉ P.thinSeamCollar l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : l = k
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hl).elim)
    · have hnot : q ∉ P.closedThinSeamCollar l := by
        exact hotherClosed l hl
      have hpre : ∀ᶠ z in 𝓝 y,
          (extChartAt I α).symm z ∉ P.closedThinSeamCollar l :=
        hsymmCont.preimage_mem_nhds
          ((P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hnot)
      filter_upwards [hpre] with z hz hne hthin
      exact hz (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)
  have hgram :
      Riemannian.chartGramOnE (I := I)
          P.gluedCurvatureBoundedSmoothRiemannianMetric α i j =ᶠ[𝓝 y]
        (fun z : ℂ => (Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re +
          W z.re ^ 2 * (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy, hother]
      with z hz hotherz
    exact P.gluedCurvatureBoundedSeam_chartGramOnE_eq k θ α hchart hz i j
      (fun l hne => hotherz l hne)
  have hW : ContDiff ℝ 2 W := by
    dsimp [W]
    have hindex : (2 : ℕ∞ω) ≤ ∞ := by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    exact (gluingCurvatureBoundedWarp_contDiff (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos).of_le
        hindex
  have hpow : HasDerivAt (fun t : ℝ => W t ^ 2)
      (2 * W y.re * deriv W y.re) y.re := by
    have hpow' := (hW.differentiable (by norm_num) y.re).hasDerivAt.pow 2
    change HasDerivAt (fun t : ℝ => W t ^ 2) _ _ at hpow'
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpow'
  have hcomp : HasFDerivAt (fun z : ℂ => W z.re ^ 2)
      ((2 * W y.re * deriv W y.re) • Complex.reCLM) y := by
    convert hpow.hasFDerivAt.comp y Complex.reCLM.hasFDerivAt using 1 <;>
      ext z <;>
      simp [Complex.reCLM_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, mul_comm]
  have hmodel : HasFDerivAt
      (fun z : ℂ => (Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re +
        W z.re ^ 2 * (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im)
      ((2 * W y.re * deriv W y.re * (Module.finBasis ℝ ℂ i).im *
        (Module.finBasis ℝ ℂ j).im) • Complex.reCLM) y := by
    have h := (hcomp.mul_const
      ((Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im)).add_const
        ((Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ j).re)
    convert h using 1 <;> ext z <;>
      simp [mul_assoc, mul_comm, mul_left_comm, add_comm]
  rw [Riemannian.partialDeriv, hgram.fderiv_eq, hmodel.fderiv]
  simp [W, Complex.reCLM_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

/-- **Math.** The directional derivative of the seam Gram tensor, contracted
against three arbitrary model vectors, is the radial derivative of the warped
coefficient times their real/imaginary components. This is the metric-derivative
input to the coordinate Koszul formula. -/
theorem gluedCurvatureBoundedSeam_gramDirectionalDerivative_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (u v w : ℂ)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    (∑ i, ∑ j,
      (∑ a, Riemannian.Geodesic.chartCoord (E := ℂ) a u *
        Riemannian.partialDeriv (E := ℂ) a
          (Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
            P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) y) *
        Riemannian.Geodesic.chartCoord (E := ℂ) i v *
          Riemannian.Geodesic.chartCoord (E := ℂ) j w) =
      2 * gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos y.re *
        deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re *
        u.re * v.im * w.im := by
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  let c : ℝ := 2 * W y.re * deriv W y.re
  have hsum_re (z : ℂ) :
      (∑ i, (Module.finBasis ℝ ℂ i).re *
        Riemannian.Geodesic.chartCoord (E := ℂ) i z) = z.re := by
    have h := congrArg Complex.reCLM ((Module.finBasis ℝ ℂ).sum_repr z)
    simpa only [map_sum, map_smul, Complex.reCLM_apply,
      Riemannian.Geodesic.chartCoord_def, smul_eq_mul, mul_comm] using h
  have hsum_im (z : ℂ) :
      (∑ i, (Module.finBasis ℝ ℂ i).im *
        Riemannian.Geodesic.chartCoord (E := ℂ) i z) = z.im := by
    have h := congrArg Complex.imCLM ((Module.finBasis ℝ ℂ).sum_repr z)
    simpa only [map_sum, map_smul, Complex.imCLM_apply,
      Riemannian.Geodesic.chartCoord_def, smul_eq_mul, mul_comm] using h
  have hsum_im' (z : ℂ) :
      (∑ i, Riemannian.Geodesic.chartCoord (E := ℂ) i z *
        (Module.finBasis ℝ ℂ i).im) = z.im := by
    calc
      _ = ∑ i, (Module.finBasis ℝ ℂ i).im *
            Riemannian.Geodesic.chartCoord (E := ℂ) i z := by
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
      _ = z.im := hsum_im z
  have hsum3 (f h z : Fin (Module.finrank ℝ ℂ) → ℝ) :
      (∑ i, ∑ j, ∑ a, f i * h j * z a) =
        (∑ i, f i) * (∑ j, h j) * (∑ a, z a) := by
    calc
      _ = ∑ i, ∑ j, f i * h j * (∑ a, z a) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        calc
          _ = ∑ a, z a * (f i * h j) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
          _ = (∑ a, z a) * (f i * h j) := (Finset.sum_mul _ _ _).symm
          _ = f i * h j * (∑ a, z a) := by ring
      _ = (∑ i, f i) * (∑ j, h j) * (∑ a, z a) := by
        calc
          _ = (∑ i, f i) * (∑ j, h j * (∑ a, z a)) := by
            calc
              _ = ∑ i, ∑ j, f i * (h j * (∑ a, z a)) := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                ring
              _ = _ := (Fintype.sum_mul_sum _ _).symm
          _ = (∑ i, f i) * ((∑ j, h j) * (∑ a, z a)) := by
            congr 1
            exact (Finset.sum_mul Finset.univ (fun j => h j) (∑ a, z a)).symm
          _ = _ := by ring
  have hscaled_re (z : ℂ) :
      (∑ a, c * Riemannian.Geodesic.chartCoord (E := ℂ) a z *
        (Module.finBasis ℝ ℂ a).re) = c * z.re := by
    calc
      _ = ∑ a, c * ((Module.finBasis ℝ ℂ a).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) a z) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              ring
      _ = c * ∑ a, (Module.finBasis ℝ ℂ a).re *
            Riemannian.Geodesic.chartCoord (E := ℂ) a z := by
              symm
              exact Finset.mul_sum Finset.univ
                (fun a => (Module.finBasis ℝ ℂ a).re *
                  Riemannian.Geodesic.chartCoord (E := ℂ) a z) c
      _ = c * z.re := by rw [hsum_re]
  have hexpanded :
      (∑ i, ∑ j,
        (∑ a, Riemannian.Geodesic.chartCoord (E := ℂ) a u *
          Riemannian.partialDeriv (E := ℂ) a
            (Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
              P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) y) *
          Riemannian.Geodesic.chartCoord (E := ℂ) i v *
            Riemannian.Geodesic.chartCoord (E := ℂ) j w) =
        ∑ i, ∑ j, ∑ a,
          (Riemannian.Geodesic.chartCoord (E := ℂ) i v *
              (Module.finBasis ℝ ℂ i).im) *
            (Riemannian.Geodesic.chartCoord (E := ℂ) j w *
              (Module.finBasis ℝ ℂ j).im) *
            (c * Riemannian.Geodesic.chartCoord (E := ℂ) a u *
              (Module.finBasis ℝ ℂ a).re) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [P.gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
      k θ α hchart hy i j a hotherClosed]
    dsimp [c, W]
    ring
  rw [hexpanded, hsum3]
  rw [hsum_im' v, hsum_im' w, hscaled_re u]
  dsimp [c, W]
  ring

/-- **Math.** The actual seam-chart Christoffel contraction on arbitrary
coordinate vectors is the Levi-Civita connection of
`dx ^ 2 + W(x) ^ 2 dy ^ 2`. The proof characterizes the output by its metric
pairing, using metric compatibility, torsion-freeness, and the computed
directional Gram derivative. It does not choose or identify a preferred basis
of `ℂ` over `ℝ`. -/
theorem gluedCurvatureBoundedSeam_chartChristoffelBilin_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (u v : ℂ)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.Jacobi.chartChristoffelBilin
        (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α y u v =
      Complex.mk
        (-gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
          deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re * u.im * v.im)
        ((deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re /
          gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re) *
          (u.re * v.im + u.im * v.re)) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  letI : NeZero (Module.finrank ℝ ℂ) := ⟨by simp [Complex.finrank_real_complex]⟩
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  let Γ : ℂ → ℂ → ℂ := fun a b =>
    Riemannian.Jacobi.chartChristoffelBilin (I := I) metric α y a b
  let K : ℂ → ℂ → ℂ := fun a b =>
    Complex.mk (-W y.re * deriv W y.re * a.im * b.im)
      ((deriv W y.re / W y.re) * (a.re * b.im + a.im * b.re))
  let D : ℂ → ℂ → ℂ → ℝ := fun a b c =>
    ∑ i, ∑ j,
      (∑ d, Riemannian.Geodesic.chartCoord (E := ℂ) d a *
        Riemannian.partialDeriv (E := ℂ) d
          (Riemannian.chartGramOnE (I := I) metric α i j) y) *
        Riemannian.Geodesic.chartCoord (E := ℂ) i b *
          Riemannian.Geodesic.chartCoord (E := ℂ) j c
  have hbase : (extChartAt I α).symm y ∈
      (trivializationAt ℂ (TangentSpace I) α).baseSet := by
    rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hWpos : 0 < W y.re := by
    dsimp [W]
    exact gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos y.re
  have hD (a b c : ℂ) :
      D a b c = 2 * W y.re * deriv W y.re * a.re * b.im * c.im := by
    dsimp [D]
    exact P.gluedCurvatureBoundedSeam_gramDirectionalDerivative_eq
      k θ α hchart hy a b c hotherClosed
  have hbalance (a b c : ℂ) :
      D a b c = Riemannian.chartMetricInner (I := I) metric α y
          (Γ a b) c +
        Riemannian.chartMetricInner (I := I) metric α y b (Γ a c) := by
    simpa only [D, Γ, Riemannian.Jacobi.chartChristoffelBilin_apply] using
      (Riemannian.chartMetricInner_gram_deriv_balance
        (I := I) metric α y a b c hbase)
  have hΓsymm (a b : ℂ) : Γ a b = Γ b a := by
    simpa only [Γ] using
      (Riemannian.Jacobi.chartChristoffelBilin_symm
        (I := I) metric α y a b)
  have hkoszul (a b c : ℂ) :
      2 * Riemannian.chartMetricInner (I := I) metric α y (Γ a b) c =
        D a b c + D b a c - D c a b := by
    have h₁ := hbalance a b c
    have h₂ := hbalance b a c
    have h₃ := hbalance c a b
    rw [hΓsymm b a] at h₂
    rw [hΓsymm c a, hΓsymm c b] at h₃
    rw [Riemannian.chartMetricInner_symm (I := I) metric α y (Γ a c) b] at h₃
    linarith [h₁, h₂, h₃]
  have hpair (a b c : ℂ) :
      Riemannian.chartMetricInner (I := I) metric α y (Γ a b) c =
        W y.re * deriv W y.re *
          (c.im * (a.re * b.im + a.im * b.re) -
            c.re * a.im * b.im) := by
    have h := hkoszul a b c
    rw [hD a b c, hD b a c, hD c a b] at h
    nlinarith [h]
  have hKpair (a b c : ℂ) :
      Riemannian.chartMetricInner (I := I) metric α y (K a b) c =
        W y.re * deriv W y.re *
          (c.im * (a.re * b.im + a.im * b.re) -
            c.re * a.im * b.im) := by
    rw [P.gluedCurvatureBoundedSeam_chartMetricInner_eq
      k θ α hchart hy (K a b) c hotherClosed]
    dsimp [K, W]
    field_simp [ne_of_gt hWpos]
    ring
  have hinner (a b c : ℂ) :
      Riemannian.chartMetricInner (I := I) metric α y (Γ a b) c =
        Riemannian.chartMetricInner (I := I) metric α y (K a b) c := by
    rw [hpair a b c, hKpair a b c]
  have hΓeq (a b : ℂ) : Γ a b = K a b := by
    apply Complex.ext
    · have h := hinner a b 1
      rw [P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (Γ a b) 1 hotherClosed,
          P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (K a b) 1 hotherClosed] at h
      simpa using h
    · have h := hinner a b Complex.I
      rw [P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (Γ a b) Complex.I hotherClosed,
          P.gluedCurvatureBoundedSeam_chartMetricInner_eq
            k θ α hchart hy (K a b) Complex.I hotherClosed] at h
      have hmul : W y.re ^ 2 * (Γ a b).im = W y.re ^ 2 * (K a b).im := by
        simpa [Complex.I_re, Complex.I_im] using h
      exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hWpos)) hmul
  simpa only [Γ, K, W] using hΓeq u v

/-- **Math.** In the real and angular coordinate directions, the seam-chart
curvature of the actual patched metric is the warped-product value
`R(∂x, ∂y)∂y = -W W'' ∂x`. The pointwise connection formula is transported to
a neighborhood before differentiating, so the result also holds at the edge
of the smoothing collar. -/
theorem gluedCurvatureBoundedSeam_chartCurvature_real_angular
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.Jacobi.chartCurvature
        (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α y 1 Complex.I Complex.I =
      Complex.mk
        (-gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
          deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re) 0 := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  letI : NeZero (Module.finrank ℝ ℂ) := ⟨by simp [Complex.finrank_real_complex]⟩
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  let F : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    Riemannian.Jacobi.chartChristoffelBilin (I := I) metric α
  let q : P.GluedCarrier := (extChartAt I α).symm y
  have hyInterior : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy
  have hFdiff : DifferentiableAt ℝ F y := by
    dsimp [F, metric]
    exact Riemannian.Jacobi.differentiableAt_chartChristoffelBilin
      (I := I) P.gluedCurvatureBoundedSmoothRiemannianMetric α hyInterior
  have hfirst (a : ℂ) :
      fderiv ℝ (fun z : ℂ => F z a) y = (fderiv ℝ F y).flip a := by
    rw [fderiv_clm_apply hFdiff (differentiableAt_const a)]
    ext d b
    simp
  have hFaDiff (a : ℂ) : DifferentiableAt ℝ (fun z : ℂ => F z a) y :=
    hFdiff.clm_apply (differentiableAt_const a)
  have hsecond (a b : ℂ) :
      fderiv ℝ (fun z : ℂ => F z a b) y =
        (fderiv ℝ (fun z : ℂ => F z a) y).flip b := by
    rw [fderiv_clm_apply (hFaDiff a) (differentiableAt_const b)]
    ext d
    simp
  have hFderiv_apply (a b d : ℂ) :
      fderiv ℝ (fun z : ℂ => F z a b) y d = fderiv ℝ F y d a b := by
    calc
      _ = (fderiv ℝ (fun z : ℂ => F z a) y d) b := by
        rw [hsecond a b]
        simp
      _ = (fderiv ℝ F y d a) b := by
        rw [hfirst a]
        simp
  have hsymmCont : ContinuousAt (extChartAt I α).symm y :=
    (continuousOn_extChartAt_symm (I := I) α).continuousAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hotherNear : ∀ᶠ z in 𝓝 y, ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt I α).symm z ∉ P.closedThinSeamCollar l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : l = k
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hl).elim)
    · have hnot : q ∉ P.closedThinSeamCollar l := hotherClosed l hl
      filter_upwards [hsymmCont.preimage_mem_nhds
        ((P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hnot)]
        with z hz hne
      exact hz
  have htarget : ∀ᶠ z in 𝓝 y, z ∈ (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).mem_nhds hy
  have hII : (fun z : ℂ => F z Complex.I Complex.I) =ᶠ[𝓝 y]
      (fun z => Complex.ofReal (-(W z.re * deriv W z.re))) := by
    filter_upwards [htarget, hotherNear] with z hz hnot
    have h := P.gluedCurvatureBoundedSeam_chartChristoffelBilin_eq
      k θ α hchart hz Complex.I Complex.I (fun l hl => hnot l hl)
    simpa [F, W, Complex.I_re, Complex.I_im, Complex.ofReal] using h
  have h1I : (fun z : ℂ => F z 1 Complex.I) =ᶠ[𝓝 y]
      (fun z => Complex.ofReal (deriv W z.re / W z.re) * Complex.I) := by
    filter_upwards [htarget, hotherNear] with z hz hnot
    have h := P.gluedCurvatureBoundedSeam_chartChristoffelBilin_eq
      k θ α hchart hz 1 Complex.I (fun l hl => hnot l hl)
    have h' : F z 1 Complex.I = Complex.mk 0 (deriv W z.re / W z.re) := by
      simpa [F, W, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im] using h
    calc
      F z 1 Complex.I = Complex.mk 0 (deriv W z.re / W z.re) := h'
      _ = Complex.ofReal (deriv W z.re / W z.re) * Complex.I := by
        apply Complex.ext <;> simp [Complex.ofReal, Complex.I_re, Complex.I_im]
  have hW : ContDiff ℝ ∞ W := by
    dsimp [W]
    exact gluingCurvatureBoundedWarp_contDiff (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  have hWderiv : HasDerivAt W (deriv W y.re) y.re :=
    (hW.differentiable (by norm_num) y.re).hasDerivAt
  have hW' : ContDiff ℝ ∞ (deriv W) := hW.deriv'
  have hWderiv' : HasDerivAt (deriv W) (deriv (deriv W) y.re) y.re :=
    (hW'.differentiable (by norm_num) y.re).hasDerivAt
  have hprod : HasDerivAt (fun t : ℝ => -(W t * deriv W t))
      (-(deriv W y.re ^ 2 + W y.re * deriv (deriv W) y.re)) y.re := by
    convert (hWderiv.mul hWderiv').neg using 1
    all_goals try rfl
    all_goals ring_nf
  have hprodC : HasFDerivAt
      (fun z : ℂ => Complex.ofReal (-(W z.re * deriv W z.re)))
      (Complex.ofRealCLM.comp
        ((-(deriv W y.re ^ 2 + W y.re * deriv (deriv W) y.re)) • Complex.reCLM)) y := by
    have hcomp := hprod.hasFDerivAt.comp y Complex.reCLM.hasFDerivAt
    convert Complex.ofRealCLM.hasFDerivAt.comp y hcomp using 1
    all_goals
      first
      | rfl
      | (ext z; simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]; ring)
  have hIIderiv :
      fderiv ℝ (fun z : ℂ => F z Complex.I Complex.I) y 1 =
        Complex.ofReal (-(deriv W y.re ^ 2 + W y.re * deriv (deriv W) y.re)) := by
    rw [hII.fderiv_eq]
    rw [hprodC.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have hquot : HasDerivAt (fun t : ℝ => deriv W t / W t)
      ((deriv (deriv W) y.re * W y.re - deriv W y.re * deriv W y.re) /
        W y.re ^ 2) y.re := hWderiv'.div hWderiv (ne_of_gt
          (gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos y.re))
  have hquotC : HasFDerivAt
      (fun z : ℂ => Complex.ofReal (deriv W z.re / W z.re))
      (Complex.ofRealCLM.comp
        (((deriv (deriv W) y.re * W y.re - deriv W y.re * deriv W y.re) /
          W y.re ^ 2) • Complex.reCLM)) y := by
    have hcomp := hquot.hasFDerivAt.comp y Complex.reCLM.hasFDerivAt
    convert Complex.ofRealCLM.hasFDerivAt.comp y hcomp using 1
    all_goals
      first
      | rfl
      | (ext z; simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]; ring)
  have hquotIC := hquotC.mul_const Complex.I
  have h1Ideriv : fderiv ℝ (fun z : ℂ => F z 1 Complex.I) y Complex.I = 0 := by
    rw [h1I.fderiv_eq, hquotIC.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have hAt (a b : ℂ) : F y a b =
      Complex.mk (-W y.re * deriv W y.re * a.im * b.im)
        ((deriv W y.re / W y.re) * (a.re * b.im + a.im * b.re)) :=
    P.gluedCurvatureBoundedSeam_chartChristoffelBilin_eq
      k θ α hchart hy a b hotherClosed
  rw [Riemannian.Jacobi.chartCurvature_def,
    Riemannian.Jacobi.christoffelCurvature]
  rw [← hFderiv_apply Complex.I Complex.I 1,
    ← hFderiv_apply 1 Complex.I Complex.I,
    hIIderiv, h1Ideriv,
    hAt 1 (F y Complex.I Complex.I), hAt Complex.I (F y 1 Complex.I),
    hAt Complex.I Complex.I, hAt 1 Complex.I]
  apply Complex.ext
  · simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    rw [← Complex.ofReal_pow]
    simp only [Complex.ofReal_re]
    simp only [W]
    field_simp [ne_of_gt (gluingCurvatureBoundedWarp_pos P.radius_pos
      P.thinSeamWidth_pos y.re)]
    ring
  · simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      pow_two, Complex.mul_im]

/-- **Math.** The intrinsic Levi-Civita curvature form of the actual patched
metric, evaluated on its radial/angular chart frame, is the warped curvature
numerator `W W''`. This transfers the chart-Christoffel calculation through
the chart-frame curvature bridge. -/
theorem gluedCurvatureBoundedSeam_curvatureFormAt_radial_angular
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p : P.GluedCarrier := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    (Riemannian.RiemannianMetric.leviCivitaConnection
      (I := I) (M := P.GluedCarrier) metric).curvatureFormAt metric p
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p (1 : ℂ))
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p Complex.I)
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p Complex.I)
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p (1 : ℂ)) =
        gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
        deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p : P.GluedCarrier := (extChartAt I α).symm y
  let τ := trivializationAt ℂ (TangentSpace I) α
  have hpSource : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := by
    simpa [τ] using hpSource
  have hframe (v : ℂ) :
      (∑ i : Fin (Module.finrank ℝ ℂ),
        Riemannian.Geodesic.chartCoord (E := ℂ) i v •
          Riemannian.Tensor.chartBasisVecFiber (I := I) α i p) =
        τ.symmL ℝ p v := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ ℂ),
          Riemannian.Geodesic.chartCoord (E := ℂ) i v •
            τ.symmL ℝ p (Module.finBasis ℝ ℂ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Riemannian.Tensor.chartBasisVecFiber]
          exact congrArg (fun z => Riemannian.Geodesic.chartCoord (E := ℂ) i v • z)
            ((Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase
              (Module.finBasis ℝ ℂ i)).symm)
      _ = τ.symmL ℝ p
          (∑ i : Fin (Module.finrank ℝ ℂ),
            Riemannian.Geodesic.chartCoord (E := ℂ) i v • Module.finBasis ℝ ℂ i) := by
          simp only [map_sum, map_smul]
      _ = τ.symmL ℝ p v := by
          congr 1
          simpa only [Riemannian.Geodesic.chartCoord_def] using
            (Module.finBasis ℝ ℂ).sum_repr v
  have hbridge := Riemannian.Jacobi.curvatureFormAt_chartFrame
    (E := ℂ) (H := ℂ) (I := I) (M := P.GluedCarrier)
    (g := P.gluedCurvatureBoundedSmoothRiemannianMetric)
    (α := α) (p := p) hpSource (1 : ℂ) Complex.I Complex.I (1 : ℂ)
  rw [hframe 1, hframe Complex.I] at hbridge
  have hcoord : (extChartAt I α) p = y := (extChartAt I α).right_inv hy
  rw [hcoord] at hbridge
  rw [P.gluedCurvatureBoundedSeam_chartCurvature_real_angular
    k θ α hchart hy hotherClosed] at hbridge
  have hchartInner := P.gluedCurvatureBoundedSeam_chartMetricInner_eq
    k θ α hchart hy
    (Complex.mk
      (-gluingCurvatureBoundedWarp (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
        deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re) 0)
    (1 : ℂ) hotherClosed
  change (Riemannian.RiemannianMetric.leviCivitaConnection
      P.gluedCurvatureBoundedSmoothRiemannianMetric).curvatureFormAt
      P.gluedCurvatureBoundedSmoothRiemannianMetric p
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I)
      (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p (1 : ℂ)) =
    gluingCurvatureBoundedWarp (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
        deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re
  calc
    _ = -Riemannian.chartMetricInner
          P.gluedCurvatureBoundedSmoothRiemannianMetric α y
          (Complex.mk
            (-gluingCurvatureBoundedWarp (gluingRadius C g)
              (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
              deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
                (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re) 0)
          1 := hbridge
    _ = gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
        deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re := by
      rw [hchartInner]
      simp [Complex.one_re, Complex.one_im]

/-- **Math.** The actual Riemannian sectional curvature of the radial/angular
chart frame is `-W''/W`. The area denominator is computed from the patched
metric itself, not from a coordinate model assumed to be orthonormal. -/
theorem gluedCurvatureBoundedSeam_sectionalCurvature_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p : P.GluedCarrier := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    let τ := trivializationAt ℂ (TangentSpace I) α
    letI : Bundle.RiemannianBundle
        (fun q : P.GluedCarrier => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    Riemannian.sectionalCurvature
      ((Riemannian.RiemannianMetric.leviCivitaConnection
        (I := I) (M := P.GluedCarrier) metric).curvatureFormAt metric p)
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I) =
        -(deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re /
          gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p : P.GluedCarrier := (extChartAt I α).symm y
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let τ := trivializationAt ℂ (TangentSpace I) α
  let X : TangentSpace I p := τ.symmL ℝ p (1 : ℂ)
  let Y : TangentSpace I p := τ.symmL ℝ p Complex.I
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  letI : Bundle.RiemannianBundle
      (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  have hpSource : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := by
    simpa [τ] using hpSource
  have hcoord : (extChartAt I α) p = y := (extChartAt I α).right_inv hy
  have hmetric (a b : ℂ) :
      Riemannian.RiemannianMetric.metricInner metric p
          (τ.symmL ℝ p a) (τ.symmL ℝ p b) =
        Riemannian.chartMetricInner metric α y a b := by
    calc
      Riemannian.RiemannianMetric.metricInner metric p
          (τ.symmL ℝ p a) (τ.symmL ℝ p b) =
          Riemannian.RiemannianMetric.metricInner metric p
            (τ.symm p a) (τ.symm p b) := by
        rw [Bundle.Trivialization.symmL_apply τ hpBase a,
          Bundle.Trivialization.symmL_apply τ hpBase b]
      _ = Riemannian.chartMetricInner metric α y a b := by
        have h := Riemannian.chartMetricInner_extChartAt_eq_metricInner
          (I := I) metric α hpSource a b
        rw [hcoord] at h
        exact h.symm
  have hchartInner (a b : ℂ) :
      Riemannian.chartMetricInner metric α y a b =
        a.re * b.re + W y.re ^ 2 * a.im * b.im := by
    simpa only [W, metric] using P.gluedCurvatureBoundedSeam_chartMetricInner_eq
      k θ α hchart hy a b hotherClosed
  have hxx : inner ℝ X X = 1 := by
    change Riemannian.RiemannianMetric.metricInner metric p
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p (1 : ℂ)) = 1
    rw [hmetric 1 1, hchartInner 1 1]
    simp [Complex.one_re, Complex.one_im]
  have hyy : inner ℝ Y Y = W y.re ^ 2 := by
    change Riemannian.RiemannianMetric.metricInner metric p
      (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p Complex.I) = W y.re ^ 2
    rw [hmetric Complex.I Complex.I, hchartInner Complex.I Complex.I]
    simp [Complex.I_re, Complex.I_im]
  have hxy : inner ℝ X Y = 0 := by
    change Riemannian.RiemannianMetric.metricInner metric p
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I) = 0
    rw [hmetric 1 Complex.I, hchartInner 1 Complex.I]
    simp [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  have hwedge : Riemannian.wedgeSq X Y = W y.re ^ 2 := by
    rw [Riemannian.wedgeSq, hxx, hyy, hxy]
    ring
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection
    (I := I) (M := P.GluedCarrier) metric
  have hLC : connection.IsLeviCivita metric :=
    connection.isLeviCivita_of_koszulDual metric
      (fun A B Z q =>
        Riemannian.RiemannianMetric.koszulDualSection_dual metric A B Z q)
  have hB := connection.isAlgCurvatureForm_curvatureFormAt metric hLC p
  have hform : connection.curvatureFormAt metric p X Y Y X =
      W y.re * deriv (deriv W) y.re := by
    simpa [I, p, metric, τ, X, Y, W] using
      P.gluedCurvatureBoundedSeam_curvatureFormAt_radial_angular
        k θ α hchart hy hotherClosed
  have hnum : connection.curvatureFormAt metric p X Y X Y =
      -(W y.re * deriv (deriv W) y.re) := by
    have h := hB.antisymm₃₄ X Y X Y
    rw [hform] at h
    exact h
  change connection.curvatureFormAt metric p X Y X Y / Riemannian.wedgeSq X Y =
    -(deriv (deriv W) y.re / W y.re)
  rw [hnum, hwedge]
  have hWpos : 0 < W y.re := by
    simpa [W] using gluingCurvatureBoundedWarp_pos P.radius_pos
      P.thinSeamWidth_pos y.re
  have hWne : W y.re ≠ 0 := ne_of_gt hWpos
  field_simp [hWne]

/-- **Math.** The normalized intrinsic sectional curvature of the actual
patched seam metric is at most `-1`, including the smoothing boundary. -/
theorem gluedCurvatureBoundedSeam_sectionalCurvature_le_neg_one
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p : P.GluedCarrier := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    let τ := trivializationAt ℂ (TangentSpace I) α
    letI : Bundle.RiemannianBundle
        (fun q : P.GluedCarrier => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    Riemannian.sectionalCurvature
      ((Riemannian.RiemannianMetric.leviCivitaConnection
        (I := I) (M := P.GluedCarrier) metric).curvatureFormAt metric p)
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I) ≤ -1 := by
  dsimp only
  rw [P.gluedCurvatureBoundedSeam_sectionalCurvature_eq k θ α hchart hy hotherClosed]
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  change -(deriv (deriv W) y.re / W y.re) ≤ -1
  have hWpos : 0 < W y.re :=
    gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos y.re
  have hODE := gluingCurvatureBoundedWarp_deriv_sub_eq_forcing
    (gluingRadius C g) (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re
  have hforcing := gluingCurvatureForcing_nonneg
    (gluingRadius C g) (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re
  have hratio : 1 ≤ deriv (deriv W) y.re / W y.re := by
    apply (le_div_iff₀ hWpos).2
    dsimp only [W]
    linarith
  linarith

/-- **Math.** The seam curvature bound controls the actual Levi-Civita
curvature operator on every pair of tangent vectors, with its full Gram-area
factor. In particular it applies to unit-speed geodesics and their normal
Jacobi fields, without assuming that those vectors are a coordinate frame. -/
theorem gluedCurvatureBoundedSeam_curvatureOperatorAt_lower_bound
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p : P.GluedCarrier := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    ∀ u v : TangentSpace I p,
      Riemannian.RiemannianMetric.metricInner metric p u u *
          Riemannian.RiemannianMetric.metricInner metric p v v -
        Riemannian.RiemannianMetric.metricInner metric p u v *
          Riemannian.RiemannianMetric.metricInner metric p u v ≤
        Riemannian.RiemannianMetric.metricInner metric p
          ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
            p u v v) u := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p : P.GluedCarrier := (extChartAt I α).symm y
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let τ := trivializationAt ℂ (TangentSpace I) α
  letI : Bundle.RiemannianBundle
      (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  have hpSource : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := by
    simpa [τ] using hpSource
  let e : Module.Basis (Fin 2) ℝ (TangentSpace I p) :=
    Complex.basisOneI.map (τ.continuousLinearEquivAt ℝ p hpBase).symm.toLinearEquiv
  have he0 : e 0 = τ.symmL ℝ p (1 : ℂ) := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI,
      Matrix.cons_val_zero, ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have he1 : e 1 = τ.symmL ℝ p Complex.I := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI,
      Matrix.cons_val_one, Matrix.cons_val_zero,
      ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have hlin : LinearIndependent ℝ ![e 0, e 1] := by
    convert e.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  have harea : 0 < Riemannian.wedgeSq (e 0) (e 1) :=
    (Riemannian.wedgeSq_pos_iff_linearIndependent (e 0) (e 1)).2 hlin
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection
    (I := I) (M := P.GluedCarrier) metric
  have hsectional :
      Riemannian.sectionalCurvature (connection.curvatureFormAt metric p)
        (e 0) (e 1) ≤ -1 := by
    rw [he0, he1]
    exact P.gluedCurvatureBoundedSeam_sectionalCurvature_le_neg_one
      k θ α hchart hy hotherClosed
  dsimp only
  intro u v
  have hbase := (div_le_iff₀ harea).mp hsectional
  have h := Riemannian.curvatureOperatorAt_pair_lower_bound_of_basis_pair
    (I := I) metric p e (-1) hbase u v
  simpa only [neg_neg, one_mul] using h

/-- **Math.** At every point of a closed smoothing collar, the canonical
chart is the corresponding seam chart. Its intrinsic curvature inequality
therefore holds on the actual tangent space at that point. -/
theorem gluedCurvatureBounded_curvatureOperatorAt_lower_bound_of_mem_closedThinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (k : Fin (n - 1)) (hb : b ∈ P.closedThinSeamCollar k) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    ∀ u v : TangentSpace I b,
      Riemannian.RiemannianMetric.metricInner metric b u u *
          Riemannian.RiemannianMetric.metricInner metric b v v -
        Riemannian.RiemannianMetric.metricInner metric b u v *
          Riemannian.RiemannianMetric.metricInner metric b u v ≤
        Riemannian.RiemannianMetric.metricInner metric b
          ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
            b u v v) u := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let y : ℂ := (extChartAt I b) b
  have hy : y ∈ (extChartAt I b).target := mem_extChartAt_target b
  have hpoint : (extChartAt I b).symm y = b :=
    (extChartAt I b).left_inv (mem_extChartAt_source b)
  obtain ⟨θ, hchart⟩ :=
    P.gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar b k hb
  have hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt I b).symm y ∉ P.closedThinSeamCollar l := by
    intro l hl
    rw [hpoint]
    intro hbl
    exact Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) hbl hb
  have h := P.gluedCurvatureBoundedSeam_curvatureOperatorAt_lower_bound
    k θ b hchart.symm hy hotherClosed
  dsimp only [I, y] at h
  rw [extChartAt_to_inv] at h
  exact h

/-- **Math.** The second chart partial of the actual seam Gram entry is the
second radial derivative of the warp, multiplied by the radial components of
both differentiating basis vectors. This is the second-order metric input for
the chart-Christoffel curvature formula. -/
theorem gluedCurvatureBoundedSeam_secondPartialDeriv_chartGramOnE_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (i j a b : Fin (Module.finrank ℝ ℂ))
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.partialDeriv (E := ℂ) b
        (fun z => Riemannian.partialDeriv (E := ℂ) a
          (Riemannian.chartGramOnE (I := modelWithCornersSelf ℝ ℂ)
            P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) z) y =
      2 * (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re ^ 2 +
        gluingCurvatureBoundedWarp (gluingRadius C g)
          (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
          deriv (deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
            (gluingThinSeamWidth C g) P.thinSeamWidth_pos)) y.re) *
        (Module.finBasis ℝ ℂ b).re * (Module.finBasis ℝ ℂ a).re *
        (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let q : P.GluedCarrier := (extChartAt I α).symm y
  let W : ℝ → ℝ := gluingCurvatureBoundedWarp (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  let A : ℝ := (Module.finBasis ℝ ℂ a).re *
    (Module.finBasis ℝ ℂ i).im * (Module.finBasis ℝ ℂ j).im
  let H : ℝ → ℝ := fun t => 2 * W t * deriv W t
  have hsymmCont : ContinuousAt (extChartAt I α).symm y :=
    (continuousOn_extChartAt_symm (I := I) α).continuousAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hotherNear : ∀ᶠ z in 𝓝 y, ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt I α).symm z ∉ P.closedThinSeamCollar l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : l = k
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hl).elim)
    · have hnot : q ∉ P.closedThinSeamCollar l := hotherClosed l hl
      filter_upwards [hsymmCont.preimage_mem_nhds
        ((P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hnot)]
        with z hz hne
      exact hz
  have hfirst :
      (fun z : ℂ => Riemannian.partialDeriv (E := ℂ) a
          (Riemannian.chartGramOnE (I := I)
            P.gluedCurvatureBoundedSmoothRiemannianMetric α i j) z) =ᶠ[𝓝 y]
        (fun z : ℂ => H z.re * A) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy,
      hotherNear] with z hz hnot
    have hpart := P.gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
      k θ α hchart hz i j a (fun l hl => hnot l hl)
    simpa [W, H, A, mul_assoc, mul_comm, mul_left_comm] using hpart
  have hW : ContDiff ℝ ∞ W := by
    dsimp [W]
    exact gluingCurvatureBoundedWarp_contDiff (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos
  have hW' : ContDiff ℝ ∞ (deriv W) := hW.deriv'
  have hH : HasDerivAt H
      (2 * (deriv W y.re * deriv W y.re + W y.re * deriv (deriv W) y.re)) y.re := by
    have hprod :=
      ((hW.differentiable (by norm_num) y.re).hasDerivAt).mul
        ((hW'.differentiable (by norm_num) y.re).hasDerivAt)
    dsimp [H]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod.const_mul 2
  have hcomp : HasFDerivAt (fun z : ℂ => H z.re)
      ((2 * (deriv W y.re * deriv W y.re + W y.re * deriv (deriv W) y.re)) •
        Complex.reCLM) y := by
    convert hH.hasFDerivAt.comp y Complex.reCLM.hasFDerivAt using 1 <;>
      ext z <;>
      simp [Complex.reCLM_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  have hmodel : HasFDerivAt (fun z : ℂ => H z.re * A)
      ((2 * (deriv W y.re * deriv W y.re + W y.re * deriv (deriv W) y.re) * A) •
        Complex.reCLM) y := by
    have h := hcomp.mul_const A
    convert h using 1 <;> ext z <;>
      simp [smul_eq_mul, mul_assoc, mul_comm]
  rw [Riemannian.partialDeriv, hfirst.fderiv_eq, hmodel.fderiv]
  simp only [W, A, smul_apply, Complex.reCLM_apply, smul_eq_mul]
  ring

/-- **Math.** The actual seam chart-Christoffel coefficient is the inverse
Gram contraction of the explicit first Gram derivatives in the arbitrary
model-space basis. -/
theorem gluedCurvatureBoundedSeam_chartChristoffel_eq
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (α : P.GluedCarrier)
    (hchart : P.seamAngularComplexChart k θ = chartAt ℂ α)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (i j m : Fin (Module.finrank ℝ ℂ))
    (hotherClosed : ∀ l : Fin (n - 1), l ≠ k →
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar l) :
    Riemannian.chartChristoffel (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α i j m y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ ℂ),
        Riemannian.Tensor.chartInvGramMatrix (I := modelWithCornersSelf ℝ ℂ)
          P.gluedCurvatureBoundedSmoothRiemannianMetric α
          ((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y) m l *
          (2 * gluingCurvatureBoundedWarp (gluingRadius C g)
              (gluingThinSeamWidth C g) P.thinSeamWidth_pos y.re *
            deriv (gluingCurvatureBoundedWarp (gluingRadius C g)
              (gluingThinSeamWidth C g) P.thinSeamWidth_pos) y.re *
            ((Module.finBasis ℝ ℂ i).re * (Module.finBasis ℝ ℂ l).im *
                (Module.finBasis ℝ ℂ j).im +
              (Module.finBasis ℝ ℂ j).re * (Module.finBasis ℝ ℂ l).im *
                (Module.finBasis ℝ ℂ i).im -
              (Module.finBasis ℝ ℂ l).re * (Module.finBasis ℝ ℂ i).im *
                (Module.finBasis ℝ ℂ j).im)) := by
  rw [Riemannian.chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [P.gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
      k θ α hchart hy l j i hotherClosed,
    P.gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
      k θ α hchart hy l i j hotherClosed,
    P.gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
      k θ α hchart hy i j l hotherClosed]
  ring

#print axioms gluedCurvatureBoundedSeam_chartGramOnE_eq
#print axioms gluedCurvatureBoundedSeam_partialDeriv_chartGramOnE_eq
#print axioms gluedCurvatureBoundedSeam_secondPartialDeriv_chartGramOnE_eq
#print axioms gluedCurvatureBoundedSeam_chartChristoffel_eq
#print axioms gluedCurvatureBoundedSeam_chartMetricInner_eq
#print axioms gluedCurvatureBoundedSeam_gramDirectionalDerivative_eq
#print axioms gluedCurvatureBoundedSeam_chartChristoffelBilin_eq
#print axioms gluedCurvatureBoundedSeam_chartCurvature_real_angular
#print axioms gluedCurvatureBoundedSeam_curvatureFormAt_radial_angular
#print axioms gluedCurvatureBoundedSeam_sectionalCurvature_eq
#print axioms gluedCurvatureBoundedSeam_sectionalCurvature_le_neg_one
#print axioms gluedCurvatureBoundedSeam_curvatureOperatorAt_lower_bound
#print axioms
  gluedCurvatureBounded_curvatureOperatorAt_lower_bound_of_mem_closedThinSeamCollar

end

end SystolicGrowth.ExerciseGluingPreparation
