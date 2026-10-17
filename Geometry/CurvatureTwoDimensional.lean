module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Connection.CurvaturePointwise
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

/-!
# Curvature sign reduction in dimension two

An algebraic curvature form on a two-dimensional real vector space is
determined by its value on one basis bivector.  This is the linear-algebra
step needed to turn a local Gaussian-curvature calculation into a curvature
sign statement for arbitrary tangent vectors.
-/

noncomputable section

namespace Riemannian.IsAlgCurvatureForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : V → V → V → V → ℝ}

/-- **Math.** In dimension two, the diagonal curvature value on any pair is a
nonnegative square multiple of the value on a chosen basis pair. -/
theorem diag_eq_det_sq_mul_basis (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V) (x y : V) :
    B x y x y =
      (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) ^ 2 *
        B (e 0) (e 1) (e 0) (e 1) := by
  let X := e.repr x 0 • e 0 + e.repr x 1 • e 1
  let Y := e.repr y 0 • e 0 + e.repr y 1 • e 1
  have hx : X = x := by
    dsimp [X]
    simpa only [Fin.sum_univ_two] using (e.sum_repr x)
  have hy : Y = y := by
    dsimp [Y]
    simpa only [Fin.sum_univ_two] using (e.sum_repr y)
  have hxy : B x y x y = B X Y X Y := by
    calc
      B x y x y = B X y x y := congrArg (fun z => B z y x y) hx.symm
      _ = B X Y x y := congrArg (fun z => B X z x y) hy.symm
      _ = B X Y X y := congrArg (fun z => B X Y z y) hx.symm
      _ = B X Y X Y := congrArg (fun z => B X Y X z) hy.symm
  rw [hxy]
  calc
    B X Y X Y =
      (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) *
        B (e 0) (e 1) X Y := by
      change B (e.repr x 0 • e 0 + e.repr x 1 • e 1)
          (e.repr y 0 • e 0 + e.repr y 1 • e 1)
          (e.repr x 0 • e 0 + e.repr x 1 • e 1)
          (e.repr y 0 • e 0 + e.repr y 1 • e 1) = _
      exact hB.bilin_det_12 (e.repr x 0) (e.repr x 1)
        (e.repr y 0) (e.repr y 1) (e 0) (e 1)
        (e.repr x 0 • e 0 + e.repr x 1 • e 1)
        (e.repr y 0 • e 0 + e.repr y 1 • e 1)
    _ = (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) ^ 2 *
        B (e 0) (e 1) (e 0) (e 1) := by
      have h : B (e 0) (e 1) X Y =
          (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) *
            B (e 0) (e 1) (e 0) (e 1) := by
        change B (e 0) (e 1)
            (e.repr x 0 • e 0 + e.repr x 1 • e 1)
            (e.repr y 0 • e 0 + e.repr y 1 • e 1) = _
        exact hB.bilin_det_34 (e.repr x 0) (e.repr x 1)
          (e.repr y 0) (e.repr y 1) (e 0) (e 1) (e 0) (e 1)
      rw [h]
      ring

/-- **Math.** A nonpositive basis sectional numerator implies nonpositive sectional
numerators for all vector pairs in a two-dimensional space. -/
theorem diag_nonpos_of_basis (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V)
    (hbase : B (e 0) (e 1) (e 0) (e 1) ≤ 0) (x y : V) :
    B x y x y ≤ 0 := by
  rw [hB.diag_eq_det_sq_mul_basis e x y]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hbase

/-- **Math.** The curvature-operator sign used by the Jacobi comparison arguments is
the opposite of the diagonal sectional numerator. -/
theorem basis_reverse_pair_nonneg (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V)
    (hbase : B (e 0) (e 1) (e 0) (e 1) ≤ 0) (x y : V) :
    0 ≤ B x y y x := by
  have hdiag := hB.diag_nonpos_of_basis e hbase x y
  have hskew := hB.antisymm₃₄ x y x y
  linarith

/-- **Math.** A nonpositive sectional curvature quotient on a basis pair with
positive area denominator gives the curvature-operator sign on every pair in
dimension two. -/
theorem basis_reverse_pair_nonneg_of_sectional_nonpos (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V)
    (harea : 0 < wedgeSq (e 0) (e 1))
    (hsectional : sectionalCurvature B (e 0) (e 1) ≤ 0)
    (x y : V) :
    0 ≤ B x y y x := by
  have hbase : B (e 0) (e 1) (e 0) (e 1) ≤ 0 := by
    unfold sectionalCurvature at hsectional
    have h := (div_le_iff₀ harea).mp hsectional
    simpa using h
  exact hB.basis_reverse_pair_nonneg e hbase x y

end Riemannian.IsAlgCurvatureForm

namespace Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** The Gram determinant of two vectors in a two-dimensional space
transforms by the square of their coordinate determinant in any chosen basis. -/
theorem wedgeSq_eq_det_sq_mul_basis (e : Module.Basis (Fin 2) ℝ V) (x y : V) :
    wedgeSq x y =
      (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) ^ 2 *
        wedgeSq (e 0) (e 1) := by
  simpa only [stdCurvForm_diag] using
    isAlgCurvatureForm_stdCurvForm.diag_eq_det_sq_mul_basis e x y

namespace IsAlgCurvatureForm

variable {B : V → V → V → V → ℝ}

/-- **Math.** A sectional numerator bound on one basis pair gives the same
area-normalized numerator bound on every tangent pair in dimension two. -/
theorem diag_le_mul_wedgeSq_of_basis (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V) (κ : ℝ)
    (hbase : B (e 0) (e 1) (e 0) (e 1) ≤ κ * wedgeSq (e 0) (e 1))
    (x y : V) :
    B x y x y ≤ κ * wedgeSq x y := by
  rw [hB.diag_eq_det_sq_mul_basis e x y, wedgeSq_eq_det_sq_mul_basis e x y]
  calc
    _ ≤ (e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0) ^ 2 *
        (κ * wedgeSq (e 0) (e 1)) :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
    _ = _ := by ring

/-- **Math.** A basis sectional upper bound gives the reversed curvature-pair
lower bound used by the Jacobi comparison, retaining its full area factor. -/
theorem neg_mul_wedgeSq_le_reverse_pair_of_basis (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V) (κ : ℝ)
    (hbase : B (e 0) (e 1) (e 0) (e 1) ≤ κ * wedgeSq (e 0) (e 1))
    (x y : V) :
    -κ * wedgeSq x y ≤ B x y y x := by
  have hdiag := hB.diag_le_mul_wedgeSq_of_basis e κ hbase x y
  have hskew := hB.antisymm₃₄ x y x y
  linarith

/-- **Math.** Dividing the basis numerator by its positive Gram determinant
provides exactly the basis hypothesis needed for the arbitrary-pair bound. -/
theorem neg_mul_wedgeSq_le_reverse_pair_of_sectional (hB : IsAlgCurvatureForm B)
    (e : Module.Basis (Fin 2) ℝ V) (κ : ℝ)
    (harea : 0 < wedgeSq (e 0) (e 1))
    (hsectional : sectionalCurvature B (e 0) (e 1) ≤ κ)
    (x y : V) :
    -κ * wedgeSq x y ≤ B x y y x := by
  have hbase : B (e 0) (e 1) (e 0) (e 1) ≤ κ * wedgeSq (e 0) (e 1) := by
    exact (div_le_iff₀ harea).mp hsectional
  exact hB.neg_mul_wedgeSq_le_reverse_pair_of_basis e κ hbase x y

end IsAlgCurvatureForm

open Bundle Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** On a two-dimensional tangent space, a nonpositive basis
sectional numerator for the Levi-Civita curvature form implies the curvature
operator sign required by the Jacobi-field comparison argument for every pair
of tangent vectors. -/
theorem curvatureOperatorAt_pair_nonneg_of_basis_pair
    (g : RiemannianMetric I M) (p : M)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace I p))
    (hbase : g.leviCivitaConnection.curvatureFormAt g p
      (e 0) (e 1) (e 0) (e 1) ≤ 0)
    (x y : TangentSpace I p) :
    0 ≤ g.metricInner p
      (g.leviCivitaConnection.curvatureOperatorAt p x y y) x := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  exact hB.basis_reverse_pair_nonneg e hbase x y

/-- **Math.** A two-dimensional Levi-Civita basis curvature bound gives the
full curvature-operator inequality on arbitrary tangent vectors. The Gram
determinants here use the actual metric `g`, rather than an ambient model metric. -/
theorem curvatureOperatorAt_pair_lower_bound_of_basis_pair
    (g : RiemannianMetric I M) (p : M)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace I p)) (κ : ℝ)
    (hbase : g.leviCivitaConnection.curvatureFormAt g p
      (e 0) (e 1) (e 0) (e 1) ≤
        κ * (g.metricInner p (e 0) (e 0) * g.metricInner p (e 1) (e 1) -
          g.metricInner p (e 0) (e 1) * g.metricInner p (e 0) (e 1)))
    (x y : TangentSpace I p) :
    -κ * (g.metricInner p x x * g.metricInner p y y -
      g.metricInner p x y * g.metricInner p x y) ≤
        g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  exact hB.neg_mul_wedgeSq_le_reverse_pair_of_basis e κ hbase x y

end Riemannian

#print axioms Riemannian.IsAlgCurvatureForm.diag_eq_det_sq_mul_basis
#print axioms Riemannian.IsAlgCurvatureForm.diag_nonpos_of_basis
#print axioms Riemannian.IsAlgCurvatureForm.basis_reverse_pair_nonneg
#print axioms Riemannian.IsAlgCurvatureForm.basis_reverse_pair_nonneg_of_sectional_nonpos
#print axioms Riemannian.curvatureOperatorAt_pair_nonneg_of_basis_pair
#print axioms Riemannian.wedgeSq_eq_det_sq_mul_basis
#print axioms Riemannian.IsAlgCurvatureForm.diag_le_mul_wedgeSq_of_basis
#print axioms Riemannian.IsAlgCurvatureForm.neg_mul_wedgeSq_le_reverse_pair_of_basis
#print axioms Riemannian.IsAlgCurvatureForm.neg_mul_wedgeSq_le_reverse_pair_of_sectional
#print axioms Riemannian.curvatureOperatorAt_pair_lower_bound_of_basis_pair

end
