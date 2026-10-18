module

public import Geometry.DirichletPuncturedSpine
public import Geometry.GluingPolarCollar
public import Geometry.GluingSeamFundamentalGroup

@[expose] public section

/-!
# The actual polar puncture loop and the Dirichlet spine

A positive polar circle below the true half-systole cutoff lies in the actual
Dirichlet domain. Its radial retraction is the original frontier radial
homeomorphism with exactly the same angular parameter. The resulting
one-turn equation is an equality of actual representative paths, with the
canonical casts at the correctly retracted basepoint.
-/

open Set Metric
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth

/-- The explicit positive-radius polar point has exactly its original angle. -/
theorem hyperbolicRadialDirection_gluingPolarPoint (o : ℍ) (θ : Circle)
    {r : ℝ} (hr : 0 < r) :
    hyperbolicRadialDirection o (gluingPolarPoint o θ r) = (θ : ℂ) := by
  have htanh : 0 < Real.tanh (r / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  rw [hyperbolicRadialDirection, discChart_gluingPolarPoint, norm_mul,
    Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htanh]
  simpa only [mul_comm] using
    mul_div_cancel_right₀ (θ : ℂ) (Complex.ofReal_ne_zero.mpr htanh.ne')

namespace ClosedHyperbolicSurface

noncomputable section

variable {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)

/-- A native closed half-systole ball lies in the actual Dirichlet domain.
This uses the true systole as the infimum of deck displacements. -/
theorem closedBall_subset_dirichletDomain_of_two_mul_le {r : ℝ}
    (hsys : 2 * r ≤ X.systole) :
    closedBall o r ⊆ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  intro z hz γ
  have hzdist : dist z o ≤ r := by
    simpa only [mem_closedBall, dist_comm] using hz
  by_cases hγ : γ = 1
  · simp only [hγ, one_smul, le_refl]
  have hdisp := X.systole_le_displacement γ hγ o
  have htri := dist_triangle o z (γ • o)
  rw [dist_comm o z] at htri
  linarith

theorem gluingPolarPoint_mem_dirichletDomain (r : ℝ)
    (hr : 0 < r) (hsys : 2 * r < X.systole) (θ : Circle) :
    gluingPolarPoint o θ r ∈
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  apply X.closedBall_subset_dirichletDomain_of_two_mul_le o hsys.le
  rw [mem_closedBall, dist_comm, dist_gluingPolarPoint o θ hr.le]

theorem gluingPolarPoint_ne_center (r : ℝ) (hr : 0 < r) (θ : Circle) :
    gluingPolarPoint o θ r ≠ o := by
  intro h
  have hd := dist_gluingPolarPoint o θ hr.le
  rw [h, dist_self] at hd
  linarith

def dirichletPolarDomainCircle (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) : C(Circle, X.PuncturedDirichletDomain o) where
  toFun θ := ⟨gluingPolarPoint o θ r,
    X.gluingPolarPoint_mem_dirichletDomain o r hr hsys θ,
    gluingPolarPoint_ne_center o r hr θ⟩
  continuous_toFun := by
    have hp : Continuous (fun θ : Circle => (θ, r)) :=
      continuous_id.prodMk continuous_const
    have h : Continuous (fun θ : Circle => gluingPolarPoint o θ r) := by
      simpa only [Function.comp_def] using (gluingPolarPoint_continuous o).comp hp
    exact h.subtype_mk _

/-- The actual polar circle in the original center-punctured quotient. -/
def dirichletPuncturePolarCircle (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) : C(Circle, X.CenterPuncturedCarrier o) :=
  (X.puncturedDirichletOrbitProjection o).comp
    (X.dirichletPolarDomainCircle o r hr hsys)

@[simp]
theorem dirichletPuncturePolarCircle_coe (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    ((X.dirichletPuncturePolarCircle o r hr hsys θ).1 : X.Carrier) =
      Quotient.mk'' (gluingPolarPoint o θ r) := rfl

/-- The original frontier radial parametrization projected to the actual spine. -/
def dirichletSpineRadialCircle : C(Circle, X.dirichletBoundarySpine o) :=
  (X.dirichletFrontierSpineProjection o).comp
    ⟨(X.dirichletBoundaryRadialHomeomorph o).symm,
      (X.dirichletBoundaryRadialHomeomorph o).symm.continuous⟩

/-- The actual quotient retraction preserves the polar angle exactly. -/
@[simp]
theorem dirichletSpineRetraction_polarCircle (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    X.dirichletSpineRetraction o (X.dirichletPuncturePolarCircle o r hr hsys θ) =
      X.dirichletSpineRadialCircle o θ := by
  have hd : hyperbolicRadialDirection o
      (X.dirichletPolarDomainCircle o r hr hsys θ).1 = (θ : ℂ) := by
    simpa only [dirichletPolarDomainCircle, ContinuousMap.coe_mk] using
      hyperbolicRadialDirection_gluingPolarPoint o θ hr
  change X.dirichletSpineRetraction o
    (X.puncturedDirichletOrbitProjection o (X.dirichletPolarDomainCircle o r hr hsys θ)) = _
  rw [X.dirichletSpineRetraction_projection o,
    X.dirichletPunctureRetraction_eq_of_direction o _ θ hd]
  rfl

/-- The original positively oriented one-turn polar loop. -/
def dirichletPuncturePolarOneTurn (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    Path (X.dirichletPuncturePolarCircle o r hr hsys θ)
      (X.dirichletPuncturePolarCircle o r hr hsys θ) :=
  (circleOneTurnLoop θ).map (X.dirichletPuncturePolarCircle o r hr hsys).continuous

/-- At every time the source loop is the original polar formula. -/
@[simp]
theorem dirichletPuncturePolarOneTurn_apply (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) (t : I) :
    (X.dirichletPuncturePolarOneTurn o r hr hsys θ t).1 =
      (Quotient.mk'' (gluingPolarPoint o
        (Circle.exp ((θ : ℂ).arg + 2 * Real.pi * (t : ℝ))) r) : X.Carrier) := by
  change (Quotient.mk'' (gluingPolarPoint o (circleOneTurnLoop θ t) r) : X.Carrier) = _
  rw [circleOneTurnLoop_apply]

/-- Retraction sends the actual one-turn polar loop literally to the projected
frontier one-turn loop; its basepoint is the actual radial frontier exit. -/
theorem dirichletSpineRetraction_polarOneTurn (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    ((X.dirichletPuncturePolarOneTurn o r hr hsys θ).map
      (X.dirichletSpineRetraction o).continuous).cast
        (X.dirichletSpineRetraction_polarCircle o r hr hsys θ).symm
        (X.dirichletSpineRetraction_polarCircle o r hr hsys θ).symm =
      (circleOneTurnLoop θ).map (X.dirichletSpineRadialCircle o).continuous := by
  apply Path.ext
  funext t
  exact X.dirichletSpineRetraction_polarCircle o r hr hsys (circleOneTurnLoop θ t)

/-- The precise induced based map, with the proved moved-basepoint identity,
takes the original polar generator to the original radial frontier generator. -/
theorem dirichletSpineRetraction_fundamentalGroup_polarOneTurn (r : ℝ) (hr : 0 < r)
    (hsys : 2 * r < X.systole) (θ : Circle) :
    FundamentalGroup.mapOfEq (X.dirichletSpineRetraction o)
      (X.dirichletSpineRetraction_polarCircle o r hr hsys θ)
      ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧ =
        ⟦(circleOneTurnLoop θ).map (X.dirichletSpineRadialCircle o).continuous⟧ := by
  exact (FundamentalGroup.mapOfEq_apply (X.dirichletSpineRetraction o)
    (X.dirichletSpineRetraction_polarCircle o r hr hsys θ)
    ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧).trans
      (congrArg (fun p => (⟦p⟧ : Path.Homotopic.Quotient
        (X.dirichletSpineRadialCircle o θ) (X.dirichletSpineRadialCircle o θ)))
        (X.dirichletSpineRetraction_polarOneTurn o r hr hsys θ))

end
end ClosedHyperbolicSurface
end SystolicGrowth
