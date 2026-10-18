module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainDistance

@[expose] public section

/-!
# Native comparison at a common-fin midpoint

A midpoint lying in the identified fin has representatives in both copies.
The proved own-copy comparison therefore handles every quotient test point,
including points outside the common fin. No interior-minimizer or seam-angle
assumption is needed.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- An actual cross-copy midpoint in the common fin satisfies cosh comparison
against every point of the quotient. The same midpoint is represented in both
copies, so both previously proved own-copy test theorems apply. -/
theorem gluingCollarFiniteMetricGlue_cross_midpoint_cosh_all_test_of_commonFin_midpoint
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    let I := gluingCollarFiniteMetricGlueLeft r R lam ε
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    dist (L x) (L (I q)) = dist (L x) (Rg y) / 2 →
    dist (L (I q)) (Rg y) = dist (L x) (Rg y) / 2 →
    ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
      2 * Real.cosh (dist (L x) (Rg y) / 2) * Real.cosh (dist z (L (I q))) ≤
        Real.cosh (dist z (L x)) + Real.cosh (dist z (Rg y)) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  intro hxm hmy
  have hseam : L (I q) = Rg (J q) :=
    congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hxmR : dist (L x) (Rg (J q)) = dist (L x) (Rg y) / 2 := by
    rw [← hseam]
    exact hxm
  have hmyR : dist (Rg (J q)) (Rg y) = dist (L x) (Rg y) / 2 := by
    rw [← hseam]
    exact hmy
  have hleft :=
    gluingCollarFiniteMetricGlue_cross_midpoint_cosh_left_test_of_left_midpoint
      hR hlam hconv x y (I q) hxm hmy
  have hright :=
    gluingCollarFiniteMetricGlue_cross_midpoint_cosh_right_test_of_right_midpoint
      hR hlam hconv x y (J q) hxmR hmyR
  intro z
  refine Quotient.inductionOn z ?_
  intro c
  cases c with
  | inl w => exact hleft w
  | inr w =>
    have h := hright w
    change 2 * Real.cosh (dist (L x) (Rg y) / 2) *
      Real.cosh (dist (Rg w) (Rg (J q))) ≤
        Real.cosh (dist (Rg w) (L x)) + Real.cosh (dist (Rg w) (Rg y)) at h
    rw [← hseam] at h
    exact h

#print axioms gluingCollarFiniteMetricGlue_cross_midpoint_cosh_all_test_of_commonFin_midpoint

end SystolicGrowth
