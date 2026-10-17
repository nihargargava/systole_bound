module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronLogDerivativeResidues
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-!
# A genuine local principal-pole Perron contour

The principal weighted logarithmic derivative integrates to `2πi*x` on
every sufficiently small circle around `1`. The safe neighborhood follows
from the proved analytic regular part and local principal nonvanishing;
it is not an assumed zero-free region.

This local contour does not supply the quantitative strip, zero-avoiding
height, or rectangular edge bounds required by the global MA03 exercise.
-/

open Filter Metric
open scoped Topology

namespace SystolicGrowth.CookMagyarCircle

/-- Every sufficiently small circle around the principal pole has the exact
weighted Perron residue `x`, with its safe radius derived from local analyticity. -/
theorem exists_principal_perronLogDerivativeIntegrand_circleIntegral_eq
    (q : ℕ) [NeZero q] (x : ℝ) (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R < r →
      (∮ s in C((1 : ℂ), R),
        perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x s) =
          (2 * Real.pi * Complex.I : ℂ) * (x : ℂ) := by
  let regularPart : ℂ → ℂ := fun s =>
    dslope (fun z : ℂ => (x : ℂ) ^ z / z) 1 s +
      principalLogDerivRegularRemainder q s * ((x : ℂ) ^ s / s)
  let numerator : ℂ → ℂ := fun s => (x : ℂ) + (s - 1) * regularPart s
  have hregular : AnalyticAt ℂ regularPart 1 :=
    analyticAt_principal_perronLogDerivativeIntegrand_regular_part_one q x hx
  have hnum : AnalyticAt ℂ numerator 1 := by
    dsimp [numerator]
    exact analyticAt_const.fun_add
      ((analyticAt_id.fun_sub analyticAt_const).fun_mul hregular)
  have hdecomp : ∀ᶠ s : ℂ in 𝓝 1, s ≠ 1 →
      perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x s =
        (x : ℂ) / (s - 1) + regularPart s :=
    eventually_nhdsWithin_iff.mp
      (eventually_principal_perronLogDerivativeIntegrand_eq_pole_add_regular_part q x hx)
  have hlocal : {s : ℂ | AnalyticAt ℂ numerator s ∧
      (s ≠ 1 → perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x s =
        (x : ℂ) / (s - 1) + regularPart s)} ∈ 𝓝 (1 : ℂ) :=
    hnum.eventually_analyticAt.and hdecomp
  obtain ⟨r, hr, hsubset⟩ := nhds_basis_closedBall.mem_iff.mp hlocal
  refine ⟨r, hr, ?_⟩
  intro R hR hRr
  have hRsubset : closedBall (1 : ℂ) R ⊆ closedBall (1 : ℂ) r :=
    closedBall_subset_closedBall hRr.le
  have hdiff : DifferentiableOn ℂ numerator (closedBall (1 : ℂ) R) := by
    intro s hs
    exact ((hsubset (hRsubset hs)).1.differentiableAt).differentiableWithinAt
  have hcongr : Set.EqOn
      (perronLogDerivativeIntegrand q (1 : DirichletCharacter ℂ q) x)
      (fun s : ℂ => (s - 1)⁻¹ • numerator s) (sphere (1 : ℂ) R) := by
    intro s hs
    have hs' : s ≠ (1 : ℂ) := by
      intro h
      subst s
      simp only [mem_sphere, dist_self] at hs
      linarith
    have hpoint := (hsubset (hRsubset (sphere_subset_closedBall hs))).2 hs'
    rw [hpoint]
    change (x : ℂ) / (s - 1) + regularPart s =
      (s - 1)⁻¹ * ((x : ℂ) + (s - 1) * regularPart s)
    field_simp [sub_ne_zero.mpr hs']
  calc
    _ = ∮ s in C((1 : ℂ), R), (s - 1)⁻¹ • numerator s :=
      circleIntegral.integral_congr hR.le hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) • numerator 1 :=
      hdiff.circleIntegral_sub_inv_smul (mem_ball_self hR)
    _ = _ := by simp only [numerator, sub_self, zero_mul, add_zero, smul_eq_mul]

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.exists_principal_perronLogDerivativeIntegrand_circleIntegral_eq
