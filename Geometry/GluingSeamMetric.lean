module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamTransitions
public import Geometry.GluingCollarRiemannian

@[expose] public section

/-!
# Same-seam compatibility of the actual collar tangent form

On the exact native overlap, a same-seam transition is locally a fixed
angular translation. Its real differential is the identity and its signed
radius is unchanged. Consequently the actual continuous collar form is
preserved on arbitrary tangent vectors, including at signed radius zero.
No smoothness of the collar coefficient at the seam is needed or asserted.
-/

open scoped Topology

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual native transition at one seam has identity real differential
throughout its exact overlap, including at the seam itself. -/
theorem seamAngularComplexChart_transition_hasFDerivAt
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)).source) :
    HasFDerivAt ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)) (ContinuousLinearMap.id ℝ ℂ) x := by
  obtain ⟨m, hm⟩ := P.seamAngularComplexChart_transition_eventually_eq_add k θ ψ hx
  exact ((hasFDerivAt_id x).add_const
    ((((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)).congr_of_eventuallyEq hm

/-- The signed radius is exactly unchanged by an actual same-seam transition. -/
theorem seamAngularComplexChart_transition_re
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)).source) :
    (((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)) x).re = x.re := by
  obtain ⟨m, hm⟩ := P.seamAngularComplexChart_transition_eventually_eq_add k θ ψ hx
  have heq : (fun w => P.seamAngularComplexChart k ψ
      ((P.seamAngularComplexChart k θ).symm w)) =ᶠ[𝓝 x]
      (fun w => w + ((((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) := hm
  simpa using congrArg Complex.re heq.eq_of_nhds

/-- The actual collar tangent form descends across all angular charts of
one seam, on arbitrary real tangent vectors and including signed radius zero. -/
theorem seamAngularComplexChart_transition_tangentForm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)).source) (v u : ℂ) :
    gluingCollarTangentForm (gluingRadius C g)
      ((((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart k ψ)) x).re,
        (((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart k ψ)) x).im)
      ((fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart k ψ)) x v).re,
        (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart k ψ)) x v).im)
      ((fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart k ψ)) x u).re,
        (fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart k ψ)) x u).im) =
      gluingCollarTangentForm (gluingRadius C g) (x.re, x.im) (v.re, v.im) (u.re, u.im) := by
  rw [(P.seamAngularComplexChart_transition_hasFDerivAt k θ ψ hx).fderiv]
  simp only [ContinuousLinearMap.id_apply, gluingCollarTangentForm_apply,
    P.seamAngularComplexChart_transition_re k θ ψ hx]

#print axioms seamAngularComplexChart_transition_hasFDerivAt
#print axioms seamAngularComplexChart_transition_re
#print axioms seamAngularComplexChart_transition_tangentForm

end SystolicGrowth.ExerciseGluingPreparation
