module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

@[expose] public section

/-!
# The coercive resolvent of a Hilbert gradient graph

For a Hilbert space of pairs `(function, weak derivative)`, the map `J`
forgets the derivative. Its norm is at most one. Adding `(λ - 1)` times
the function inner product to the graph inner product gives the actual
variational resolvent of `-Δ + λ`. Lax--Milgram constructs the operator;
testing its equation proves the sharp `1 / λ` bound on function values.

The manifold gradient graph and its weak derivative identification are
separate constructions. No solvability assumption is supplied here.
-/

namespace SystolicGrowth

open ContinuousLinearMap InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The bounded energy form of the graph norm plus the positive mass term. -/
def hilbertGraphEnergy (J : V →L[ℝ] H) (mass : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).comp
    (ContinuousLinearMap.id ℝ V + (mass - 1) • (J.adjoint.comp J))

@[simp]
theorem hilbertGraphEnergy_apply (J : V →L[ℝ] H) (mass : ℝ) (v w : V) :
    hilbertGraphEnergy J mass v w = ⟪v, w⟫_ℝ + (mass - 1) * ⟪J v, J w⟫_ℝ := by
  change ⟪v + (mass - 1) • J.adjoint (J v), w⟫_ℝ = _
  rw [inner_add_left, real_inner_smul_left, J.adjoint_inner_left]

/-- The mass term is nonnegative, so the original graph norm is coercive. -/
theorem hilbertGraphEnergy_isCoercive (J : V →L[ℝ] H) {mass : ℝ} (hmass : 1 ≤ mass) :
    IsCoercive (hilbertGraphEnergy J mass) := by
  refine ⟨1, zero_lt_one, fun v => ?_⟩
  rw [hilbertGraphEnergy_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  have hnonneg : 0 ≤ (mass - 1) * ‖J v‖ ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hmass) (sq_nonneg _)
  nlinarith

/-- The actual Hilbert graph solution, obtained from the coercive inverse. -/
def hilbertGraphResolventLift (J : V →L[ℝ] H) {mass : ℝ} (hmass : 1 ≤ mass) : H →L[ℝ] V :=
  (((hilbertGraphEnergy_isCoercive J hmass).continuousLinearEquivOfBilin).symm
    ).toContinuousLinearMap.comp J.adjoint

/-- The function component of the actual variational solution. -/
def hilbertGraphResolvent (J : V →L[ℝ] H) {mass : ℝ} (hmass : 1 ≤ mass) : H →L[ℝ] H :=
  J.comp (hilbertGraphResolventLift J hmass)

/-- The constructed solution satisfies the energy equation for every test. -/
theorem hilbertGraphResolventLift_weak (J : V →L[ℝ] H) {mass : ℝ} (hmass : 1 ≤ mass)
    (f : H) (w : V) :
    hilbertGraphEnergy J mass (hilbertGraphResolventLift J hmass f) w = ⟪f, J w⟫_ℝ := by
  let A := (hilbertGraphEnergy_isCoercive J hmass).continuousLinearEquivOfBilin
  change hilbertGraphEnergy J mass (A.symm (J.adjoint f)) w = _
  rw [← IsCoercive.continuousLinearEquivOfBilin_apply]
  change ⟪A (A.symm (J.adjoint f)), w⟫_ℝ = _
  rw [A.apply_symm_apply]
  exact J.adjoint_inner_left w f

/-- No other graph vector has the same weak right-hand side. -/
theorem hilbertGraphResolventLift_unique (J : V →L[ℝ] H) {mass : ℝ} (hmass : 1 ≤ mass)
    (f : H) {v : V}
    (hv : ∀ w, hilbertGraphEnergy J mass v w = ⟪f, J w⟫_ℝ) :
    v = hilbertGraphResolventLift J hmass f := by
  let A := (hilbertGraphEnergy_isCoercive J hmass).continuousLinearEquivOfBilin
  apply A.injective
  apply ext_inner_right ℝ
  intro w
  rw [IsCoercive.continuousLinearEquivOfBilin_apply,
    IsCoercive.continuousLinearEquivOfBilin_apply,
    hilbertGraphResolventLift_weak, hv]

/-- Testing the equation with the constructed graph vector gives its exact energy. -/
theorem hilbertGraphResolventLift_energy (J : V →L[ℝ] H) {mass : ℝ} (hmass : 1 ≤ mass)
    (f : H) :
    ‖hilbertGraphResolventLift J hmass f‖ ^ 2 +
        (mass - 1) * ‖hilbertGraphResolvent J hmass f‖ ^ 2 =
      ⟪f, hilbertGraphResolvent J hmass f⟫_ℝ := by
  simpa only [hilbertGraphEnergy_apply, real_inner_self_eq_norm_sq,
    hilbertGraphResolvent, ContinuousLinearMap.comp_apply] using
    hilbertGraphResolventLift_weak J hmass f (hilbertGraphResolventLift J hmass f)

/-- The projected resolvent has the sharp positive-mass norm estimate. -/
theorem hilbertGraphResolvent_norm_le (J : V →L[ℝ] H)
    (hJ : ∀ v : V, ‖J v‖ ≤ ‖v‖) {mass : ℝ} (hmass : 1 ≤ mass) (f : H) :
    ‖hilbertGraphResolvent J hmass f‖ ≤ ‖f‖ / mass := by
  have hmasspos : 0 < mass := lt_of_lt_of_le zero_lt_one hmass
  have hproj : ‖hilbertGraphResolvent J hmass f‖ ≤ ‖hilbertGraphResolventLift J hmass f‖ :=
    hJ (hilbertGraphResolventLift J hmass f)
  have hprojSq : ‖hilbertGraphResolvent J hmass f‖ ^ 2 ≤
      ‖hilbertGraphResolventLift J hmass f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hproj 2
  have henergy := hilbertGraphResolventLift_energy J hmass f
  have hcs := real_inner_le_norm f (hilbertGraphResolvent J hmass f)
  have hbound : mass * ‖hilbertGraphResolvent J hmass f‖ ^ 2 ≤
      ‖f‖ * ‖hilbertGraphResolvent J hmass f‖ := by
    nlinarith
  by_cases hz : ‖hilbertGraphResolvent J hmass f‖ = 0
  · rw [hz]
    positivity
  · have hn : 0 < ‖hilbertGraphResolvent J hmass f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (le_div_iff₀ hmasspos).2
    nlinarith

/-- The same estimate for differences is the bound needed by the nonlinear contraction. -/
theorem hilbertGraphResolvent_dist_le (J : V →L[ℝ] H)
    (hJ : ∀ v : V, ‖J v‖ ≤ ‖v‖) {mass : ℝ} (hmass : 1 ≤ mass) (f h : H) :
    dist (hilbertGraphResolvent J hmass f) (hilbertGraphResolvent J hmass h) ≤
      dist f h / mass := by
  simpa only [dist_eq_norm, map_sub] using hilbertGraphResolvent_norm_le J hJ hmass (f - h)

/-- The operator-norm form consumed by the actual nonlinear fixed-point construction. -/
theorem hilbertGraphResolvent_opNorm_le (J : V →L[ℝ] H)
    (hJ : ∀ v : V, ‖J v‖ ≤ ‖v‖) {mass : ℝ} (hmass : 1 ≤ mass) :
    ‖hilbertGraphResolvent J hmass‖ ≤ mass⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (by linarith))
  intro f
  simpa only [div_eq_mul_inv, mul_comm] using hilbertGraphResolvent_norm_le J hJ hmass f

#print axioms hilbertGraphResolventLift_weak
#print axioms hilbertGraphResolventLift_unique
#print axioms hilbertGraphResolvent_norm_le
#print axioms hilbertGraphResolvent_dist_le
#print axioms hilbertGraphResolvent_opNorm_le

end

end SystolicGrowth
