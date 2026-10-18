module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.UpperHalfPlaneIsometryAnalytic
public import Geometry.DiscProjectiveHolonomy

@[expose] public section

/-!
# Actual half-plane isometries and projective holonomy

The literal rational Cayley equivalence is an analytic diffeomorphism.
Conjugation to the disc and the audited disc-automorphism classification
construct a canonical projective representative of each actual analytic
half-plane automorphism. Positive-orientation Poincaré isometries use the
proved analytic converter; no holonomy or coherent lift is assumed.
-/

open Set Metric Manifold UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace SystolicGrowth

noncomputable section

open Vendored.RiemannDynamics

/-- **Math.** The actual rational Cayley reading is analytic throughout the
native open disc, since its denominator is genuinely nonzero there. -/
theorem discCayleyEquiv_coe_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun z : AnalyticUnitDisc => (discCayleyEquiv z : ℂ)) := by
  have hval : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun z : AnalyticUnitDisc => (z : ℂ)) := contMDiff_subtype_val
  change ContMDiff _ _ ω (fun z : AnalyticUnitDisc =>
    Complex.I * (1 + (z : ℂ)) / (1 - (z : ℂ)))
  exact (contMDiff_const.mul (contMDiff_const.add hval)).div₀
    (contMDiff_const.sub hval) (fun z => one_sub_ne_zero_of_mem_ball z.property)

/-- **Math.** The same literal Cayley map is analytic with values in the
unchanged upper-half-plane manifold. -/
theorem discCayleyEquiv_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω discCayleyEquiv := by
  intro z
  have h := (UpperHalfPlane.contMDiffAt_ofComplex (n := ω)
    (discCayleyEquiv z).im_pos).comp z (discCayleyEquiv_coe_contMDiff z)
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h

/-- **Math.** The inverse rational Cayley reading is analytic at every
genuine half-plane point, not merely continuous. -/
theorem discCayleyEquiv_symm_coe_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun p : ℍ => (discCayleyEquiv.symm p : ℂ)) := by
  change ContMDiff _ _ ω (fun p : ℍ => ((p : ℂ) - Complex.I) / ((p : ℂ) + Complex.I))
  exact (UpperHalfPlane.contMDiff_coe.sub contMDiff_const).div₀
    (UpperHalfPlane.contMDiff_coe.add contMDiff_const)
    (fun p => add_I_ne_zero_of_im_pos p.im_pos)

/-- **Math.** The inverse maps analytically into the actual open-disc
manifold, whose inclusion chart is unchanged. -/
theorem discCayleyEquiv_symm_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω discCayleyEquiv.symm := by
  intro p
  apply contMDiffAt_iff_target.mpr
  refine ⟨discCayleyHomeomorph.symm.continuous.continuousAt, ?_⟩
  convert! discCayleyEquiv_symm_coe_contMDiff p using 1

/-- **Math.** The fixed rational Cayley equivalence, upgraded with proved
forward and inverse analyticity on the original two carriers. -/
def discCayleyDiffeomorph :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) AnalyticUnitDisc ℍ ω where
  toEquiv := discCayleyEquiv
  contMDiff_toFun := discCayleyEquiv_contMDiff
  contMDiff_invFun := discCayleyEquiv_symm_contMDiff

/-- **Math.** Analytic automorphisms of the original upper-half-plane manifold. -/
abbrev AnalyticHalfPlaneAutomorphism :=
  Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ℍ ℍ ω

/-- **Math.** Conjugate the very same half-plane automorphism by the actual
analytic rational Cayley map. -/
def halfPlaneDiscAutomorphism (e : AnalyticHalfPlaneAutomorphism) : AnalyticDiscAutomorphism :=
  (discCayleyDiffeomorph.trans e).trans discCayleyDiffeomorph.symm

/-- **Math.** The audited disc classification gives a canonical PSL₂ class
of each genuine analytic half-plane automorphism. -/
def halfPlaneProjective (e : AnalyticHalfPlaneAutomorphism) : PSL(2, ℝ) :=
  discProjective (halfPlaneDiscAutomorphism e)

@[simp] theorem halfPlaneProjective_smul (e : AnalyticHalfPlaneAutomorphism) (p : ℍ) :
    halfPlaneProjective e • p = e p := by
  obtain ⟨z, rfl⟩ := discCayleyEquiv.surjective p
  rw [halfPlaneProjective, discProjective_smul_cayley]
  change discCayleyEquiv (discCayleyEquiv.symm (e (discCayleyEquiv z))) = e (discCayleyEquiv z)
  exact discCayleyEquiv.apply_symm_apply _

/-- **Math.** The projective representative is determined by its actual
action on every half-plane point. -/
theorem halfPlaneProjective_eq_iff (e : AnalyticHalfPlaneAutomorphism) (γ : PSL(2, ℝ)) :
    halfPlaneProjective e = γ ↔ ∀ p : ℍ, γ • p = e p := by
  constructor
  · rintro rfl
    exact halfPlaneProjective_smul e
  · intro h
    apply eq_of_smul_eq_smul (α := ℍ)
    intro p
    exact (halfPlaneProjective_smul e p).trans (h p).symm

@[simp] theorem halfPlaneProjective_refl :
    halfPlaneProjective (Diffeomorph.refl (modelWithCornersSelf ℂ ℂ) ℍ ω) = 1 := by
  apply (halfPlaneProjective_eq_iff _ _).mpr
  exact fun p => one_smul _ p

/-- **Math.** Projective classes compose coherently because their genuine
half-plane actions compose, independently of SL₂ representative choices. -/
@[simp] theorem halfPlaneProjective_trans (e f : AnalyticHalfPlaneAutomorphism) :
    halfPlaneProjective (e.trans f) = halfPlaneProjective f * halfPlaneProjective e := by
  apply (halfPlaneProjective_eq_iff _ _).mpr
  intro p
  rw [mul_smul, halfPlaneProjective_smul, halfPlaneProjective_smul]
  rfl

theorem halfPlaneProjective_injective : Function.Injective halfPlaneProjective := by
  intro e f h
  apply Diffeomorph.ext
  intro p
  rw [← halfPlaneProjective_smul e p, ← halfPlaneProjective_smul f p, h]

/-- **Math.** Actual smooth positively oriented Poincaré isometries obtain
projective representatives after deriving, not assuming, their analyticity. -/
def poincareIsometryProjective
    (Φ : Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ : ℍ → ℍ))
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ : ℍ → ℍ) p).toLinearMap) :
    PSL(2, ℝ) :=
  halfPlaneProjective (upperHalfPlaneIsometryToAnalyticDiffeomorph Φ hmetric hdet)

@[simp] theorem poincareIsometryProjective_smul
    (Φ : Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ : ℍ → ℍ))
    (hdet : ∀ p : ℍ, 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ : ℍ → ℍ) p).toLinearMap)
    (p : ℍ) : poincareIsometryProjective Φ hmetric hdet • p = Φ p :=
  halfPlaneProjective_smul _ p

/-- **Math.** A genuine group action by smooth positively oriented Poincaré
isometries gives a coherent projective homomorphism. Only the original
action's identity and composition laws are inputs, not holonomy coherence. -/
def poincareIsometryActionProjectiveHom {G : Type*} [Group G]
    (Φ : G → Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : ∀ a, LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ a : ℍ → ℍ))
    (hdet : ∀ a (p : ℍ), 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ a : ℍ → ℍ) p).toLinearMap)
    (h_one : ∀ p, Φ 1 p = p)
    (h_mul : ∀ a b p, Φ (a * b) p = Φ a (Φ b p)) : G →* PSL(2, ℝ) where
  toFun a := poincareIsometryProjective (Φ a) (hmetric a) (hdet a)
  map_one' := by
    apply eq_of_smul_eq_smul (α := ℍ)
    intro p
    rw [poincareIsometryProjective_smul, h_one, one_smul]
  map_mul' a b := by
    apply eq_of_smul_eq_smul (α := ℍ)
    intro p
    rw [mul_smul, poincareIsometryProjective_smul, poincareIsometryProjective_smul,
      poincareIsometryProjective_smul, h_mul]

@[simp] theorem poincareIsometryActionProjectiveHom_smul {G : Type*} [Group G]
    (Φ : G → Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : ∀ a, LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ a : ℍ → ℍ))
    (hdet : ∀ a (p : ℍ), 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ a : ℍ → ℍ) p).toLinearMap)
    (h_one : ∀ p, Φ 1 p = p)
    (h_mul : ∀ a b p, Φ (a * b) p = Φ a (Φ b p)) (a : G) (p : ℍ) :
    poincareIsometryActionProjectiveHom Φ hmetric hdet h_one h_mul a • p = Φ a p :=
  poincareIsometryProjective_smul _ _ _ p

/-- **Math.** A faithful genuine isometry action yields faithful projective
holonomy because its action remains literally unchanged. -/
theorem poincareIsometryActionProjectiveHom_injective {G : Type*} [Group G]
    (Φ : G → Diffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ℍ ℍ ∞)
    (hmetric : ∀ a, LeeLib.Ch02.IsMetricPreserving
      upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric (Φ a : ℍ → ℍ))
    (hdet : ∀ a (p : ℍ), 0 < LinearMap.det
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) (Φ a : ℍ → ℍ) p).toLinearMap)
    (h_one : ∀ p, Φ 1 p = p)
    (h_mul : ∀ a b p, Φ (a * b) p = Φ a (Φ b p)) (hfaithful : Function.Injective Φ) :
    Function.Injective (poincareIsometryActionProjectiveHom Φ hmetric hdet h_one h_mul) := by
  intro a b h
  apply hfaithful
  apply Diffeomorph.ext
  intro p
  have he := congrArg (fun γ : PSL(2, ℝ) => γ • p) h
  simpa only [poincareIsometryActionProjectiveHom_smul] using he

#print axioms discCayleyDiffeomorph
#print axioms halfPlaneProjective_smul
#print axioms halfPlaneProjective_trans
#print axioms halfPlaneProjective_injective
#print axioms poincareIsometryProjective
#print axioms poincareIsometryProjective_smul
#print axioms poincareIsometryActionProjectiveHom
#print axioms poincareIsometryActionProjectiveHom_smul
#print axioms poincareIsometryActionProjectiveHom_injective

end
end SystolicGrowth
