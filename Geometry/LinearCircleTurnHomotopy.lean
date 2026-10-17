module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoPuncturedDiskFreePresentation
public import Geometry.GluingSeamFundamentalGroup
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Group.Equiv.TypeTags

@[expose] public section

/-!
# Actual one-turn compatibility under physical unit-fiber maps

Every genuine circle homeomorphism sends its based positive one-turn loop to
the forward or reverse one-turn class. This is proved from the actual
exponential-cover integer marking and the induced group isomorphism.
Normalized invertible real-linear maps supply a concrete geometric consumer,
without an assumed orientation, degree or generator-compatibility premise.
-/

open Set
open scoped Topology ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- **Math.** A genuine additive integer automorphism sends the positive
generator to `1` or `-1`, by actual surjectivity and integer-unit arithmetic. -/
theorem integerAddEquiv_one_eq_one_or_neg_one (e : ℤ ≃+ ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  obtain ⟨d, hd⟩ := e.surjective 1
  have hmul : e d = d * e 1 := by simpa using map_zsmul e d (1 : ℤ)
  have h : e 1 * d = 1 := by
    calc
      e 1 * d = d * e 1 := mul_comm _ _
      _ = e d := hmul.symm
      _ = 1 := hd
  exact Int.eq_one_or_neg_one_of_mul_eq_one h

/-- **Math.** The opposite multiplicative integer marking has the same
generator rigidity; the opposite is retained exactly as in the real covering
API rather than silently changing the loop-composition convention. -/
theorem oppositeIntegerMulEquiv_generator_sign
    (e : (Multiplicative ℤ)ᵐᵒᵖ ≃* (Multiplicative ℤ)ᵐᵒᵖ) :
    e (MulOpposite.op (Multiplicative.ofAdd (1 : ℤ))) =
        MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) ∨
      e (MulOpposite.op (Multiplicative.ofAdd (1 : ℤ))) =
        (MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)))⁻¹ := by
  let a : ℤ ≃+ ℤ := (AddEquiv.additiveMultiplicative ℤ).symm.trans
    ((MulEquiv.toAdditive (MulEquiv.unop e)).trans (AddEquiv.additiveMultiplicative ℤ))
  rcases integerAddEquiv_one_eq_one_or_neg_one a with hp | hm
  · left
    apply MulOpposite.unop_injective
    apply Multiplicative.toAdd.injective
    exact hp
  · right
    apply MulOpposite.unop_injective
    apply Multiplicative.toAdd.injective
    exact hm

/-- **Math.** Any actual circle homeomorphism takes the genuine positive
one-turn based loop to a forward or reverse standard turn. This constructs
the based homotopy class; no orientation or degree assumption is supplied. -/
theorem circleHomeomorph_oneTurn_homotopic
    (h : Circle ≃ₜ Circle) (u : Circle) :
    ((circleOneTurnLoop u).map h.continuous).Homotopic (circleOneTurnLoop (h u)) ∨
      ((circleOneTurnLoop u).map h.continuous).Homotopic (circleOneTurnLoop (h u)).symm := by
  let E := (circleFundamentalGroupEquivIntegers u).symm.trans
    ((fundamentalGroupHomeomorphEquiv h u).trans (circleFundamentalGroupEquivIntegers (h u)))
  have hmap : circleFundamentalGroupEquivIntegers (h u)
      (⟦(circleOneTurnLoop u).map h.continuous⟧ : FundamentalGroup Circle (h u)) =
      E (MulOpposite.op (Multiplicative.ofAdd (1 : ℤ))) := by
    calc
      _ = circleFundamentalGroupEquivIntegers (h u)
          (fundamentalGroupHomeomorphEquiv h u ⟦circleOneTurnLoop u⟧) := rfl
      _ = E (circleFundamentalGroupEquivIntegers u ⟦circleOneTurnLoop u⟧) := by
        dsimp only [E, MulEquiv.trans_apply]
        rw [MulEquiv.symm_apply_apply]
      _ = _ := by rw [circleFundamentalGroupEquivIntegers_oneTurn]
  rcases oppositeIntegerMulEquiv_generator_sign E with hp | hm
  · left
    have heq : (⟦(circleOneTurnLoop u).map h.continuous⟧ : FundamentalGroup Circle (h u)) =
        ⟦circleOneTurnLoop (h u)⟧ := by
      apply (circleFundamentalGroupEquivIntegers (h u)).injective
      rw [hmap, hp, circleFundamentalGroupEquivIntegers_oneTurn]
    exact Path.Homotopic.Quotient.exact heq
  · right
    let γ : FundamentalGroup Circle (h u) := ⟦circleOneTurnLoop (h u)⟧
    have hγ : circleFundamentalGroupEquivIntegers (h u) γ =
        MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) :=
      circleFundamentalGroupEquivIntegers_oneTurn (h u)
    have hi : (⟦(circleOneTurnLoop (h u)).symm⟧ : FundamentalGroup Circle (h u)) =
        γ⁻¹ := rfl
    have heq : (⟦(circleOneTurnLoop u).map h.continuous⟧ : FundamentalGroup Circle (h u)) =
        ⟦(circleOneTurnLoop (h u)).symm⟧ := by
      apply (circleFundamentalGroupEquivIntegers (h u)).injective
      rw [hmap, hm, hi, map_inv, hγ]
    exact Path.Homotopic.Quotient.exact heq

/-- **Math.** The actual physical normalized real-linear circle map. -/
def linearCircleMap (L : ℂ ≃L[ℝ] ℂ) (u : Circle) : Circle :=
  convexPuncturedUnitDirection (L (u : ℂ)) (by
    intro h
    exact u.coe_ne_zero (L.injective (h.trans (map_zero L).symm)))

theorem continuous_linearCircleMap (L : ℂ ≃L[ℝ] ℂ) : Continuous (linearCircleMap L) := by
  have hz : Continuous (fun u : Circle => L (u : ℂ)) :=
    L.continuous.comp continuous_subtype_val
  have hn : ∀ u : Circle, L (u : ℂ) ≠ 0 := by
    intro u h
    exact u.coe_ne_zero (L.injective (h.trans (map_zero L).symm))
  exact ((hz.norm.inv₀ (fun u => norm_ne_zero_iff.mpr (hn u))).smul hz).subtype_mk _

/-- **Math.** Genuine positive radial rescaling does not change a physical
unit-circle direction. -/
theorem convexPuncturedUnitDirection_smul_pos (z : ℂ) (hz : z ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    convexPuncturedUnitDirection (r • z) (smul_ne_zero hr.ne' hz) =
      convexPuncturedUnitDirection z hz := by
  apply Circle.coe_injective
  change ‖r • z‖⁻¹ • (r • z) = ‖z‖⁻¹ • z
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv, smul_smul]
  congr 1
  rw [mul_right_comm, inv_mul_cancel₀ hr.ne', one_mul]

@[simp] theorem convexPuncturedUnitDirection_circle (u : Circle) :
    convexPuncturedUnitDirection (u : ℂ) u.coe_ne_zero = u := by
  apply Circle.coe_injective
  change ‖(u : ℂ)‖⁻¹ • (u : ℂ) = (u : ℂ)
  rw [Circle.norm_coe, inv_one, one_smul]

/-- **Math.** Inverting the actual linear map inverts its normalized circle
map; this is proved by genuine positive normalization, not angular degree. -/
theorem linearCircleMap_inverse (L : ℂ ≃L[ℝ] ℂ) (u : Circle) :
    linearCircleMap L.symm (linearCircleMap L u) = u := by
  unfold linearCircleMap
  change convexPuncturedUnitDirection
    (L.symm (‖L (u : ℂ)‖⁻¹ • L (u : ℂ))) _ = u
  simp only [map_smul, L.symm_apply_apply]
  have hr : 0 < ‖L (u : ℂ)‖⁻¹ := by
    apply inv_pos.mpr
    apply norm_pos_iff.mpr
    intro h
    exact u.coe_ne_zero (L.injective (h.trans (map_zero L).symm))
  rw [convexPuncturedUnitDirection_smul_pos _ u.coe_ne_zero _ hr,
    convexPuncturedUnitDirection_circle]

/-- **Math.** The genuine normalized image of the circle under an invertible
real-linear map is homeomorphic to the original unit circle. -/
def linearCircleHomeomorph (L : ℂ ≃L[ℝ] ℂ) : Circle ≃ₜ Circle where
  toFun := linearCircleMap L
  invFun := linearCircleMap L.symm
  left_inv := linearCircleMap_inverse L
  right_inv := linearCircleMap_inverse L.symm
  continuous_toFun := continuous_linearCircleMap L
  continuous_invFun := continuous_linearCircleMap L.symm

/-- **Math.** The actual normalized real-linear ellipse turn is based
homotopic to a forward or reverse standard circle turn. In particular,
coordinate/metric changes cannot turn a genuine one-turn into an even loop. -/
theorem linearCircleOneTurn_homotopic (L : ℂ ≃L[ℝ] ℂ) (u : Circle) :
    ((circleOneTurnLoop u).map (continuous_linearCircleMap L)).Homotopic
        (circleOneTurnLoop (linearCircleMap L u)) ∨
      ((circleOneTurnLoop u).map (continuous_linearCircleMap L)).Homotopic
        (circleOneTurnLoop (linearCircleMap L u)).symm :=
  circleHomeomorph_oneTurn_homotopic (linearCircleHomeomorph L) u

#print axioms circleHomeomorph_oneTurn_homotopic
#print axioms linearCircleHomeomorph
#print axioms linearCircleOneTurn_homotopic

end

end SystolicGrowth
