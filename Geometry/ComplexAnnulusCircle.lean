module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamFundamentalGroup
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# The literal coordinate annulus retracts to its circle

The overlap of the embedded-disk/exterior cover is a coordinate annulus.
Its radial homotopy gives its actual circle fundamental group, retaining
the positive one-turn representative.
-/

open Set
open scoped unitInterval ContinuousMap

namespace SystolicGrowth

noncomputable section

/-- The open annulus in the original complex coordinates. -/
def complexAnnulus (a b : ℝ) : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}

theorem Internal.ComplexAnnulusCircleHelpers.complexAnnulus_ne_zero {a b : ℝ} (ha : 0 ≤ a)
    (z : complexAnnulus a b) : (z : ℂ) ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_le_of_lt ha z.2.1)

/-- The normalized direction of a genuine annulus point. -/
def complexAnnulusCircleRetraction (a b : ℝ) (ha : 0 ≤ a) :
    C(complexAnnulus a b, Circle) where
  toFun z := ⟨(‖(z : ℂ)‖⁻¹ : ℝ) • (z : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (Internal.ComplexAnnulusCircleHelpers.complexAnnulus_ne_zero ha z))),
      inv_mul_cancel₀ (norm_pos_iff.mpr (Internal.ComplexAnnulusCircleHelpers.complexAnnulus_ne_zero ha z)).ne']⟩
  continuous_toFun := by
    have hz : Continuous (fun z : complexAnnulus a b => (z : ℂ)) :=
      continuous_subtype_val
    exact ((hz.norm.inv₀ (fun z =>
      (norm_pos_iff.mpr (Internal.ComplexAnnulusCircleHelpers.complexAnnulus_ne_zero ha z)).ne')).smul hz).subtype_mk _

/-- The chosen intermediate-radius circle, with its original positive angle. -/
def complexAnnulusCircleInclusion (a b ρ : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hρb : ρ < b) : C(Circle, complexAnnulus a b) where
  toFun θ := ⟨(ρ : ℝ) • (θ : ℂ), by
    change a < ‖(ρ : ℝ) • (θ : ℂ)‖ ∧ ‖(ρ : ℝ) • (θ : ℂ)‖ < b
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe, mul_one]
    exact ⟨haρ, hρb⟩⟩
  continuous_toFun :=
    ((continuous_const : Continuous (fun _ : Circle => (ρ : ℝ))).smul (continuous_subtype_val :
      Continuous (fun θ : Circle => (θ : ℂ)))).subtype_mk _

@[simp]
theorem complexAnnulusCircleRetraction_inclusion (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) (θ : Circle) :
    complexAnnulusCircleRetraction a b ha
      (complexAnnulusCircleInclusion a b ρ hρ haρ hρb θ) = θ := by
  apply Subtype.ext
  change (‖(ρ : ℝ) • (θ : ℂ)‖⁻¹ : ℝ) • ((ρ : ℝ) • (θ : ℂ)) = (θ : ℂ)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe, mul_one,
    smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

def Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush (ρ : ℝ) (t : I) (z : ℂ) : ℂ :=
  ((1 - (t : ℝ)) + t * (ρ / ‖z‖)) • z

private theorem complexAnnulusPush_norm (ρ : ℝ) (hρ : 0 < ρ) (t : I)
    {z : ℂ} (hz : z ≠ 0) :
    ‖Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush ρ t z‖ = (1 - (t : ℝ)) * ‖z‖ + t * ρ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hs : 0 ≤ (1 - (t : ℝ)) + t * (ρ / ‖z‖) :=
    add_nonneg (sub_nonneg.mpr t.2.2) (mul_nonneg t.2.1 (div_pos hρ hn).le)
  rw [Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
    add_mul, mul_assoc, div_mul_cancel₀ _ hn.ne']

theorem Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush_mem (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) (t : I)
    (z : complexAnnulus a b) : Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush ρ t z ∈ complexAnnulus a b := by
  change a < ‖Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush ρ t z‖ ∧ ‖Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush ρ t z‖ < b
  rw [complexAnnulusPush_norm ρ hρ t (Internal.ComplexAnnulusCircleHelpers.complexAnnulus_ne_zero ha z)]
  exact (convex_Ioo a b) z.2 ⟨haρ, hρb⟩
    (sub_nonneg.mpr t.2.2) t.2.1 (by ring)

/-- Radial interpolation remains in the same original annulus. -/
def complexAnnulusCircleHomotopy (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) :
    (ContinuousMap.id (complexAnnulus a b)).Homotopy
      ((complexAnnulusCircleInclusion a b ρ hρ haρ hρb).comp
        (complexAnnulusCircleRetraction a b ha)) where
  toFun p := ⟨Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush ρ p.1 p.2,
    Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush_mem a b ρ ha hρ haρ hρb p.1 p.2⟩
  continuous_toFun := by
    have ht : Continuous (fun p : I × complexAnnulus a b => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun p : I × complexAnnulus a b => (p.2 : ℂ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (((continuous_const.sub ht).add
      (ht.mul (continuous_const.div hz.norm (fun p =>
        (norm_pos_iff.mpr (Internal.ComplexAnnulusCircleHelpers.complexAnnulus_ne_zero ha p.2)).ne')))).smul hz).subtype_mk _
  map_zero_left z := by
    apply Subtype.ext
    simp [Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush]
  map_one_left z := by
    apply Subtype.ext
    change Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush ρ 1 (z : ℂ) =
      (ρ : ℝ) • ((‖(z : ℂ)‖⁻¹ : ℝ) • (z : ℂ))
    simp [Internal.ComplexAnnulusCircleHelpers.complexAnnulusPush, div_eq_mul_inv, mul_assoc]

/-- A genuine annulus-circle homotopy equivalence, not an assumed π₁ map. -/
def complexAnnulusCircleHomotopyEquiv (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) :
    complexAnnulus a b ≃ₕ Circle where
  toFun := complexAnnulusCircleRetraction a b ha
  invFun := complexAnnulusCircleInclusion a b ρ hρ haρ hρb
  left_inv := ⟨(complexAnnulusCircleHomotopy a b ρ ha hρ haρ hρb).symm⟩
  right_inv := by
    have h : (complexAnnulusCircleRetraction a b ha).comp
        (complexAnnulusCircleInclusion a b ρ hρ haρ hρb) = ContinuousMap.id Circle := by
      apply ContinuousMap.ext
      intro θ
      exact complexAnnulusCircleRetraction_inclusion a b ρ ha hρ haρ hρb θ
    rw [h]

/-- The same radial tracks and literal circle connector join any two
annulus points. -/
theorem complexAnnulus_pathConnected (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) :
    PathConnectedSpace (complexAnnulus a b) where
  nonempty := ⟨complexAnnulusCircleInclusion a b ρ hρ haρ hρb 1⟩
  joined x y := by
    let H := complexAnnulusCircleHomotopy a b ρ ha hρ haρ hρb
    let inc := complexAnnulusCircleInclusion a b ρ hρ haρ hρb
    let r := complexAnnulusCircleRetraction a b ha
    exact ⟨(H.evalAt x).trans
      (((Circle.path (r x) (r y)).map inc.continuous).trans (H.evalAt y).symm)⟩

/-- The actual radial direction induces the annulus's based circle group. -/
def complexAnnulusCircleFundamentalGroupEquiv (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) (z : complexAnnulus a b) :
    FundamentalGroup (complexAnnulus a b) z ≃*
      FundamentalGroup Circle (complexAnnulusCircleRetraction a b ha z) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (complexAnnulusCircleHomotopyEquiv a b ρ ha hρ haρ hρb)
  exact MulEquiv.ofBijective (FundamentalGroup.map (complexAnnulusCircleRetraction a b ha) z)
    (e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
      (FundamentalGroupoid.mk z))

/-- The included positive circle loop retains its exact one-turn class
under the radial direction map, with only the equality of endpoints cast. -/
theorem complexAnnulusCircleRetraction_oneTurn (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) (θ : Circle) :
    FundamentalGroup.mapOfEq (complexAnnulusCircleRetraction a b ha)
      (complexAnnulusCircleRetraction_inclusion a b ρ ha hρ haρ hρb θ)
      ⟦(circleOneTurnLoop θ).map
        (complexAnnulusCircleInclusion a b ρ hρ haρ hρb).continuous⟧ =
      ⟦circleOneTurnLoop θ⟧ := by
  erw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  exact complexAnnulusCircleRetraction_inclusion a b ρ ha hρ haρ hρb (circleOneTurnLoop θ t)

/-- The literal overlap circle carries the positive integer generator. -/
theorem complexAnnulusCircleRetraction_oneTurn_integer (a b ρ : ℝ) (ha : 0 ≤ a)
    (hρ : 0 < ρ) (haρ : a < ρ) (hρb : ρ < b) (θ : Circle) :
    circleFundamentalGroupEquivIntegers θ
      (FundamentalGroup.mapOfEq (complexAnnulusCircleRetraction a b ha)
        (complexAnnulusCircleRetraction_inclusion a b ρ ha hρ haρ hρb θ)
        ⟦(circleOneTurnLoop θ).map
          (complexAnnulusCircleInclusion a b ρ hρ haρ hρb).continuous⟧) =
      MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) := by
  rw [complexAnnulusCircleRetraction_oneTurn, circleFundamentalGroupEquivIntegers_oneTurn]

#print axioms complexAnnulusCircleHomotopyEquiv
#print axioms complexAnnulusCircleFundamentalGroupEquiv
#print axioms complexAnnulusCircleRetraction_oneTurn_integer

end

end SystolicGrowth
