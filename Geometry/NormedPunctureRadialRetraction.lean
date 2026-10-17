module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Radial retraction outside a coordinate disk

The unit-ball complement strongly retracts the punctured coordinate space.
For the product norm on ℝ × ℝ the ball is a square; transporting this local
push through an actual embedded rectangle gives the one-holed complement
needed by the two-puncture open-cover construction.
-/

open Set
open scoped unitInterval

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radially expand only the points inside the unit coordinate ball. -/
def normPunctureRadialPush (t : I) (x : E) : E :=
  ((1 - (t : ℝ)) + t * (max 1 ‖x‖ / ‖x‖)) • x

omit [NormedSpace ℝ E] in
private theorem normPunctureRadialPush_scale_ge_one (t : I) {x : E} (hx : x ≠ 0) :
    1 ≤ (1 - (t : ℝ)) + t * (max 1 ‖x‖ / ‖x‖) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hratio : 1 ≤ max 1 ‖x‖ / ‖x‖ :=
    (le_div_iff₀ hn).mpr (by simp)
  nlinarith [mul_nonneg t.2.1 (sub_nonneg.mpr hratio)]

/-- The push never passes through the deleted coordinate origin. -/
theorem normPunctureRadialPush_ne_zero (t : I) {x : E} (hx : x ≠ 0) :
    normPunctureRadialPush t x ≠ 0 := by
  exact smul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (normPunctureRadialPush_scale_ge_one t hx))) hx

/-- The complete exterior, including the unit boundary, stays fixed. -/
theorem normPunctureRadialPush_fixed (t : I) {x : E} (hx : 1 ≤ ‖x‖) :
    normPunctureRadialPush t x = x := by
  have hn : ‖x‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  simp only [normPunctureRadialPush, max_eq_right hx, div_self hn]
  rw [show (1 - (t : ℝ)) + t * 1 = 1 by ring, one_smul]

/-- Its exact norm interpolates to the larger of the old norm and one. -/
theorem norm_normPunctureRadialPush (t : I) {x : E} (hx : x ≠ 0) :
    ‖normPunctureRadialPush t x‖ =
      (1 - (t : ℝ)) * ‖x‖ + t * max 1 ‖x‖ := by
  have hn : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hs : 0 ≤ (1 - (t : ℝ)) + t * (max 1 ‖x‖ / ‖x‖) :=
    zero_le_one.trans (normPunctureRadialPush_scale_ge_one t hx)
  rw [normPunctureRadialPush, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
    add_mul, mul_assoc, div_mul_cancel₀ _ hn]

/-- Every radial level expands monotonically during the outward push. -/
theorem norm_le_normPunctureRadialPush (t : I) {x : E} (hx : x ≠ 0) :
    ‖x‖ ≤ ‖normPunctureRadialPush t x‖ := by
  rw [norm_normPunctureRadialPush t hx]
  nlinarith [mul_nonneg t.2.1 (sub_nonneg.mpr (le_max_right (1 : ℝ) ‖x‖))]

@[simp]
theorem normPunctureRadialPush_zero (x : E) : normPunctureRadialPush 0 x = x := by
  simp [normPunctureRadialPush]

/-- At time one every surviving point lies outside the open unit ball. -/
theorem one_le_normPunctureRadialPush_one {x : E} (hx : x ≠ 0) :
    1 ≤ ‖normPunctureRadialPush 1 x‖ := by
  rw [norm_normPunctureRadialPush 1 hx]
  simp

/-- Interior points stay within the closed unit coordinate disk during the push. -/
theorem normPunctureRadialPush_norm_le_one (t : I) {x : E}
    (hx : x ≠ 0) (hn : ‖x‖ ≤ 1) :
    ‖normPunctureRadialPush t x‖ ≤ 1 := by
  rw [norm_normPunctureRadialPush t hx, max_eq_left hn]
  have hmul := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr t.2.2)
  nlinarith

theorem normPunctureRadialPush_continuous :
    Continuous (fun p : I × {x : E // x ≠ 0} =>
      normPunctureRadialPush p.1 p.2.1) := by
  have ht : Continuous (fun p : I × {x : E // x ≠ 0} => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : I × {x : E // x ≠ 0} => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hn := hx.norm
  exact ((continuous_const.sub ht).add
    (ht.mul ((continuous_const.max hn).div hn
      (fun p => (norm_pos_iff.mpr p.2.2).ne')))).smul hx

/-- The inclusion of the complete coordinate exterior into the punctured space. -/
def normExteriorInclusion : C({x : E // 1 ≤ ‖x‖}, {x : E // x ≠ 0}) where
  toFun x := ⟨x.1, norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one x.2)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The actual terminal radial retraction, not an assumed homotopy inverse. -/
def normExteriorRetraction : C({x : E // x ≠ 0}, {x : E // 1 ≤ ‖x‖}) where
  toFun x := ⟨normPunctureRadialPush 1 x.1, one_le_normPunctureRadialPush_one x.2⟩
  continuous_toFun := (normPunctureRadialPush_continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

/-- The radial push is a genuine strong deformation retraction fixing every
point of the exterior at every time. -/
def normExteriorDeformationRetraction :
    (ContinuousMap.id {x : E // x ≠ 0}).HomotopyRel
      (normExteriorInclusion.comp normExteriorRetraction)
      {x | 1 ≤ ‖x.1‖} where
  toHomotopy :=
    { toContinuousMap :=
        { toFun p := ⟨normPunctureRadialPush p.1 p.2.1,
            normPunctureRadialPush_ne_zero p.1 p.2.2⟩
          continuous_toFun := normPunctureRadialPush_continuous.subtype_mk _ }
      map_zero_left := fun x => Subtype.ext (normPunctureRadialPush_zero x.1)
      map_one_left := fun _ => rfl }
  prop' := fun t _ hx => Subtype.ext (normPunctureRadialPush_fixed t hx)

@[simp]
theorem normExteriorRetraction_inclusion (x : {x : E // 1 ≤ ‖x‖}) :
    normExteriorRetraction (normExteriorInclusion x) = x :=
  Subtype.ext (normPunctureRadialPush_fixed 1 x.2)

#print axioms normPunctureRadialPush_continuous
#print axioms normExteriorDeformationRetraction
#print axioms normExteriorRetraction_inclusion

end

end SystolicGrowth
