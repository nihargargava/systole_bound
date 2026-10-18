module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicArea

@[expose] public section

/-!
# Actual reflected identifications of equal-radius boundary circles

Reflect the upper half-plane across its imaginary axis, then conjugate by
the actual center-normalizing isometries. The resulting plane isometry
maps one center to the other and restricts to an isometry of their spheres.
This supplies the concrete circle matching for chain gluing, rather than
an assumed boundary-identification field.
-/

open Metric UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

namespace SystolicGrowth

/-- Reflection across the imaginary axis, fixing the standard basepoint. -/
def gluingMirror (z : ℍ) : ℍ :=
  ⟨-(conj (z : ℂ)), by simpa using z.im_pos⟩

@[simp] theorem gluingMirror_re (z : ℍ) : (gluingMirror z).re = -z.re := by
  simp [gluingMirror]

@[simp] theorem gluingMirror_im (z : ℍ) : (gluingMirror z).im = z.im := by
  simp [gluingMirror]

@[simp] theorem gluingMirror_involutive (z : ℍ) : gluingMirror (gluingMirror z) = z := by
  apply UpperHalfPlane.ext_re_im <;> simp

@[simp] theorem gluingMirror_I : gluingMirror (I : ℍ) = I := by
  apply UpperHalfPlane.ext_re_im <;> simp [UpperHalfPlane.I]

/-- The explicit reflection preserves the Poincaré distance. -/
theorem gluingMirror_isometry : Isometry gluingMirror := by
  apply Isometry.of_dist_eq
  intro z w
  rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq]
  simp only [gluingMirror_im]
  change 2 * Real.arsinh (dist (-(conj (z : ℂ))) (-(conj (w : ℂ))) /
    (2 * Real.sqrt (z.im * w.im))) = _
  rw [dist_neg_neg, Complex.dist_conj_conj]

/-- Reflect in the standard chart and transfer between the actual centers. -/
noncomputable def gluingCircleMap (o p z : ℍ) : ℍ :=
  p.toSL2R • gluingMirror (o.toSL2R⁻¹ • z)

@[simp] theorem gluingCircleMap_center (o p : ℍ) : gluingCircleMap o p o = p := by
  have ho : o.toSL2R⁻¹ • o = (I : ℍ) := by
    calc
      o.toSL2R⁻¹ • o = o.toSL2R⁻¹ • (o.toSL2R • (I : ℍ)) := by simp
      _ = I := inv_smul_smul _ _
  simp [gluingCircleMap, ho]

@[simp] theorem gluingCircleMap_inverse (o p z : ℍ) :
    gluingCircleMap p o (gluingCircleMap o p z) = z := by
  simp only [gluingCircleMap, inv_smul_smul, gluingMirror_involutive, smul_inv_smul]

/-- The chosen identification is a genuine plane isometry. -/
theorem gluingCircleMap_dist (o p z w : ℍ) :
    dist (gluingCircleMap o p z) (gluingCircleMap o p w) = dist z w := by
  simp only [gluingCircleMap, dist_smul]
  rw [gluingMirror_isometry.dist_eq, dist_smul]

/-- The concrete identification with its equally concrete reverse map. -/
noncomputable def gluingPlaneIsometry (o p : ℍ) : ℍ ≃ᵢ ℍ where
  toFun := gluingCircleMap o p
  invFun := gluingCircleMap p o
  left_inv := gluingCircleMap_inverse o p
  right_inv := gluingCircleMap_inverse p o
  isometry_toFun := Isometry.of_dist_eq (gluingCircleMap_dist o p)

/-- Equal-radius circles are matched exactly by the actual reflected map. -/
theorem gluingCircleMap_mem_sphere_iff (o p z : ℍ) (r : ℝ) :
    gluingCircleMap o p z ∈ sphere p r ↔ z ∈ sphere o r := by
  have hd : dist (gluingCircleMap o p z) p = dist z o := by
    calc
      _ = dist (gluingCircleMap o p z) (gluingCircleMap o p o) := by
        rw [gluingCircleMap_center]
      _ = dist z o := gluingCircleMap_dist o p z o
  simp only [mem_sphere, hd]

/-- The boundary-circle isometry used by each chain attachment. -/
noncomputable def gluingBoundaryCircleIsometry (o p : ℍ) (r : ℝ) :
    sphere o r ≃ᵢ sphere p r where
  toFun z := ⟨gluingCircleMap o p z.1, (gluingCircleMap_mem_sphere_iff o p z.1 r).mpr z.2⟩
  invFun z := ⟨gluingCircleMap p o z.1, (gluingCircleMap_mem_sphere_iff p o z.1 r).mpr z.2⟩
  left_inv z := Subtype.ext (gluingCircleMap_inverse o p z.1)
  right_inv z := Subtype.ext (gluingCircleMap_inverse p o z.1)
  isometry_toFun := Isometry.of_dist_eq fun z w => gluingCircleMap_dist o p z.1 w.1

#print axioms gluingPlaneIsometry
#print axioms gluingBoundaryCircleIsometry

end SystolicGrowth
