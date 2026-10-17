module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingNativeUnitTangentCharts

@[expose] public section

/-!
# Genuine orthonormal circle coordinates on the native seam tensor

The angular component is divided by the actual native coefficient
`sinh (r + |s|)`. This is not radial Euclidean normalization, and no smooth
replacement warp is used.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

/-- From orthonormal frame components to native radial/angular components. -/
noncomputable def gluingCollarOrthonormalCoord (r : ℝ) (z v : ℂ) : ℂ :=
  Complex.mk v.re (v.im / gluingCollarWarp r z.re)

/-- Read the orthonormal components of a native radial/angular vector. -/
noncomputable def gluingCollarOrthonormalComponents (r : ℝ) (z v : ℂ) : ℂ :=
  Complex.mk v.re (gluingCollarWarp r z.re * v.im)

@[simp] theorem gluingCollarOrthonormalComponents_coord {r : ℝ} (hr : 0 < r)
    (z v : ℂ) :
    gluingCollarOrthonormalComponents r z (gluingCollarOrthonormalCoord r z v) = v := by
  apply Complex.ext
  · rfl
  · dsimp only [gluingCollarOrthonormalComponents, gluingCollarOrthonormalCoord]
    field_simp [(gluingCollarWarp_pos hr z.re).ne']

@[simp] theorem gluingCollarOrthonormalCoord_components {r : ℝ} (hr : 0 < r)
    (z v : ℂ) :
    gluingCollarOrthonormalCoord r z (gluingCollarOrthonormalComponents r z v) = v := by
  apply Complex.ext
  · rfl
  · simp [gluingCollarOrthonormalComponents, gluingCollarOrthonormalCoord,
      (gluingCollarWarp_pos hr z.re).ne']

theorem gluingCollarOrthonormalComponents_norm_sq (r : ℝ) (z v : ℂ) :
    ‖gluingCollarOrthonormalComponents r z v‖ ^ 2 =
      gluingComplexCollarTangentForm r z v v := by
  rw [Complex.sq_norm, gluingComplexCollarTangentForm_apply]
  simp [gluingCollarOrthonormalComponents, gluingCollarTangentForm, mul_assoc]
  ring

theorem gluingCollarOrthonormalCoord_self {r : ℝ} (hr : 0 < r) (z v : ℂ) :
    gluingComplexCollarTangentForm r z (gluingCollarOrthonormalCoord r z v)
      (gluingCollarOrthonormalCoord r z v) = ‖v‖ ^ 2 := by
  rw [← gluingCollarOrthonormalComponents_norm_sq,
    gluingCollarOrthonormalComponents_coord hr]

theorem gluingCollarOrthonormalComponents_norm_eq_one (r : ℝ) (z v : ℂ)
    (hv : gluingComplexCollarTangentForm r z v v = 1) :
    ‖gluingCollarOrthonormalComponents r z v‖ = 1 := by
  have hs := gluingCollarOrthonormalComponents_norm_sq r z v
  rw [hv] at hs
  nlinarith [norm_nonneg (gluingCollarOrthonormalComponents r z v)]

theorem gluingCollarOrthonormalCoord_smul (r : ℝ) (z v : ℂ) (a : ℝ) :
    gluingCollarOrthonormalCoord r z (a • v) = a • gluingCollarOrthonormalCoord r z v := by
  apply Complex.ext <;> simp [gluingCollarOrthonormalCoord, mul_div_assoc]

theorem gluingCollarOrthonormalComponents_smul (r : ℝ) (z v : ℂ) (a : ℝ) :
    gluingCollarOrthonormalComponents r z (a • v) =
      a • gluingCollarOrthonormalComponents r z v := by
  apply Complex.ext <;> simp [gluingCollarOrthonormalComponents, mul_left_comm]

theorem gluingCollarOrthonormalCoord_ne_zero {r : ℝ} (hr : 0 < r) (z : ℂ)
    {v : ℂ} (hv : v ≠ 0) : gluingCollarOrthonormalCoord r z v ≠ 0 := by
  intro h
  have heq := gluingCollarOrthonormalComponents_coord hr z v
  simp [h, gluingCollarOrthonormalComponents] at heq
  exact hv heq.symm

theorem gluingCollarOrthonormalComponents_ne_zero {r : ℝ} (hr : 0 < r) (z : ℂ)
    {v : ℂ} (hv : v ≠ 0) : gluingCollarOrthonormalComponents r z v ≠ 0 := by
  intro h
  have heq := gluingCollarOrthonormalCoord_components hr z v
  simp [h, gluingCollarOrthonormalCoord] at heq
  exact hv heq.symm

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The native seam orthonormal circle parameter in the actual unit fiber. -/
noncomputable def nativeSeamUnitTangentParam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (a : Circle) :
    P.NativeUnitTangentFiber b :=
  P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩)
    b hb (gluingCollarOrthonormalCoord (gluingRadius C g) (P.seamAngularComplexChart k θ b) a)
    (by rw [P.gluingChartTangentForm_seam, gluingCollarOrthonormalCoord_self P.radius_pos,
      a.norm_coe]; norm_num)

/-- Recover the true orthonormal frame components from an actual native unit tangent. -/
noncomputable def nativeSeamUnitTangentAngle
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (v : P.NativeUnitTangentFiber b) : Circle :=
  ⟨gluingCollarOrthonormalComponents (gluingRadius C g) (P.seamAngularComplexChart k θ b)
    (P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩) b v),
    mem_sphere_zero_iff_norm.2 (gluingCollarOrthonormalComponents_norm_eq_one _ _ _ (by
      rw [← P.gluingChartTangentForm_seam k θ]
      exact P.nativeUnitTangentCoord_self (P.seamAngularComplexChart k θ)
        (Or.inr ⟨k, θ, rfl⟩) b hb v))⟩

@[simp] theorem nativeSeamUnitTangentCoord_param
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (a : Circle) :
    P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩) b
      (P.nativeSeamUnitTangentParam k θ b hb a) =
        gluingCollarOrthonormalCoord (gluingRadius C g) (P.seamAngularComplexChart k θ b) a :=
  P.nativeUnitTangentCoord_ofCoordinates _ _ _ _ _ _

@[simp] theorem nativeSeamUnitTangentAngle_param
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (a : Circle) :
    P.nativeSeamUnitTangentAngle k θ b hb (P.nativeSeamUnitTangentParam k θ b hb a) = a := by
  apply Subtype.ext
  change gluingCollarOrthonormalComponents _ _ (P.nativeUnitTangentCoord _ _ _ _) = (a : ℂ)
  rw [P.nativeSeamUnitTangentCoord_param, gluingCollarOrthonormalComponents_coord P.radius_pos]

@[simp] theorem nativeSeamUnitTangentParam_angle
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (v : P.NativeUnitTangentFiber b) :
    P.nativeSeamUnitTangentParam k θ b hb (P.nativeSeamUnitTangentAngle k θ b hb v) = v := by
  apply Subtype.ext
  change ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b
      (gluingCollarOrthonormalCoord _ _ (gluingCollarOrthonormalComponents _ _
        (P.nativeUnitTangentCoord _ _ b v))) = v.val
  rw [gluingCollarOrthonormalCoord_components P.radius_pos]
  exact Trivialization.symmL_continuousLinearMapAt _ (by exact hb) v.val

/-- Literal unit seam coordinates recover their orthonormal parameter exactly. -/
theorem nativeSeamUnitTangentAngle_ofCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (v : ℂ)
    (hv : P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
      (P.seamAngularComplexChart k θ b) v v = 1) :
    (P.nativeSeamUnitTangentAngle k θ b hb
      (P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ)
        (Or.inr ⟨k, θ, rfl⟩) b hb v hv) : ℂ) =
    gluingCollarOrthonormalComponents (gluingRadius C g) (P.seamAngularComplexChart k θ b) v := by
  change gluingCollarOrthonormalComponents _ _ (P.nativeUnitTangentCoord _ _ _ _) = _
  rw [P.nativeUnitTangentCoord_ofCoordinates]

/-- Reparameterize the native radial chart by the genuine orthonormal frame. -/
noncomputable def nativeSeamCircleReparam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (a : Circle) : Circle :=
  ⟨NormedSpace.normalize (gluingCollarOrthonormalCoord (gluingRadius C g)
    (P.seamAngularComplexChart k θ b) a), mem_sphere_zero_iff_norm.2
      (NormedSpace.norm_normalize (gluingCollarOrthonormalCoord_ne_zero P.radius_pos _ a.coe_ne_zero))⟩

/-- Inverse reparameterization, restoring orthonormal angular components. -/
noncomputable def nativeSeamCircleReparamInv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (a : Circle) : Circle :=
  ⟨NormedSpace.normalize (gluingCollarOrthonormalComponents (gluingRadius C g)
    (P.seamAngularComplexChart k θ b) a), mem_sphere_zero_iff_norm.2
      (NormedSpace.norm_normalize (gluingCollarOrthonormalComponents_ne_zero P.radius_pos _ a.coe_ne_zero))⟩

@[simp] theorem nativeSeamCircleReparamInv_reparam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (a : Circle) :
    P.nativeSeamCircleReparamInv k θ b (P.nativeSeamCircleReparam k θ b a) = a := by
  apply Subtype.ext
  change NormedSpace.normalize (gluingCollarOrthonormalComponents _ _
    (NormedSpace.normalize (gluingCollarOrthonormalCoord _ _ a))) = (a : ℂ)
  have hc : gluingCollarOrthonormalComponents (gluingRadius C g) (P.seamAngularComplexChart k θ b)
      (NormedSpace.normalize (gluingCollarOrthonormalCoord (gluingRadius C g)
        (P.seamAngularComplexChart k θ b) a)) =
      ‖gluingCollarOrthonormalCoord (gluingRadius C g) (P.seamAngularComplexChart k θ b) a‖⁻¹ • (a : ℂ) := by
    rw [NormedSpace.normalize, gluingCollarOrthonormalComponents_smul,
      gluingCollarOrthonormalComponents_coord P.radius_pos]
  rw [hc,
    NormedSpace.normalize_smul_of_pos (inv_pos.2 (norm_pos_iff.2
      (gluingCollarOrthonormalCoord_ne_zero P.radius_pos _ a.coe_ne_zero)))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one a.norm_coe

@[simp] theorem nativeSeamCircleReparam_reparamInv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (a : Circle) :
    P.nativeSeamCircleReparam k θ b (P.nativeSeamCircleReparamInv k θ b a) = a := by
  apply Subtype.ext
  change NormedSpace.normalize (gluingCollarOrthonormalCoord _ _
    (NormedSpace.normalize (gluingCollarOrthonormalComponents _ _ a))) = (a : ℂ)
  have hc : gluingCollarOrthonormalCoord (gluingRadius C g) (P.seamAngularComplexChart k θ b)
      (NormedSpace.normalize (gluingCollarOrthonormalComponents (gluingRadius C g)
        (P.seamAngularComplexChart k θ b) a)) =
      ‖gluingCollarOrthonormalComponents (gluingRadius C g) (P.seamAngularComplexChart k θ b) a‖⁻¹ • (a : ℂ) := by
    rw [NormedSpace.normalize, gluingCollarOrthonormalCoord_smul,
      gluingCollarOrthonormalCoord_components P.radius_pos]
  rw [hc,
    NormedSpace.normalize_smul_of_pos (inv_pos.2 (norm_pos_iff.2
      (gluingCollarOrthonormalComponents_ne_zero P.radius_pos _ a.coe_ne_zero)))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one a.norm_coe

theorem nativeSeamCircleReparam_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle =>
      P.nativeSeamCircleReparam k θ q.1.val q.2) := by
  apply Continuous.subtype_mk
  have he : Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle =>
      P.seamAngularComplexChart k θ q.1.val) :=
    (P.seamAngularComplexChart k θ).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_fst) (fun q => q.1.property)
  have hw := (gluingCollarWarp_continuous (gluingRadius C g)).comp (Complex.continuous_re.comp he)
  have ha : Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle => (q.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hv : Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle =>
      gluingCollarOrthonormalCoord (gluingRadius C g) (P.seamAngularComplexChart k θ q.1.val) q.2) :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((Complex.continuous_re.comp ha).prodMk
        ((Complex.continuous_im.comp ha).div hw (fun q =>
          (gluingCollarWarp_pos P.radius_pos _).ne')))
  exact (hv.norm.inv₀ (fun q => (norm_pos_iff.2
    (gluingCollarOrthonormalCoord_ne_zero P.radius_pos _ q.2.coe_ne_zero)).ne')).smul hv

theorem nativeSeamCircleReparamInv_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle =>
      P.nativeSeamCircleReparamInv k θ q.1.val q.2) := by
  apply Continuous.subtype_mk
  have he : Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle =>
      P.seamAngularComplexChart k θ q.1.val) :=
    (P.seamAngularComplexChart k θ).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_fst) (fun q => q.1.property)
  have hw := (gluingCollarWarp_continuous (gluingRadius C g)).comp (Complex.continuous_re.comp he)
  have ha : Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle => (q.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hv : Continuous (fun q : (P.seamAngularComplexChart k θ).source × Circle =>
      gluingCollarOrthonormalComponents (gluingRadius C g)
        (P.seamAngularComplexChart k θ q.1.val) q.2) :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((Complex.continuous_re.comp ha).prodMk (hw.mul (Complex.continuous_im.comp ha)))
  exact (hv.norm.inv₀ (fun q => (norm_pos_iff.2
    (gluingCollarOrthonormalComponents_ne_zero P.radius_pos _ q.2.coe_ne_zero)).ne')).smul hv

/-- The base-dependent orthonormal-to-radial circle reparameterization is a
genuine homeomorphism, including the signed-radius-zero seam. -/
noncomputable def nativeSeamCircleReparamHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamAngularComplexChart k θ).source × Circle ≃ₜ
      (P.seamAngularComplexChart k θ).source × Circle where
  toFun q := (q.1, P.nativeSeamCircleReparam k θ q.1.val q.2)
  invFun q := (q.1, P.nativeSeamCircleReparamInv k θ q.1.val q.2)
  left_inv q := by simp only [P.nativeSeamCircleReparamInv_reparam]
  right_inv q := by simp only [P.nativeSeamCircleReparam_reparamInv]
  continuous_toFun := continuous_fst.prodMk (P.nativeSeamCircleReparam_continuous k θ)
  continuous_invFun := continuous_fst.prodMk (P.nativeSeamCircleReparamInv_continuous k θ)

theorem nativeUnitTangentParam_seamCircleReparam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (a : Circle) :
    P.nativeUnitTangentParam (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩) b hb
      (P.nativeSeamCircleReparam k θ b a) = P.nativeSeamUnitTangentParam k θ b hb a := by
  have heq : P.nativeSeamCircleReparam k θ b a =
      P.nativeUnitTangentAngle (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩)
        b hb (P.nativeSeamUnitTangentParam k θ b hb a) := by
    apply Subtype.ext
    change NormedSpace.normalize (gluingCollarOrthonormalCoord _ _ a) =
      NormedSpace.normalize (P.nativeUnitTangentCoord _ _ _ _)
    rw [P.nativeSeamUnitTangentCoord_param]
  rw [heq]
  exact P.nativeUnitTangentParam_angle _ _ b hb _

/-- Genuine source-times-circle coordinates for the native seam unit tangent
bundle, in the orthonormal radial/angular gauge. -/
noncomputable def nativeSeamUnitTangentBundleHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamAngularComplexChart k θ).source × Circle ≃ₜ
      P.NativeUnitTangentOver (P.seamAngularComplexChart k θ) :=
  (P.nativeSeamCircleReparamHomeomorph k θ).trans
    (P.nativeUnitTangentBundleHomeomorph (P.seamAngularComplexChart k θ) (Or.inr ⟨k, θ, rfl⟩))

theorem nativeSeamUnitTangentBundleHomeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (q : (P.seamAngularComplexChart k θ).source × Circle) :
    (P.nativeSeamUnitTangentBundleHomeomorph k θ q).val.val =
      TotalSpace.mk q.1.val (P.nativeSeamUnitTangentParam k θ q.1.val q.1.property q.2).val := by
  change TotalSpace.mk q.1.val (P.nativeUnitTangentParam _ _ q.1.val q.1.property
    (P.nativeSeamCircleReparam k θ q.1.val q.2)).val = _
  rw [P.nativeUnitTangentParam_seamCircleReparam]

/-- A literal coordinate-unit vector is exactly the native seam parameter
whose orthonormal components are that vector's radial/weighted-angular pair. -/
theorem nativeSeamUnitTangentParam_ofCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (v : ℂ)
    (hv : P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
      (P.seamAngularComplexChart k θ b) v v = 1) :
    P.nativeSeamUnitTangentParam k θ b hb
      ⟨gluingCollarOrthonormalComponents (gluingRadius C g) (P.seamAngularComplexChart k θ b) v,
        mem_sphere_zero_iff_norm.2 (gluingCollarOrthonormalComponents_norm_eq_one _ _ _ (by
          rwa [← P.gluingChartTangentForm_seam k θ]))⟩ =
      P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ)
        (Or.inr ⟨k, θ, rfl⟩) b hb v hv := by
  have heq : (⟨gluingCollarOrthonormalComponents (gluingRadius C g)
      (P.seamAngularComplexChart k θ b) v, mem_sphere_zero_iff_norm.2
        (gluingCollarOrthonormalComponents_norm_eq_one _ _ _ (by
          rwa [← P.gluingChartTangentForm_seam k θ]))⟩ : Circle) =
      P.nativeSeamUnitTangentAngle k θ b hb
        (P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ)
          (Or.inr ⟨k, θ, rfl⟩) b hb v hv) := by
    apply Subtype.ext
    exact (P.nativeSeamUnitTangentAngle_ofCoordinates k θ b hb v hv).symm
  rw [heq]
  exact P.nativeSeamUnitTangentParam_angle k θ b hb _

/-- The orthonormal native parameter is identified by literal coordinate
equality, including vectors transported from a genuine physical Fermi chart. -/
theorem nativeSeamUnitTangentParam_eq_ofCoordinates
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (a : Circle) (v : ℂ)
    (hv : P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
      (P.seamAngularComplexChart k θ b) v v = 1)
    (hcoord : v = gluingCollarOrthonormalCoord (gluingRadius C g)
      (P.seamAngularComplexChart k θ b) a) :
    P.nativeSeamUnitTangentParam k θ b hb a =
      P.nativeUnitTangentOfCoordinates (P.seamAngularComplexChart k θ)
        (Or.inr ⟨k, θ, rfl⟩) b hb v hv := by
  subst v
  rfl

theorem nativeSeamUnitTangentParam_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) :
    Continuous (P.nativeSeamUnitTangentParam k θ b hb) := by
  have hcoord : Continuous (fun a : Circle => gluingCollarOrthonormalCoord (gluingRadius C g)
      (P.seamAngularComplexChart k θ b) a) :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((Complex.continuous_re.comp continuous_subtype_val).prodMk
        ((Complex.continuous_im.comp continuous_subtype_val).div_const _))
  apply Continuous.subtype_mk
  exact (ContinuousLinearMap.continuous _).comp hcoord

theorem nativeSeamUnitTangentAngle_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) :
    Continuous (P.nativeSeamUnitTangentAngle k θ b hb) := by
  have hc : Continuous (P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b) :=
    (ContinuousLinearMap.continuous _).comp continuous_subtype_val
  apply Continuous.subtype_mk
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((Complex.continuous_re.comp hc).prodMk
      (continuous_const.mul (Complex.continuous_im.comp hc)))

/-- The true seam fiber's orthonormal circle chart. -/
noncomputable def nativeSeamUnitTangentFiberHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) :
    Circle ≃ₜ P.NativeUnitTangentFiber b where
  toFun := P.nativeSeamUnitTangentParam k θ b hb
  invFun := P.nativeSeamUnitTangentAngle k θ b hb
  left_inv := P.nativeSeamUnitTangentAngle_param k θ b hb
  right_inv := P.nativeSeamUnitTangentParam_angle k θ b hb
  continuous_toFun := P.nativeSeamUnitTangentParam_continuous k θ b hb
  continuous_invFun := P.nativeSeamUnitTangentAngle_continuous k θ b hb

/-- Angular-lift choices do not change the true native orthonormal unit
tangent on any genuine same-seam chart overlap. -/
theorem nativeSeamUnitTangentParam_angularChart_independent
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hb' : b ∈ (P.seamAngularComplexChart k ψ).source) (a : Circle) :
    P.nativeSeamUnitTangentParam k θ b hb a =
      P.nativeSeamUnitTangentParam k ψ b hb' a := by
  have hx : P.seamAngularComplexChart k θ b ∈
      ((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart k ψ)).source :=
    ⟨(P.seamAngularComplexChart k θ).map_source hb, by
      change (P.seamAngularComplexChart k θ).symm (P.seamAngularComplexChart k θ b) ∈
        (P.seamAngularComplexChart k ψ).source
      rw [(P.seamAngularComplexChart k θ).left_inv hb]
      exact hb'⟩
  have hre : (P.seamAngularComplexChart k ψ b).re =
      (P.seamAngularComplexChart k θ b).re := by
    simpa only [OpenPartialHomeomorph.trans_apply,
      (P.seamAngularComplexChart k θ).left_inv hb] using
      P.seamAngularComplexChart_transition_re k θ ψ hx
  unfold nativeSeamUnitTangentParam
  apply P.nativeUnitTangentOfCoordinates_overlap
  rw [(P.seamAngularComplexChart_transition_hasFDerivAt k θ ψ hx).fderiv,
    ContinuousLinearMap.id_apply]
  simp only [gluingCollarOrthonormalCoord, hre]

#print axioms nativeSeamUnitTangentParam
#print axioms nativeSeamUnitTangentAngle_ofCoordinates
#print axioms nativeSeamUnitTangentParam_angle
#print axioms nativeSeamUnitTangentBundleHomeomorph
#print axioms nativeSeamUnitTangentBundleHomeomorph_apply
#print axioms nativeSeamUnitTangentParam_ofCoordinates
#print axioms nativeSeamUnitTangentParam_eq_ofCoordinates
#print axioms nativeSeamUnitTangentFiberHomeomorph
#print axioms nativeSeamUnitTangentParam_angularChart_independent

end ExerciseGluingPreparation
end SystolicGrowth
