module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoPuncturedDiskOpenCover
public import Geometry.FermiDiskPositiveWinding

@[expose] public section

/-!
# Positive scaling of the two-punctured disk sides

The local chart of radius `r` is normalized by multiplication by `r⁻¹`.
These lemmas record that this positive scaling carries each actual side to
the correspondingly scaled side and is compatible with Fermi coordinates.
-/

namespace SystolicGrowth

theorem twoPuncturedDiskOverlapLower_smul (s α β : ℝ) :
    twoPuncturedDiskOverlapLower (s * α) (s * β) =
      s * twoPuncturedDiskOverlapLower α β := by
  simp only [twoPuncturedDiskOverlapLower]
  ring

theorem twoPuncturedDiskOverlapUpper_smul (s α β : ℝ) :
    twoPuncturedDiskOverlapUpper (s * α) (s * β) =
      s * twoPuncturedDiskOverlapUpper α β := by
  simp only [twoPuncturedDiskOverlapUpper]
  ring

/-- Scaling by `s ∈ (0,1]` takes the lower side to the lower side with
scaled puncture heights. -/
theorem twoPuncturedDiskLowerSide_smul {s α β : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ twoPuncturedDiskLowerSide α β) :
    s • z ∈ twoPuncturedDiskLowerSide (s * α) (s * β) := by
  rcases hz with ⟨⟨hzball, hzim⟩, hzα⟩
  have hzNorm : ‖z‖ < 1 := by
    change dist z 0 < 1 at hzball
    simpa only [dist_zero_right] using hzball
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change dist (s • z) 0 < 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0]
    calc
      s * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < 1 := hzNorm
  · change (s • z).im < twoPuncturedDiskOverlapUpper (s * α) (s * β)
    change z.im < twoPuncturedDiskOverlapUpper α β at hzim
    simp only [Complex.smul_im, smul_eq_mul, twoPuncturedDiskOverlapUpper_smul]
    exact mul_lt_mul_of_pos_left hzim hs0
  · intro hzEq
    apply hzα
    have hcenter : s • twoPuncturedDiskLeftCenter α =
        twoPuncturedDiskLeftCenter (s * α) := by
      apply Complex.ext <;> simp [twoPuncturedDiskLeftCenter]
    rw [← hcenter] at hzEq
    exact (smul_right_injective ℂ hs0.ne') hzEq

/-- Scaling by `s ∈ (0,1]` takes the upper side to the upper side with
scaled puncture heights. -/
theorem twoPuncturedDiskUpperSide_smul {s α β : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ twoPuncturedDiskUpperSide α β) :
    s • z ∈ twoPuncturedDiskUpperSide (s * α) (s * β) := by
  rcases hz with ⟨⟨hzball, hzim⟩, hzβ⟩
  have hzNorm : ‖z‖ < 1 := by
    change dist z 0 < 1 at hzball
    simpa only [dist_zero_right] using hzball
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change dist (s • z) 0 < 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0]
    calc
      s * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < 1 := hzNorm
  · change twoPuncturedDiskOverlapLower (s * α) (s * β) < (s • z).im
    change twoPuncturedDiskOverlapLower α β < z.im at hzim
    simp only [Complex.smul_im, smul_eq_mul, twoPuncturedDiskOverlapLower_smul]
    exact mul_lt_mul_of_pos_left hzim hs0
  · intro hzEq
    apply hzβ
    have hcenter : s • twoPuncturedDiskRightCenter β =
        twoPuncturedDiskRightCenter (s * β) := by
      apply Complex.ext <;> simp [twoPuncturedDiskRightCenter]
    rw [← hcenter] at hzEq
    exact (smul_right_injective ℂ hs0.ne') hzEq

/-- The radius-normalization instance of lower-side scaling. -/
theorem twoPuncturedDiskLowerSide_inv_smul {r α β : ℝ} (hr : 1 ≤ r)
    {z : ℂ} (hz : z ∈ twoPuncturedDiskLowerSide α β) :
    r⁻¹ • z ∈ twoPuncturedDiskLowerSide (r⁻¹ * α) (r⁻¹ * β) := by
  apply twoPuncturedDiskLowerSide_smul (inv_pos.mpr (zero_lt_one.trans_le hr))
    (inv_le_one_of_one_le₀ hr) hz

/-- The radius-normalization instance of upper-side scaling. -/
theorem twoPuncturedDiskUpperSide_inv_smul {r α β : ℝ} (hr : 1 ≤ r)
    {z : ℂ} (hz : z ∈ twoPuncturedDiskUpperSide α β) :
    r⁻¹ • z ∈ twoPuncturedDiskUpperSide (r⁻¹ * α) (r⁻¹ * β) := by
  apply twoPuncturedDiskUpperSide_smul (inv_pos.mpr (zero_lt_one.trans_le hr))
    (inv_le_one_of_one_le₀ hr) hz

/-- Fermi coordinates are unchanged when chart radii are absorbed into the
two axis scales and the complex coordinate is divided by that radius. -/
theorem orientedFermiDiskPoint_scaled (m a b r : ℝ) (hr : r ≠ 0)
    (z : ℂ) :
    orientedFermiDiskPoint m (a * r) (b * r) ((r⁻¹ : ℝ) • z) =
      orientedFermiDiskPoint m a b z := by
  have him : (a * r) * ((r⁻¹ : ℝ) • z).im = a * z.im := by
    rw [Complex.smul_im]
    simp only [smul_eq_mul]
    field_simp [hr]
  have hre : (b * r) * ((r⁻¹ : ℝ) • z).re = b * z.re := by
    rw [Complex.smul_re]
    simp only [smul_eq_mul]
    field_simp [hr]
  change gluingFinFermiPoint 1
      (m + (a * r) * ((r⁻¹ : ℝ) • z).im)
      ((b * r) * ((r⁻¹ : ℝ) • z).re) =
    gluingFinFermiPoint 1 (m + a * z.im) (b * z.re)
  rw [him, hre]

/-- The literal positive polar loop's Fermi-coordinate map scales by the
same positive factor as the coordinate disk. Its origin and phase are
unchanged. -/
theorem fermiPositivePolarCoordinate_scaled (m a b r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (ρ : ℝ) (θ : Circle) :
    fermiPositivePolarCoordinate m (a * r) (b * r)
        (mul_pos ha hr) (mul_pos hb hr) ρ θ =
      (r⁻¹ : ℝ) • fermiPositivePolarCoordinate m a b ha hb ρ θ := by
  let H := orientedFermiDiskHomeomorph m (a * r) (b * r)
    (mul_pos ha hr) (mul_pos hb hr)
  have hcenter : orientedFermiDiskPoint m (a * r) (b * r) 0 =
      orientedFermiDiskPoint m a b 0 := by
    simp [orientedFermiDiskPoint]
  change H.symm _ = _
  apply H.injective
  rw [H.apply_symm_apply]
  change gluingPolarPoint (orientedFermiDiskPoint m (a * r) (b * r) 0)
      (fermiPositivePolarAngle θ) ρ =
    orientedFermiDiskPoint m (a * r) (b * r)
      ((r⁻¹ : ℝ) • fermiPositivePolarCoordinate m a b ha hb ρ θ)
  rw [orientedFermiDiskPoint_scaled m a b r hr.ne'
    (fermiPositivePolarCoordinate m a b ha hb ρ θ)]
  rw [orientedFermiDiskPoint_positivePolarCoordinate]
  rw [hcenter]

#print axioms twoPuncturedDiskLowerSide_smul
#print axioms twoPuncturedDiskUpperSide_smul
#print axioms twoPuncturedDiskLowerSide_inv_smul
#print axioms twoPuncturedDiskUpperSide_inv_smul
#print axioms orientedFermiDiskPoint_scaled
#print axioms fermiPositivePolarCoordinate_scaled

end SystolicGrowth
