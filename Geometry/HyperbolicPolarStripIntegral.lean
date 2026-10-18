module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicConeArea
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

/-!
# Exact hyperbolic polar-strip integral

The principal angular strip has width `2π`. Integrating its genuine
hyperbolic density `sinh r` gives `2π(cosh R - 1)`, both in real-product
coordinates and in the complex coordinates used by smooth area transfer.
-/

open Set MeasureTheory
open scoped ENNReal Topology

namespace SystolicGrowth

noncomputable section

/-- **Math.** The nonnegative hyperbolic radial density has exact mass
`cosh R - 1` on the positive radial interval. -/
theorem sinh_lintegral_Ioo {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ r : ℝ in Ioo 0 R, ENNReal.ofReal (Real.sinh r)) =
      ENNReal.ofReal (Real.cosh R - 1) := by
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  simpa only [hyperbolicConePolarWarp, div_self hpi, one_mul] using
    hyperbolicConePolarWarp_lintegral (a := 2 * Real.pi) (by positivity) hR

/-- **Math.** The full principal polar strip has hyperbolic area
`2π(cosh R - 1)`. -/
theorem hyperbolicPolarStrip_lintegral {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ p : ℝ × ℝ in Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (Real.sinh p.1)) =
      ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.sinh p.1)) :=
    (Real.continuous_sinh.comp continuous_fst).measurable.ennreal_ofReal
  change (∫⁻ p : ℝ × ℝ in Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal (Real.sinh p.1) ∂(volume : Measure ℝ).prod volume) = _
  rw [setLIntegral_prod _ hm.aemeasurable]
  simp only [setLIntegral_const, Real.volume_Ioo]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, sinh_lintegral_Ioo hR,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (Real.one_le_cosh R))]
  congr 1
  ring

/-- **Math.** The same exact strip area in complex coordinates. The
real/imaginary coordinate equivalence preserves actual Lebesgue volume. -/
theorem hyperbolicPolarPrincipalStrip_complex_lintegral {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ z : ℂ in {z | z.re ∈ Ioo 0 R ∧ z.im ∈ Ioo (-Real.pi) Real.pi},
      ENNReal.ofReal (Real.sinh z.re)) =
      ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) := by
  have heq := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal (Real.sinh p.1))
    (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi)
  exact heq.trans (hyperbolicPolarStrip_lintegral hR)

/-- **Math.** The actual subtype pullback of complex volume, weighted by
the hyperbolic polar density, has the exact disk-model mass. This is the
measure form consumed by the smooth disk-area transfer theorem. -/
theorem hyperbolicPolarPrincipalStrip_withDensity_univ {R : ℝ} (hR : 0 ≤ R) :
    (((volume : Measure ℂ).comap
      (Subtype.val : {z : ℂ | z.re ∈ Ioo 0 R ∧ z.im ∈ Ioo (-Real.pi) Real.pi} → ℂ)).withDensity
      (fun z => ENNReal.ofReal (Real.sinh z.val.re))) univ =
      ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) := by
  have hs : MeasurableSet {z : ℂ | z.re ∈ Ioo 0 R ∧ z.im ∈ Ioo (-Real.pi) Real.pi} :=
    (measurableSet_Ioo.preimage Complex.measurable_re).inter
      (measurableSet_Ioo.preimage Complex.measurable_im)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_subtype_comap hs (fun z : ℂ => ENNReal.ofReal (Real.sinh z.re))]
  exact hyperbolicPolarPrincipalStrip_complex_lintegral hR

#print axioms hyperbolicPolarStrip_lintegral
#print axioms hyperbolicPolarPrincipalStrip_complex_lintegral
#print axioms hyperbolicPolarPrincipalStrip_withDensity_univ

end
end SystolicGrowth
