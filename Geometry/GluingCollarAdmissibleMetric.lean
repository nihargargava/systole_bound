module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelMetric
public import Geometry.GluingCollarLipschitzLength
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Lipschitz-admissible distance in the actual collar plane

The admissible distance is the infimum of the genuine weighted speed
integrals over ordinary complex-coordinate Lipschitz curves on `[0,1]`.
Endpoint conditions and the Lipschitz constant are part of the indexing
set, not hypotheses asserting a distance or length comparison. Empty
indexing sets have infimum `⊤`, as usual for extended nonnegative reals.
The native C¹ near-minimizers construct the required admissible curves.
Their infimum equals the literal native collar distance by the proved
weighted length bound for every Lipschitz curve. No curvature claim follows.
No global complex metric instance is replaced here.
-/

open Set MeasureTheory Bundle Manifold
open scoped ENNReal NNReal Manifold Bundle

namespace SystolicGrowth

/-- Infimum of actual collar weighted lengths over coordinate curves
Lipschitz on the closed unit interval with their prescribed endpoints. -/
noncomputable def gluingCollarAdmissibleEDist (r : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (α : ℝ → ℂ) (_h0 : α 0 = z) (_h1 : α 1 = w)
    (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K α (Icc 0 1)),
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)))

/-- Every admissible curve bounds the admissible infimum by its literal
weighted speed integral. No finiteness or smoothness premise is needed. -/
theorem gluingCollarAdmissibleEDist_le_warp_length (r : ℝ) {z w : ℂ}
    {α : ℝ → ℂ} {K : ℝ≥0} (h0 : α 0 = z) (h1 : α 1 = w)
    (hLip : LipschitzOnWith K α (Icc 0 1)) :
    gluingCollarAdmissibleEDist r z w ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  unfold gluingCollarAdmissibleEDist
  exact iInf_le_of_le α (iInf_le_of_le h0 (iInf_le_of_le h1
    (iInf_le_of_le (show ∃ K : ℝ≥0, LipschitzOnWith K α (Icc 0 1) from ⟨K, hLip⟩)
      le_rfl)))

/-- Genuine global native C¹ near-minimizers are Lipschitz in the ordinary
complex coordinates on the compact interval and bound the admissible infimum. -/
theorem gluingCollarAdmissibleEDist_le_native {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarAdmissibleEDist r z w ≤ gluingCollarModelEDist hr z w := by
  classical
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
    gluingCollarModelRiemannianBundle hr
  by_contra hbad
  have hnear : riemannianEDist (modelWithCornersSelf ℝ ℂ) z w <
      gluingCollarAdmissibleEDist r z w := lt_of_not_ge hbad
  obtain ⟨α, h0, h1, hα, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hnear zero_lt_one
  obtain ⟨K, hLip⟩ := hα.contDiff.contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_Icc (0 : ℝ) 1) isCompact_Icc
  have hbound := gluingCollarAdmissibleEDist_le_warp_length r h0 h1 hLip
  rw [← gluingCollarModelPathELength_eq_lintegral hr] at hbound
  change gluingCollarAdmissibleEDist r z w ≤
    pathELength (modelWithCornersSelf ℝ ℂ) α 0 1 at hbound
  exact (not_lt_of_ge hbound) hlen

/-- In particular the admissible infimum is genuinely finite, so it cannot
be the empty-family value `⊤`. This follows from constructed native curves. -/
theorem gluingCollarAdmissibleEDist_lt_top {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarAdmissibleEDist r z w < ⊤ :=
  (gluingCollarAdmissibleEDist_le_native hr z w).trans_lt
    (gluingCollarModelEDist_lt_top hr z w)

/-- Every admissible weighted length bounds the literal native distance,
so taking its infimum gives the reverse metric comparison. -/
theorem gluingCollarModelEDist_le_admissible {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarModelEDist hr z w ≤ gluingCollarAdmissibleEDist r z w := by
  unfold gluingCollarAdmissibleEDist
  refine le_iInf fun α ↦ le_iInf fun h0 ↦ le_iInf fun h1 ↦ le_iInf fun hLip ↦ ?_
  obtain ⟨K, hK⟩ := hLip
  simpa only [h0, h1] using gluingCollarModelEDist_le_lipschitz_warp_length hr hK

/-- The ordinary-Lipschitz admissible warped distance is exactly the
constructed native C¹-path-infimum distance, including seam-zero points. -/
theorem gluingCollarAdmissibleEDist_eq_native {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarAdmissibleEDist r z w = gluingCollarModelEDist hr z w :=
  le_antisymm (gluingCollarAdmissibleEDist_le_native hr z w)
    (gluingCollarModelEDist_le_admissible hr z w)

/-- Literal native metric-instance consumer of the admissible distance
identity; the ambient Euclidean complex `edist` is not used. -/
theorem gluingCollarModelMetricSpace_edist_eq_admissible {r : ℝ} (hr : 0 < r)
    (z w : ℂ) :
    @edist ℂ (gluingCollarModelMetricSpace hr).toEDist z w =
      gluingCollarAdmissibleEDist r z w :=
  (gluingCollarAdmissibleEDist_eq_native hr z w).symm

#print axioms gluingCollarAdmissibleEDist_le_native
#print axioms gluingCollarAdmissibleEDist_lt_top
#print axioms gluingCollarModelEDist_le_admissible
#print axioms gluingCollarAdmissibleEDist_eq_native
#print axioms gluingCollarModelMetricSpace_edist_eq_admissible

end SystolicGrowth
