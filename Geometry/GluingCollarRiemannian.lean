module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarWarp
public import Mathlib.Topology.VectorBundle.Riemannian

@[expose] public section

/-!
# The continuous Riemannian form in a seam collar

The real coordinate model is `(t, θ)`, with tangent vectors in `ℝ × ℝ`.
The actual form is `dt² + sinh (r + |t|)² dθ²`. We construct a native
`Bundle.ContinuousRiemannianMetric` on its trivial tangent bundle. This is
only the coordinate collar metric field: no glued manifold, smooth tensor,
length metric, or curvature assertion is made. In particular, the absolute
value in the coefficient is retained at the seam.
-/

namespace SystolicGrowth

/-- The real two-dimensional collar coordinate and tangent model. -/
abbrev GluingCollarModel := ℝ × ℝ

/-- The actual continuous bilinear tangent form in collar coordinates. -/
noncomputable def gluingCollarTangentForm (r : ℝ) (p : GluingCollarModel) :
    GluingCollarModel →L[ℝ] GluingCollarModel →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (gluingCollarWarp r p.1) ^ 2 •
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem gluingCollarTangentForm_apply (r : ℝ) (p u v : GluingCollarModel) :
    gluingCollarTangentForm r p u v =
      u.1 * v.1 + (gluingCollarWarp r p.1) ^ 2 * u.2 * v.2 := by
  simp [gluingCollarTangentForm, mul_assoc]

theorem gluingCollarTangentForm_symm (r : ℝ) (p u v : GluingCollarModel) :
    gluingCollarTangentForm r p u v = gluingCollarTangentForm r p v u := by
  simp only [gluingCollarTangentForm_apply]
  ring

theorem gluingCollarTangentForm_self (r : ℝ) (p u : GluingCollarModel) :
    gluingCollarTangentForm r p u u =
      u.1 ^ 2 + (gluingCollarWarp r p.1) ^ 2 * u.2 ^ 2 := by
  simp only [gluingCollarTangentForm_apply]
  ring

theorem gluingCollarTangentForm_pos {r : ℝ} (hr : 0 < r)
    (p u : GluingCollarModel) (hu : u ≠ 0) :
    0 < gluingCollarTangentForm r p u u := by
  rw [gluingCollarTangentForm_self]
  have hw : 0 < (gluingCollarWarp r p.1) ^ 2 :=
    sq_pos_of_pos (gluingCollarWarp_pos hr p.1)
  by_cases h₁ : u.1 = 0
  · have h₂ : u.2 ≠ 0 := by
      intro h₂
      exact hu (Prod.ext h₁ h₂)
    simpa [h₁] using mul_pos hw (sq_pos_of_ne_zero h₂)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁)
      (mul_nonneg hw.le (sq_nonneg _))

/-- Continuity includes the seam `t = 0`; differentiability there is not asserted. -/
theorem gluingCollarTangentForm_continuous (r : ℝ) :
    Continuous (gluingCollarTangentForm r) := by
  letI : ContinuousAdd (GluingCollarModel →L[ℝ] GluingCollarModel →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd
      (GluingCollarModel →L[ℝ] GluingCollarModel →L[ℝ] ℝ) _
      (inferInstanceAs (AddGroup (GluingCollarModel →L[ℝ] GluingCollarModel →L[ℝ] ℝ)))
      (inferInstanceAs
        (IsTopologicalAddGroup (GluingCollarModel →L[ℝ] GluingCollarModel →L[ℝ] ℝ)))
  unfold gluingCollarTangentForm
  have hw : Continuous (fun p : GluingCollarModel => (gluingCollarWarp r p.1) ^ 2) :=
    ((gluingCollarWarp_continuous r).comp continuous_fst).pow 2
  have h₂ : Continuous (fun _ : GluingCollarModel =>
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) :=
    continuous_const
  exact continuous_const.add (hw.smul h₂)

/-- An explicit bound for the unit ellipsoid, in the unchanged product topology. -/
theorem gluingCollarTangentForm_unit_norm_le {r : ℝ} (hr : 0 < r)
    (p u : GluingCollarModel) (hu : gluingCollarTangentForm r p u u < 1) :
    ‖u‖ ≤ 1 + ((gluingCollarWarp r p.1) ^ 2)⁻¹ := by
  rw [gluingCollarTangentForm_self] at hu
  have hw : 0 < (gluingCollarWarp r p.1) ^ 2 :=
    sq_pos_of_pos (gluingCollarWarp_pos hr p.1)
  have hi : 0 < ((gluingCollarWarp r p.1) ^ 2)⁻¹ := inv_pos.mpr hw
  have h₁ : u.1 ^ 2 ≤ 1 := by
    have := mul_nonneg hw.le (sq_nonneg u.2)
    linarith
  have h₂ : u.2 ^ 2 < ((gluingCollarWarp r p.1) ^ 2)⁻¹ := by
    rw [← one_div, lt_div_iff₀ hw]
    nlinarith [sq_nonneg u.1]
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  constructor
  · exact (sq_le_one_iff_abs_le_one _).mp h₁ |>.trans (by linarith)
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u.2 - 1 / 2), sq_nonneg (u.2 + 1 / 2)]

theorem gluingCollarTangentForm_isVonNBounded {r : ℝ} (hr : 0 < r)
    (p : GluingCollarModel) :
    Bornology.IsVonNBounded ℝ {u : GluingCollarModel | gluingCollarTangentForm r p u u < 1} := by
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  exact ⟨1 + ((gluingCollarWarp r p.1) ^ 2)⁻¹,
    fun u hu => gluingCollarTangentForm_unit_norm_le hr p u hu⟩

/-- The explicit form as a continuous section of the native bilinear-form bundle. -/
theorem gluingCollarTangentForm_continuous_section (r : ℝ) :
    Continuous (fun p : GluingCollarModel =>
      Bundle.TotalSpace.mk' (GluingCollarModel →L[ℝ] GluingCollarModel →L[ℝ] ℝ) p
        (gluingCollarTangentForm r p :
          Bundle.Trivial GluingCollarModel GluingCollarModel p →L[ℝ]
            Bundle.Trivial GluingCollarModel GluingCollarModel p →L[ℝ] ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert (gluingCollarTangentForm_continuous r).continuousAt using 1
  funext q
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hs (w : GluingCollarModel) :
      ((Bundle.Trivial.trivialization GluingCollarModel ℝ).prod
        (Bundle.Trivial.trivialization GluingCollarModel ℝ)).symm q w = w := by
    let e := (Bundle.Trivial.trivialization GluingCollarModel ℝ).prod
      (Bundle.Trivial.trivialization GluingCollarModel ℝ)
    change e.symm q (e ⟨q, w⟩).2 = w
    exact e.symm_apply_apply_mk (by simp [e]) w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, hs]

/-- The actual continuous Riemannian metric in the real seam-collar chart. -/
noncomputable def gluingCollarContinuousRiemannianMetric {r : ℝ} (hr : 0 < r) :
    Bundle.ContinuousRiemannianMetric GluingCollarModel
      (Bundle.Trivial GluingCollarModel GluingCollarModel) where
  inner := gluingCollarTangentForm r
  symm := gluingCollarTangentForm_symm r
  pos := gluingCollarTangentForm_pos hr
  isVonNBounded := gluingCollarTangentForm_isVonNBounded hr
  continuous := gluingCollarTangentForm_continuous_section r

@[simp] theorem gluingCollarContinuousRiemannianMetric_inner {r : ℝ} (hr : 0 < r)
    (p u v : GluingCollarModel) :
    (gluingCollarContinuousRiemannianMetric hr).inner p u v =
      u.1 * v.1 + (gluingCollarWarp r p.1) ^ 2 * u.2 * v.2 :=
  gluingCollarTangentForm_apply r p u v

end SystolicGrowth

#print axioms SystolicGrowth.gluingCollarTangentForm_pos
#print axioms SystolicGrowth.gluingCollarTangentForm_continuous_section
#print axioms SystolicGrowth.gluingCollarContinuousRiemannianMetric
#print axioms SystolicGrowth.gluingCollarContinuousRiemannianMetric_inner
