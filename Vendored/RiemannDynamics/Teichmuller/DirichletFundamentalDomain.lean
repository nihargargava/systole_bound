module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

/-
## Vendoring provenance

The Dirichlet-domain and null-bisector proofs in this file are ported from
`RiemannDynamics/Teichmuller/FuchsianGeometry/Dirichlet.lean` at immutable upstream commit
`b3fa37cc0f18a23ea66b654ea3f73eb472129010` of
https://github.com/will1491/RiemannDynamics. The upstream file is Apache-2.0 licensed.
Imports and the namespace were reduced for the vendored location. The final a.e.-tiling and
`IsFundamentalDomain` declarations are a local adaptation of those upstream ingredients that
avoids the upstream compactness/Mumford dependency.
-/

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Dirichlet domains as measurable fundamental domains

For a properly discontinuous, free subgroup of `SL(2, ℝ)`, the closed Dirichlet domain covers
the upper half plane and distinct translates overlap only on volume-null bisectors. This produces
a `MeasureTheory.IsFundamentalDomain` without the Mumford compactness stack.
-/

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth.Vendored.RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-- The **Dirichlet domain** of `Γ` centered at `τ₀`: the points at least as close to `τ₀`
as to any other point of its `Γ`-orbit. -/
def dirichletDomain (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Set UpperHalfPlane :=
  {τ | ∀ γ : Γ, dist τ τ₀ ≤ dist τ (γ • τ₀)}

/-- Membership in the Dirichlet domain, unfolded: `τ` belongs exactly when no point of the
`Γ`-orbit of `τ₀` is strictly closer to `τ` than `τ₀` itself. -/
theorem mem_dirichletDomain {τ : UpperHalfPlane} :
    τ ∈ dirichletDomain Γ τ₀ ↔ ∀ γ : Γ, dist τ τ₀ ≤ dist τ (γ • τ₀) :=
  Iff.rfl

/-! ## Basepoint membership, closedness, tiling -/

/-- The center lies in its own Dirichlet domain: no orbit point can be closer to `τ₀` than
the distance `0` from `τ₀` to itself. -/
theorem basepoint_mem_dirichletDomain : τ₀ ∈ dirichletDomain Γ τ₀ := by
  intro γ
  rw [dist_self]
  exact dist_nonneg

/-- The Dirichlet domain is closed: it is an intersection, over the group, of the closed
half-planes `{τ | dist τ τ₀ ≤ dist τ (γ • τ₀)}`. -/
theorem isClosed_dirichletDomain (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : IsClosed (dirichletDomain Γ τ₀) := by
  have h : dirichletDomain Γ τ₀ =
      ⋂ γ : Γ, {τ : UpperHalfPlane | dist τ τ₀ ≤ dist τ (γ • τ₀)} := by
    ext τ
    simp only [dirichletDomain, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun γ =>
    isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

/-- **Tiling**: every point has a `Γ`-translate inside the Dirichlet domain. The orbit point
of `τ₀` nearest to `τ` exists because only finitely many translates of `τ₀` enter the closed
ball of radius `dist τ τ₀` about `τ`. -/
theorem exists_smul_mem_dirichletDomain (hΓ : ProperlyDiscontinuousSMul Γ UpperHalfPlane)
    (τ₀ τ : UpperHalfPlane) : ∃ γ : Γ, γ • τ ∈ dirichletDomain Γ τ₀ := by
  classical
  have hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall τ (dist τ τ₀)).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  have hS : {γ : ↥Γ | dist τ (γ • τ₀) ≤ dist τ τ₀}.Finite := by
    refine hfin1.subset ?_
    intro γ hγ
    refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hγ
  have h1S : (1 : ↥Γ) ∈ {γ : ↥Γ | dist τ (γ • τ₀) ≤ dist τ τ₀} := by
    simp only [Set.mem_setOf_eq, one_smul, le_refl]
  obtain ⟨γ₀, hγ₀S, hγ₀min⟩ :=
    Set.exists_min_image _ (fun γ : ↥Γ => dist τ (γ • τ₀)) hS ⟨1, h1S⟩
  have hglobal : ∀ γ : ↥Γ, dist τ (γ₀ • τ₀) ≤ dist τ (γ • τ₀) := by
    intro γ
    by_cases hγ : dist τ (γ • τ₀) ≤ dist τ τ₀
    · exact hγ₀min γ hγ
    · exact le_trans hγ₀S (le_of_lt (not_le.mp hγ))
  refine ⟨γ₀⁻¹, ?_⟩
  intro γ
  have e1 : dist (γ₀⁻¹ • τ) τ₀ = dist τ (γ₀ • τ₀) := by
    calc dist (γ₀⁻¹ • τ) τ₀ = dist (γ₀ • γ₀⁻¹ • τ) (γ₀ • τ₀) := (dist_smul γ₀ _ _).symm
      _ = dist τ (γ₀ • τ₀) := by rw [smul_inv_smul]
  have e2 : dist (γ₀⁻¹ • τ) (γ • τ₀) = dist τ ((γ₀ * γ) • τ₀) := by
    calc dist (γ₀⁻¹ • τ) (γ • τ₀) = dist (γ₀ • γ₀⁻¹ • τ) (γ₀ • γ • τ₀) :=
        (dist_smul γ₀ _ _).symm
      _ = dist τ ((γ₀ * γ) • τ₀) := by rw [smul_inv_smul, mul_smul]
  rw [e1, e2]
  exact hglobal (γ₀ * γ)

/-- Vertical lines in `ℂ` are volume-null. -/
theorem volume_re_line_eq_zero (r : ℝ) : volume {w : ℂ | w.re = r} = 0 := by
  have h : {w : ℂ | w.re = r} =
      Complex.measurableEquivRealProd ⁻¹' ({r} ×ˢ (Set.univ : Set ℝ)) := by
    ext w
    simp [Complex.measurableEquivRealProd_apply, Set.mem_prod]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton r).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- Level sets of `normSq (· - c)` in `ℂ` are volume-null: they are empty or spheres. -/
theorem volume_normSq_levelSet_eq_zero (c : ℂ) (k : ℝ) :
    volume {w : ℂ | Complex.normSq (w - c) = k} = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · have h : {w : ℂ | Complex.normSq (w - c) = k} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ Complex.normSq_nonneg (w - c)) (not_le.mpr hk)
    rw [h, measure_empty]
  · have h : {w : ℂ | Complex.normSq (w - c) = k} = Metric.sphere c (Real.sqrt k) := by
      ext w
      rw [Set.mem_setOf_eq, Metric.mem_sphere, dist_eq_norm]
      constructor
      · intro h
        rw [← Real.sqrt_sq (norm_nonneg (w - c)), Complex.sq_norm, h]
      · intro h
        rw [← Complex.sq_norm, h, Real.sq_sqrt hk]
    rw [h]
    exact Measure.addHaar_sphere volume c _

/-- A subset of the upper half plane whose complex image is Lebesgue-null is null for the
hyperbolic measure: the latter is a density against the pullback of the Lebesgue measure. -/
theorem volume_eq_zero_of_coe_image_null {s : Set UpperHalfPlane}
    (h : volume (UpperHalfPlane.coe '' s) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_def]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [UpperHalfPlane.measurableEmbedding_coe.comap_apply]
  exact h

/-- The perpendicular bisector of two distinct points of the upper half plane lies on a
volume-null subset of `ℂ`: equidistance transforms under `cosh_dist` into a real quadratic
equation whose solution set is a vertical line (equal heights) or a circle centered on the
real axis (distinct heights). -/
theorem exists_null_carrier_bisector (a b : UpperHalfPlane) (hab : a ≠ b) :
    ∃ S : Set ℂ, volume S = 0 ∧
      ∀ τ : UpperHalfPlane, dist τ a = dist τ b → (τ : ℂ) ∈ S := by
  have key : ∀ τ : UpperHalfPlane, dist τ a = dist τ b →
      b.im * (((τ : ℂ).re - (a : ℂ).re) ^ 2 + (τ.im - a.im) ^ 2) =
      a.im * (((τ : ℂ).re - (b : ℂ).re) ^ 2 + (τ.im - b.im) ^ 2) := by
    intro τ hd
    have hy : 0 < τ.im := τ.im_pos
    have hA : 0 < a.im := a.im_pos
    have hB : 0 < b.im := b.im_pos
    have hcosh := congrArg Real.cosh hd
    rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hcosh
    have h1 : dist (τ : ℂ) (a : ℂ) ^ 2 / (2 * τ.im * a.im) =
        dist (τ : ℂ) (b : ℂ) ^ 2 / (2 * τ.im * b.im) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h1
    have h2 : (2 * τ.im) * (b.im * dist (τ : ℂ) (a : ℂ) ^ 2) =
        (2 * τ.im) * (a.im * dist (τ : ℂ) (b : ℂ) ^ 2) := by linear_combination h1
    have hkey := mul_left_cancel₀ (by positivity : (2 * τ.im : ℝ) ≠ 0) h2
    have hda : dist (τ : ℂ) (a : ℂ) ^ 2 =
        ((τ : ℂ).re - (a : ℂ).re) ^ 2 + ((τ : ℂ).im - (a : ℂ).im) ^ 2 := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    have hdb : dist (τ : ℂ) (b : ℂ) ^ 2 =
        ((τ : ℂ).re - (b : ℂ).re) ^ 2 + ((τ : ℂ).im - (b : ℂ).im) ^ 2 := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hda, hdb] at hkey
    simpa only [UpperHalfPlane.coe_im] using hkey
  by_cases hAB : a.im = b.im
  · -- equal heights: the bisector lies on a vertical line
    have hpq : (a : ℂ).re ≠ (b : ℂ).re := by
      intro h
      apply hab
      apply UpperHalfPlane.ext
      apply Complex.ext h
      rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      exact hAB
    refine ⟨{w : ℂ | w.re = ((a : ℂ).re + (b : ℂ).re) / 2}, volume_re_line_eq_zero _, ?_⟩
    intro τ hd
    have hkey := key τ hd
    rw [Set.mem_setOf_eq]
    have hB : 0 < b.im := b.im_pos
    have hsq : ((τ : ℂ).re - (a : ℂ).re) ^ 2 = ((τ : ℂ).re - (b : ℂ).re) ^ 2 := by
      have hcancel := mul_left_cancel₀ hB.ne'
        (by linear_combination hkey
          + (((τ : ℂ).re - (b : ℂ).re) ^ 2 + (τ.im - b.im) ^ 2) * hAB :
          b.im * (((τ : ℂ).re - (a : ℂ).re) ^ 2 + (τ.im - a.im) ^ 2) =
          b.im * (((τ : ℂ).re - (b : ℂ).re) ^ 2 + (τ.im - b.im) ^ 2))
      have him : (τ.im - a.im) ^ 2 = (τ.im - b.im) ^ 2 := by rw [hAB]
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact absurd (by linarith) hpq
    · linarith
  · -- distinct heights: the bisector lies on a circle centered on the real axis
    obtain ⟨c, hc⟩ : ∃ c : ℝ,
        c = ((a : ℂ).re * b.im - (b : ℂ).re * a.im) / (b.im - a.im) := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = (b.im * ((a : ℂ).re ^ 2 + a.im ^ 2)
        - a.im * ((b : ℂ).re ^ 2 + b.im ^ 2)) / (b.im - a.im) := ⟨_, rfl⟩
    refine ⟨{w : ℂ | Complex.normSq (w - (c : ℂ)) = c ^ 2 - e},
      volume_normSq_levelSet_eq_zero _ _, ?_⟩
    intro τ hd
    have hkey := key τ hd
    have hBA : b.im - a.im ≠ 0 := sub_ne_zero.mpr fun h => hAB h.symm
    rw [Set.mem_setOf_eq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [UpperHalfPlane.coe_im]
    have hG' : (b.im - a.im) * (τ : ℂ).re ^ 2
        - 2 * ((a : ℂ).re * b.im - (b : ℂ).re * a.im) * (τ : ℂ).re
        + (b.im - a.im) * τ.im ^ 2
        + (b.im * (((a : ℂ).re) ^ 2 + a.im ^ 2) - a.im * (((b : ℂ).re) ^ 2 + b.im ^ 2))
        = 0 := by linear_combination hkey
    have hG : (τ : ℂ).re ^ 2 - 2 * c * (τ : ℂ).re + τ.im ^ 2 + e = 0 := by
      rw [hc, he]
      field_simp
      linear_combination hG'
    linear_combination hG

/-- **Bisectors are volume-null** in the upper half plane. -/
theorem volume_bisector_eq_zero (a b : UpperHalfPlane) (hab : a ≠ b) :
    volume {τ : UpperHalfPlane | dist τ a = dist τ b} = 0 := by
  obtain ⟨S, hS0, hsub⟩ := exists_null_carrier_bisector a b hab
  apply volume_eq_zero_of_coe_image_null
  refine measure_mono_null ?_ hS0
  rintro w ⟨τ, hτ, rfl⟩
  exact hsub τ hτ

/-! ## Almost-everywhere tiling -/

/-- Distinct translates of a Dirichlet domain overlap only on the perpendicular bisector of
`τ₀` and its translate, hence are almost everywhere disjoint when the basepoint stabilizer is
trivial. -/
theorem aedisjoint_smul_dirichletDomain
    (hfree : ∀ γ : Γ, γ • τ₀ = τ₀ → γ = 1) (γ : Γ) (hγ : γ ≠ 1) :
    AEDisjoint volume (γ • dirichletDomain Γ τ₀) (dirichletDomain Γ τ₀) := by
  letI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane
      (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  rw [AEDisjoint]
  refine measure_mono_null ?_ (volume_bisector_eq_zero τ₀ (γ • τ₀) ?_)
  · rintro z ⟨hzγ, hz⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hzγ
    have hforward : dist z τ₀ ≤ dist z (γ • τ₀) := hz γ
    have hbackward : dist z (γ • τ₀) ≤ dist z τ₀ := by
      have h := hzγ γ⁻¹
      calc
        dist z (γ • τ₀) = dist (γ⁻¹ • z) (γ⁻¹ • (γ • τ₀)) :=
          (dist_smul γ⁻¹ z (γ • τ₀)).symm
        _ = dist (γ⁻¹ • z) τ₀ := by rw [inv_smul_smul]
        _ ≤ dist (γ⁻¹ • z) (γ⁻¹ • τ₀) := h
        _ = dist z τ₀ := dist_smul γ⁻¹ z τ₀
    exact le_antisymm hforward hbackward
  · intro h
    exact hγ (hfree γ h.symm)

/-- For a properly discontinuous free action, the closed Dirichlet domain is a measurable
fundamental domain for hyperbolic area. -/
theorem isFundamentalDomain_dirichletDomain
    (hproper : ProperlyDiscontinuousSMul Γ UpperHalfPlane)
    (hfree : ∀ γ : Γ, γ • τ₀ = τ₀ → γ = 1) :
    IsFundamentalDomain Γ (dirichletDomain Γ τ₀) volume := by
  letI : SMulInvariantMeasure Γ UpperHalfPlane volume :=
    ⟨fun c s hs => SMulInvariantMeasure.measure_preimage_smul
      (M := GL (Fin 2) ℝ)
      (Matrix.SpecialLinearGroup.mapGL ℝ
        (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)) hs⟩
  refine IsFundamentalDomain.mk''
    (isClosed_dirichletDomain Γ τ₀).measurableSet.nullMeasurableSet
    (Filter.Eventually.of_forall (exists_smul_mem_dirichletDomain hproper τ₀))
    (aedisjoint_smul_dirichletDomain hfree)
    (fun γ => (measurePreserving_smul γ (volume : Measure UpperHalfPlane)).quasiMeasurePreserving)

end SystolicGrowth.Vendored.RiemannDynamics
