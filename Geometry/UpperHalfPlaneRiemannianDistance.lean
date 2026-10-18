module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.UpperHalfPlaneRiemannianMetric

@[expose] public section

/-!
# Compatibility of the Poincaré tensor with the existing hyperbolic distance

The actual manifold path integral is identified with the audited Poincaré
speed integral. Endpoint length comparison and genuine length-realizing
segments then identify its path infimum with mathlib's original metric.
-/

open Bundle Manifold Set Riemannian UpperHalfPlane MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace SystolicGrowth

noncomputable section

/-- **Math.** The actual tangent norm is Poincaré speed measured in the
unchanged ambient complex norm. -/
theorem upperHalfPlanePoincareMetric_tangent_norm (z : ℍ)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) z) :
    letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
      ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
    ‖v‖ = @norm ℂ Complex.instNorm v / z.im := by
  letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  conv_lhs => rw [norm_tangent_eq_sqrt_metricInner upperHalfPlanePoincareMetric z v]
  change Real.sqrt (upperHalfPlanePoincareMetric.inner z v v) = _
  rw [upperHalfPlanePoincareMetric_inner, @real_inner_self_eq_norm_sq ℂ _ _ v,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (@norm_nonneg ℂ _ v),
    Real.sqrt_sq z.im_pos.le]

/-- **Math.** Differentiation in the existing singleton chart is ordinary
complex differentiation of the included real curve. -/
theorem upperHalfPlane_curve_mfderiv_eq_deriv {γ : ℝ → ℍ} {t : ℝ}
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1 =
      deriv (fun s => (γ s : ℂ)) t := by
  have hcomp := mfderiv_comp t
    ((upperHalfPlane_coe_contMDiff_real (γ t)).mdifferentiableAt (by simp)) hγ
  rw [upperHalfPlane_coe_mfderiv_real, mfderiv_eq_fderiv] at hcomp
  have happ := congrArg (fun f => f 1) hcomp
  change (fderiv ℝ (fun s => (γ s : ℂ)) t) 1 =
    (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t) 1 at happ
  exact happ.symm

/-- **Math.** Closed-interval smooth manifold paths have the literal
Poincaré integral as their actual Riemannian path length. -/
theorem upperHalfPlanePoincareMetric_pathELength {γ : ℝ → ℍ} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ)
      1 γ (Icc a b)) :
    letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
      ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (‖deriv (fun s => (γ s : ℂ)) t‖ / (γ t).im) := by
  letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t :=
    (hγ t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
      |>.mdifferentiableAt (by simp)
  change ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ₑ = _
  rw [← ofReal_norm, upperHalfPlanePoincareMetric_tangent_norm]
  congr 1
  exact congrArg (fun v : ℂ => ‖v‖ / (γ t).im)
    (upperHalfPlane_curve_mfderiv_eq_deriv hd)

/-- **Math.** Existing hyperbolic endpoint distance is bounded by the actual
Riemannian length of every closed-interval smooth competitor. -/
theorem upperHalfPlane_edist_le_poincare_pathELength {γ : ℝ → ℍ} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ)
      1 γ (Icc a b)) (hab : a ≤ b) :
    letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
      ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
    edist (γ a) (γ b) ≤ pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  have hα : ContDiffOn ℝ 1 (fun s => (γ s : ℂ)) (Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp
      ((upperHalfPlane_coe_contMDiff_real.of_le (by simp)).comp_contMDiffOn hγ)
  have h := hyperbolic_dist_le_poincare_lintegral hα hab
    (fun s _ => (γ s).im_pos)
  rw [upperHalfPlanePoincareMetric_pathELength hγ]
  simpa only [UpperHalfPlane.mk_coe, ← edist_dist, UpperHalfPlane.im] using h

/-- **Math.** The actual inverse singleton chart is smooth over the real
model throughout the open upper half-plane. -/
theorem upperHalfPlane_ofComplex_contMDiffAt_real {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      UpperHalfPlane.ofComplex z := by
  rw [_root_.contMDiffAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Filter.Tendsto.congr' (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using! tendsto_id
  · simpa using! contDiffAt_id.congr_of_eventuallyEq
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz)

/-- **Math.** The existing hyperbolic segment supplies an actual smooth
Riemannian competitor of length exactly the original hyperbolic edistance. -/
theorem upperHalfPlane_riemannianEDist_le_edist (z w : ℍ) :
    letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
      ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
    riemannianEDist (modelWithCornersSelf ℝ ℂ) z w ≤ edist z w := by
  letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  obtain ⟨α, hα, hpos, h0, h1, hlen, _⟩ := exists_hyperbolic_length_realizing_segment z w
  let γ : ℝ → ℍ := fun t => UpperHalfPlane.ofComplex (α t)
  have hcoe : (fun t => (γ t : ℂ)) = α := by
    funext t
    simp only [γ, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t), UpperHalfPlane.coe_mk]
  have hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ := by
    intro t
    exact ((upperHalfPlane_ofComplex_contMDiffAt_real (hpos t)).of_le (by simp)).comp t
      (contMDiffAt_iff_contDiffAt.mpr hα.contDiffAt)
  have hγ0 : γ 0 = z := by
    apply UpperHalfPlane.ext
    change (fun t => (γ t : ℂ)) 0 = _
    rw [hcoe, h0]
  have hγ1 : γ 1 = w := by
    apply UpperHalfPlane.ext
    change (fun t => (γ t : ℂ)) 1 = _
    rw [hcoe, h1]
  refine (riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 hγ1 zero_le_one).trans_eq ?_
  rw [upperHalfPlanePoincareMetric_pathELength hγ.contMDiffOn, hcoe]
  convert hlen using 1
  congr 1
  funext t
  rw [show (γ t).im = (α t).im from congrArg Complex.im (congrFun hcoe t)]

/-- **Math.** Every smooth path has length at least the original edistance,
so the actual Riemannian length infimum dominates that unchanged distance. -/
theorem upperHalfPlane_edist_le_riemannianEDist (z w : ℍ) :
    letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
      ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
    edist z w ≤ riemannianEDist (modelWithCornersSelf ℝ ℂ) z w := by
  letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  simp only [riemannianEDist, le_iInf_iff]
  intro γ hγ
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  simpa using upperHalfPlane_edist_le_poincare_pathELength
    (hγ.comp_contMDiffOn contMDiffOn_projIcc) zero_le_one

/-- **Math.** The Poincaré tensor induces exactly mathlib's existing hyperbolic
distance; no carrier topology or metric-space instance is replaced. -/
theorem upperHalfPlanePoincareMetric_isRiemannianDist :
    upperHalfPlanePoincareMetric.IsRiemannianDist := by
  letI : RiemannianBundle (fun z : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) z) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  refine ⟨fun z w => le_antisymm (upperHalfPlane_edist_le_riemannianEDist z w)
    (upperHalfPlane_riemannianEDist_le_edist z w)⟩

#print axioms upperHalfPlanePoincareMetric_tangent_norm
#print axioms upperHalfPlanePoincareMetric_pathELength
#print axioms upperHalfPlanePoincareMetric_isRiemannianDist

end
end SystolicGrowth
