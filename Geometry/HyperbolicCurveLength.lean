module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Topology.Order.ProjIcc
public import Geometry.LipschitzCoordinateCalculus

@[expose] public section

/-!
# Poincare length controls hyperbolic endpoint distance

The comparison is proved from the actual upper-half-plane metric, not from
an assumed identification of that metric with a Riemannian path infimum.
Within derivatives handle the two endpoints of a merely within-C1 curve.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace SystolicGrowth

private theorem hyperbolic_distance_liminf_slope
    {α : ℝ → ℂ} {a b x : ℝ} (hα : ContDiffOn ℝ 1 α (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < (α t).im) (hx : x ∈ Ico a b)
    (z : UpperHalfPlane) {r : ℝ}
    (hr : ‖derivWithin α (Icc a b) x‖ / (α x).im < r) :
    ∃ᶠ t in 𝓝[>] x,
      slope (fun t => dist z (UpperHalfPlane.ofComplex (α t))) x t < r := by
  have hxc : x ∈ Icc a b := Ico_subset_Icc_self hx
  have hp : 0 < (α x).im := hpos x hxc
  have hdx : HasDerivWithinAt α (derivWithin α (Icc a b) x) (Ioi x) x :=
    ((hα x hxc).differentiableWithinAt one_ne_zero).hasDerivWithinAt
      |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)
  have hcont : Tendsto α (𝓝[>] x) (𝓝 (α x)) :=
    (hα.continuousOn x hxc).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)
  have hlim : Tendsto
      (fun t => ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im))
      (𝓝[>] x) (𝓝 (‖derivWithin α (Icc a b) x‖ / (α x).im)) := by
    have hs := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp hdx
    have hi := Complex.continuous_im.continuousAt.tendsto.comp hcont
    have hd := ((tendsto_const_nhds (x := (α x).im)).mul hi).sqrt
    have hh := hs.norm.div hd (by positivity)
    change Tendsto (fun t => ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im))
      (𝓝[>] x) (𝓝 (‖derivWithin α (Icc a b) x‖ /
        Real.sqrt ((α x).im * (α x).im))) at hh
    simpa only [Real.sqrt_mul_self hp.le] using hh
  have hlt : ∀ᶠ t in 𝓝[>] x,
      ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im) < r :=
    hlim (Iio_mem_nhds hr)
  apply Filter.Eventually.frequently
  filter_upwards [hlt, Icc_mem_nhdsGT_of_mem hx, self_mem_nhdsWithin] with t ht htc hxt
  have hpt : 0 < (α t).im := hpos t htc
  have hbound := UpperHalfPlane.dist_le_dist_coe_div_sqrt
    (UpperHalfPlane.mk (α t) hpt) (UpperHalfPlane.mk (α x) hp)
  have htri : dist z (UpperHalfPlane.mk (α t) hpt) -
      dist z (UpperHalfPlane.mk (α x) hp) ≤
      dist (UpperHalfPlane.mk (α t) hpt) (UpperHalfPlane.mk (α x) hp) := by
    have := dist_triangle z (UpperHalfPlane.mk (α x) hp)
      (UpperHalfPlane.mk (α t) hpt)
    rw [dist_comm (UpperHalfPlane.mk (α x) hp)] at this
    linarith
  have htx : 0 < t - x := sub_pos.mpr hxt
  rw [slope_def_field, UpperHalfPlane.ofComplex_apply_of_im_pos hp,
    UpperHalfPlane.ofComplex_apply_of_im_pos hpt]
  calc
    _ ≤ (dist (α t) (α x) / Real.sqrt ((α t).im * (α x).im)) / (t - x) :=
      div_le_div_of_nonneg_right (htri.trans hbound) htx.le
    _ = ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im) := by
      simp only [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos htx, dist_eq_norm]
      rw [mul_comm (α x).im (α t).im]
      ring
    _ < r := ht

private theorem hyperbolic_distance_liminf_slope_of_hasDerivAt
    {α : ℝ → ℂ} {a b x : ℝ} {K : ℝ≥0}
    (_hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < (α t).im) (hx : x ∈ Ico a b)
    (z : UpperHalfPlane) (hxd : HasDerivAt α (deriv α x) x) {r : ℝ}
    (hr : ‖deriv α x‖ / (α x).im < r) :
    ∃ᶠ t in 𝓝[>] x,
      slope (fun t => dist z (UpperHalfPlane.ofComplex (α t))) x t < r := by
  have hxc : x ∈ Icc a b := Ico_subset_Icc_self hx
  have hp : 0 < (α x).im := hpos x hxc
  have hdx : HasDerivWithinAt α (deriv α x) (Ioi x) x :=
    hxd.hasDerivWithinAt.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)
  have hcont : Tendsto α (𝓝[>] x) (𝓝 (α x)) :=
    (hα.continuousOn x hxc).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)
  have hlim : Tendsto
      (fun t => ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im))
      (𝓝[>] x) (𝓝 (‖deriv α x‖ / (α x).im)) := by
    have hs := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp hdx
    have hi := Complex.continuous_im.continuousAt.tendsto.comp hcont
    have hd := ((tendsto_const_nhds (x := (α x).im)).mul hi).sqrt
    have hh := hs.norm.div hd (by positivity)
    change Tendsto (fun t => ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im))
      (𝓝[>] x) (𝓝 (‖deriv α x‖ /
        Real.sqrt ((α x).im * (α x).im))) at hh
    simpa only [Real.sqrt_mul_self hp.le] using hh
  have hlt : ∀ᶠ t in 𝓝[>] x,
      ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im) < r :=
    hlim (Iio_mem_nhds hr)
  apply Filter.Eventually.frequently
  filter_upwards [hlt, Icc_mem_nhdsGT_of_mem hx, self_mem_nhdsWithin] with t ht htc hxt
  have hpt : 0 < (α t).im := hpos t htc
  have hbound := UpperHalfPlane.dist_le_dist_coe_div_sqrt
    (UpperHalfPlane.mk (α t) hpt) (UpperHalfPlane.mk (α x) hp)
  have htri : dist z (UpperHalfPlane.mk (α t) hpt) -
      dist z (UpperHalfPlane.mk (α x) hp) ≤
      dist (UpperHalfPlane.mk (α t) hpt) (UpperHalfPlane.mk (α x) hp) := by
    have ht' := dist_triangle z (UpperHalfPlane.mk (α x) hp)
      (UpperHalfPlane.mk (α t) hpt)
    rw [dist_comm (UpperHalfPlane.mk (α x) hp)] at ht'
    linarith
  have htx : 0 < t - x := sub_pos.mpr hxt
  rw [slope_def_field, UpperHalfPlane.ofComplex_apply_of_im_pos hp,
    UpperHalfPlane.ofComplex_apply_of_im_pos hpt]
  calc
    _ ≤ (dist (α t) (α x) / Real.sqrt ((α t).im * (α x).im)) / (t - x) :=
      div_le_div_of_nonneg_right (htri.trans hbound) htx.le
    _ = ‖slope α x t‖ / Real.sqrt ((α x).im * (α t).im) := by
      simp only [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos htx, dist_eq_norm]
      rw [mul_comm (α x).im (α t).im]
      ring
    _ < r := ht

private theorem hyperbolic_distance_deriv_le_of_lipschitz
    {α : ℝ → ℂ} {F : ℝ → ℝ} {a b x : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < (α t).im) (hx : x ∈ Ioo a b)
    (z : UpperHalfPlane)
    (hF : ∀ t ∈ Icc a b,
      F t = dist z (UpperHalfPlane.ofComplex (α t)))
    (hαd : DifferentiableAt ℝ α x) (hFd : DifferentiableAt ℝ F x) :
    deriv F x ≤ ‖deriv α x‖ / (α x).im := by
  have hx' : x ∈ Ico a b := ⟨le_of_lt hx.1, hx.2⟩
  have hfreq : ∀ r : ℝ, ‖deriv α x‖ / (α x).im < r →
      ∃ᶠ t in 𝓝[>] x, slope F x t < r := by
    intro r hr
    have h := hyperbolic_distance_liminf_slope_of_hasDerivAt hab hα hpos hx'
      z hαd.hasDerivAt hr
    have h' := h.and_eventually (Icc_mem_nhdsGT_of_mem hx')
    exact h'.mono fun t ⟨hlt, ht⟩ => by
      rw [slope_def_field] at hlt ⊢
      change (dist z (UpperHalfPlane.ofComplex (α t)) -
        dist z (UpperHalfPlane.ofComplex (α x))) / (t - x) < r at hlt
      change (F t - F x) / (t - x) < r
      rw [hF t ht, hF x (Ico_subset_Icc_self hx')]
      exact hlt
  by_contra hnot
  have hlt : ‖deriv α x‖ / (α x).im < deriv F x := lt_of_not_ge hnot
  let r := (‖deriv α x‖ / (α x).im + deriv F x) / 2
  have hr₁ : ‖deriv α x‖ / (α x).im < r := by dsimp [r]; linarith
  have hr₂ : r < deriv F x := by dsimp [r]; linarith
  have hfrequent := hfreq r hr₁
  have hlim : Tendsto (slope F x) (𝓝[>] x) (𝓝 (deriv F x)) :=
    (hasDerivAt_iff_tendsto_slope.mp hFd.hasDerivAt).mono_left
      (nhdsWithin_mono x (by intro t ht; exact ne_of_gt ht))
  have heventual : ∀ᶠ t in 𝓝[>] x, r < slope F x t := hlim (Ioi_mem_nhds hr₂)
  obtain ⟨t, hlow, hhigh⟩ := hfrequent.and_eventually heventual |>.exists
  exact (not_lt_of_ge hlow.le) hhigh

/-- Hyperbolic endpoint distance is bounded by Poincare length for every
interval-Lipschitz curve in the upper half-plane. This is the regularity
needed for finite-Fermi competitors, including nonsmooth seam contact. -/
theorem hyperbolic_dist_le_poincare_lintegral_of_lipschitz
    {α : ℝ → ℂ} {a b : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < (α t).im) :
    ENNReal.ofReal (dist (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab⟩))
      (UpperHalfPlane.mk (α b) (hpos b ⟨hab, le_rfl⟩))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (‖deriv α t‖ / (α t).im) := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have himCont : ContinuousOn (fun t => (α t).im) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn hα.continuousOn
  obtain ⟨m, hmpos, hmin⟩ := isCompact_Icc.exists_forall_le' himCont hpos
  let F : ℝ → ℝ := fun t => dist
    (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab'.le⟩))
    (UpperHalfPlane.ofComplex (α t))
  let LF : ℝ≥0 := Real.toNNReal ((K : ℝ) / m)
  have hFLip : LipschitzOnWith LF F (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have hys : m ≤ (α s).im := hmin s hs
    have hyt : m ≤ (α t).im := hmin t ht
    have hysPos : 0 < (α s).im := hpos s hs
    have hytPos : 0 < (α t).im := hpos t ht
    have hden : m ≤ Real.sqrt ((α s).im * (α t).im) := by
      have hmSq : m ^ 2 ≤ (α s).im * (α t).im := by nlinarith
      exact (Real.le_sqrt hmpos.le (mul_nonneg hysPos.le hytPos.le)).2 hmSq
    have hmetric := UpperHalfPlane.dist_le_dist_coe_div_sqrt
      (UpperHalfPlane.mk (α s) (hpos s hs)) (UpperHalfPlane.mk (α t) (hpos t ht))
    have hαst := hα.dist_le_mul s hs t ht
    have hdist : dist (UpperHalfPlane.ofComplex (α s))
        (UpperHalfPlane.ofComplex (α t)) ≤ ((K : ℝ) / m) * dist s t := by
      calc
        _ ≤ dist (α s) (α t) / Real.sqrt ((α s).im * (α t).im) := by
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hpos s hs),
            UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t ht)]
          exact hmetric
        _ ≤ dist (α s) (α t) / m :=
          div_le_div_of_nonneg_left (show 0 ≤ dist (α s) (α t) from dist_nonneg)
            hmpos hden
        _ ≤ ((K : ℝ) * dist s t) / m :=
          div_le_div_of_nonneg_right hαst hmpos.le
        _ = ((K : ℝ) / m) * dist s t := by ring
    have htri : dist (F s) (F t) ≤ dist
        (UpperHalfPlane.ofComplex (α s)) (UpperHalfPlane.ofComplex (α t)) := by
      rw [Real.dist_eq]
      calc
        |F s - F t| ≤ dist (UpperHalfPlane.ofComplex (α s))
            (UpperHalfPlane.ofComplex (α t)) := by
          have h := abs_dist_sub_le
            (UpperHalfPlane.ofComplex (α s)) (UpperHalfPlane.ofComplex (α t))
            (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab'.le⟩))
          simpa [F, abs_sub_comm, dist_comm] using h
        _ = dist (UpperHalfPlane.ofComplex (α s))
            (UpperHalfPlane.ofComplex (α t)) := rfl
    exact htri.trans (le_trans hdist (by
      gcongr
      exact Real.le_coe_toNNReal ((K : ℝ) / m)))
  let q : ℝ → ℝ := fun t => ‖deriv α t‖ / (α t).im
  have hqInt : IntervalIntegrable q volume a b := by
    have hderiv := lipschitzCoordinate_intervalIntegrable_deriv hab hα
    have hnorm := hderiv.norm
    have hinvIcc : ContinuousOn (fun t => ((α t).im)⁻¹) (Icc a b) :=
      (Complex.continuous_im.comp_continuousOn hα.continuousOn).inv₀
        (fun t ht => (hpos t ht).ne')
    have hinv : ContinuousOn (fun t => (α t).im⁻¹) (uIcc a b) := by
      simpa [uIcc_of_le hab] using hinvIcc
    convert hnorm.mul_continuousOn hinv using 1
    simp [q, div_eq_mul_inv]
  let f : ℝ → ℝ := fun t => F t
  have hFu : LipschitzOnWith LF f (uIcc a b) := by
    simpa only [f, uIcc_of_le hab] using hFLip
  have hfac := hFu.absolutelyContinuousOnInterval
  have hfInt : IntervalIntegrable (deriv f) volume a b := hfac.intervalIntegrable_deriv
  have hαdiff := SystolicGrowth.lipschitzComplex_differentiableAt_ae hab hα
  have hfdiff := ae_restrict_of_ae (s := uIcc a b) hfac.ae_differentiableAt
  rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc] at hfdiff
  rw [← restrict_Ioo_eq_restrict_Icc] at hαdiff
  have hderivLe : deriv f ≤ᵐ[volume.restrict (Ioo a b)] q := by
    filter_upwards [hαdiff, hfdiff, ae_restrict_mem measurableSet_Ioo]
      with t hαd hfd hmem
    have hfd := hfd (Ioo_subset_Icc_self hmem)
    have hle := hyperbolic_distance_deriv_le_of_lipschitz hab hα hpos hmem
      (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab'.le⟩))
      (fun s hs => by rfl)
      hαd hfd
    simpa [f, q] using hle
  have hderivLeIcc : deriv f ≤ᵐ[volume.restrict (Icc a b)] q := by
    rwa [← restrict_Ioo_eq_restrict_Icc]
  have hreal : dist (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab'.le⟩))
      (UpperHalfPlane.mk (α b) (hpos b ⟨hab'.le, le_rfl⟩)) ≤
        ∫ t in Icc a b, q t := by
    have hmono := intervalIntegral.integral_mono_ae_restrict hab'.le hfInt hqInt hderivLeIcc
    have hFTC := hfac.integral_deriv_eq_sub
    have hFb : f b = dist
        (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab'.le⟩))
        (UpperHalfPlane.mk (α b) (hpos b ⟨hab'.le, le_rfl⟩)) := by
      simp [f, F, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos b ⟨hab'.le, le_rfl⟩)]
    have hstart : UpperHalfPlane.ofComplex (α a) =
        UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab'.le⟩) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos (hpos a ⟨le_rfl, hab'.le⟩)
    have hFa : f a = 0 := by simp [f, F, hstart]
    rw [hFTC, hFa, hFb] at hmono
    have hIccEq : (∫ t in a..b, q t) = ∫ t in Icc a b, q t := by
      rw [intervalIntegral.integral_of_le hab'.le, restrict_Ioc_eq_restrict_Icc]
    rw [hIccEq] at hmono
    simpa only [sub_zero] using hmono
  have hqRestricted : Integrable q (volume.restrict (Icc a b)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hqInt
  apply (ENNReal.ofReal_le_ofReal hreal).trans_eq
  rw [ofReal_integral_eq_lintegral_ofReal hqRestricted]
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact div_nonneg (norm_nonneg _) (hpos t ht).le

/-- The actual hyperbolic endpoint distance is bounded by the integral of
the Poincare speed of a curve that is C1 only on the closed parameter interval. -/
theorem hyperbolic_dist_le_poincare_lintegral {α : ℝ → ℂ} {a b : ℝ}
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hab : a ≤ b)
    (hpos : ∀ t ∈ Icc a b, 0 < (α t).im) :
    ENNReal.ofReal (dist (UpperHalfPlane.mk (α a) (hpos a ⟨le_rfl, hab⟩))
      (UpperHalfPlane.mk (α b) (hpos b ⟨hab, le_rfl⟩))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (‖deriv α t‖ / (α t).im) := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  let q : ℝ → ℝ := fun t => ‖derivWithin α (Icc a b) t‖ / (α t).im
  have hq : ContinuousOn q (Icc a b) :=
    ((hα.derivWithin (m := 0) (uniqueDiffOn_Icc hab') (by simp)).continuousOn.norm).div
      (Complex.continuous_im.comp_continuousOn hα.continuousOn)
      (fun t ht => (hpos t ht).ne')
  let Q : ℝ → ℝ := fun t => q (projIcc a b hab'.le t)
  have hQ : Continuous Q :=
    (continuousOn_iff_continuous_restrict.mp hq).comp continuous_projIcc
  have hQeq : ∀ t ∈ Icc a b, Q t = q t := by
    intro t ht
    dsimp only [Q]
    rw [projIcc_of_mem hab'.le ht]
  let B : ℝ → ℝ := fun t => ∫ s in a..t, Q s
  have hBder : ∀ t, HasDerivAt B (Q t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable _ _)
      hQ.stronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
  have hf : ContinuousOn (fun t => dist (UpperHalfPlane.ofComplex (α a))
      (UpperHalfPlane.ofComplex (α t))) (Icc a b) := by
    have hlift : ContinuousOn (fun t => UpperHalfPlane.ofComplex (α t)) (Icc a b) := by
      apply UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr
      apply hα.continuousOn.congr
      intro t ht
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos t ht),
        UpperHalfPlane.coe_mk]
    exact continuous_dist.comp_continuousOn (continuousOn_const.prodMk hlift)
  have hend : dist (UpperHalfPlane.ofComplex (α a))
      (UpperHalfPlane.ofComplex (α b)) ≤ B b := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hf
      (B' := Q) (B := B)
    · simp [B]
    · exact fun t _ => (hBder t).continuousAt.continuousWithinAt
    · intro t _
      exact (hBder t).hasDerivWithinAt
    · intro t ht r hr
      rw [hQeq t (Ico_subset_Icc_self ht)] at hr
      exact hyperbolic_distance_liminf_slope hα hpos ht _ hr
    · exact ⟨hab'.le, le_rfl⟩
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hpos a ⟨le_rfl, hab'.le⟩),
    UpperHalfPlane.ofComplex_apply_of_im_pos (hpos b ⟨hab'.le, le_rfl⟩)] at hend
  apply (ENNReal.ofReal_le_ofReal hend).trans_eq
  rw [show B b = ∫ t in Icc a b, q t by
    dsimp only [B]
    rw [intervalIntegral.integral_of_le hab'.le, restrict_Ioc_eq_restrict_Icc]
    exact integral_congr_ae (by
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      exact hQeq t ht)]
  rw [ofReal_integral_eq_lintegral_ofReal hq.integrableOn_Icc]
  · apply lintegral_congr_ae
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    dsimp only [q]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact div_nonneg (norm_nonneg _) (hpos t ht).le

#print axioms hyperbolic_dist_le_poincare_lintegral
#print axioms hyperbolic_dist_le_poincare_lintegral_of_lipschitz

end SystolicGrowth
