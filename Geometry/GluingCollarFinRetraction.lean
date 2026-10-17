module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteBandDistance

@[expose] public section

/-!
# Augmented fin quotient and its source retraction

The AB04 approximant identifies entire adjacent fins, including their
interiors. Its retraction first clips transverse coordinates to the strip
and then applies the inverse band map. The retraction agrees on every
identified fin point and recovers every embedded source point exactly.
-/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace SystolicGrowth

/-- Clip a Fermi point to the variable-width strip while preserving its
radial coordinate. -/
noncomputable def gluingCollarFinStripClamp (r ε : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re, gluingCollarClampReal (ε * gluingCollarWarp r z.re) z.im⟩

@[simp] theorem gluingCollarFinStripClamp_re (r ε : ℝ) (z : ℂ) :
    (gluingCollarFinStripClamp r ε z).re = z.re := rfl

@[simp] theorem gluingCollarFinStripClamp_im (r ε : ℝ) (z : ℂ) :
    (gluingCollarFinStripClamp r ε z).im =
      gluingCollarClampReal (ε * gluingCollarWarp r z.re) z.im := rfl

theorem gluingCollarClampReal_eq_upper {a u : ℝ} (ha : 0 ≤ a) (hu : a ≤ u) :
    gluingCollarClampReal a u = a := by
  rw [gluingCollarClampReal, min_eq_left hu, max_eq_right (by linarith)]

theorem gluingCollarClampReal_eq_lower {a u : ℝ} (ha : 0 ≤ a) (hu : u ≤ -a) :
    gluingCollarClampReal a u = -a := by
  rw [gluingCollarClampReal, min_eq_right (by linarith), max_eq_left hu]

/-- Simultaneously varying the transverse coordinate and the strip half-width
changes the clipped coordinate by at most their larger change. -/
theorem gluingCollarClampReal_abs_sub_le (a b u v : ℝ) :
    |gluingCollarClampReal a u - gluingCollarClampReal b v| ≤
      max |a - b| |u - v| := by
  have hmax := abs_max_sub_max_le_max (-a) (min a u) (-b) (min b v)
  have hmin := abs_min_sub_min_le_max a u b v
  have hneg : |-a - -b| = |a - b| := by
    rw [neg_sub_neg, abs_sub_comm]
  rw [hneg] at hmax
  exact hmax.trans (max_le (le_max_left _ _ ) hmin)

/-- At every common differentiability point, variable-width clipping bounds
the transverse derivative by the larger input/half-width derivative. This
also covers contact points where neither clipping branch is locally fixed. -/
theorem gluingCollarClampReal_deriv_abs_le
    {a u : ℝ → ℝ} {t a' u' v' : ℝ}
    (ha : HasDerivAt a a' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt (fun s => gluingCollarClampReal (a s) (u s)) v' t) :
    |v'| ≤ max |a'| |u'| := by
  let v : ℝ → ℝ := fun s => gluingCollarClampReal (a s) (u s)
  have hslope (s : ℝ) : |slope v t s| ≤ max |slope a t s| |slope u t s| := by
    by_cases hst : s = t
    · subst s
      simp [slope]
    · have hden : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
      have h := gluingCollarClampReal_abs_sub_le (a s) (a t) (u s) (u t)
      simp only [slope_def_field, abs_div]
      rw [max_div_div_right (le_of_lt hden)]
      exact (div_le_div_iff_of_pos_right hden).2 h
  exact le_of_tendsto_of_tendsto hv.tendsto_slope.abs
    (ha.tendsto_slope.abs.max hu.tendsto_slope.abs)
    (Filter.Eventually.of_forall hslope)

/-- The scalar Fermi speed estimate used after clipping: contraction of the
horizontal weight and a transverse derivative bounded by the larger original
derivative or `δ` times the radial derivative cost at most `1+δ`. -/
theorem gluingCollarFinStripClamp_pointwise_speed_le
    {C C' δ p q q' : ℝ} (hC : 1 ≤ C) (hC' : 0 ≤ C')
    (hweight : C' ≤ C) (hδ : 0 ≤ δ)
    (htransverse : |q'| ≤ max (δ * |p|) |q|) :
    Real.sqrt (p ^ 2 * C' ^ 2 + q' ^ 2) ≤
      (1 + δ) * Real.sqrt (p ^ 2 * C ^ 2 + q ^ 2) := by
  have hq : q' ^ 2 ≤ δ ^ 2 * p ^ 2 + q ^ 2 := by
    by_cases h : δ * |p| ≤ |q|
    · rw [max_eq_right h] at htransverse
      have hs := sq_le_sq₀ (abs_nonneg q') (abs_nonneg q) |>.2 htransverse
      simp only [sq_abs] at hs
      nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg p)]
    · rw [max_eq_left (le_of_not_ge h)] at htransverse
      have hs := sq_le_sq₀ (abs_nonneg q') (mul_nonneg hδ (abs_nonneg p))
        |>.2 htransverse
      simp only [mul_pow, sq_abs] at hs
      nlinarith [sq_nonneg q]
  have hweightSq : C' ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ hC' (by linarith)).2 hweight
  have hhorizontal : p ^ 2 * C' ^ 2 ≤ p ^ 2 * C ^ 2 :=
    mul_le_mul_of_nonneg_left hweightSq (sq_nonneg p)
  have hp : p ^ 2 ≤ p ^ 2 * C ^ 2 := by
    have hCsq : 1 ≤ C ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hCsq)]
  have hbase : 0 ≤ p ^ 2 * C ^ 2 + q ^ 2 := by positivity
  have hδterm : δ ^ 2 * p ^ 2 ≤ δ ^ 2 * (p ^ 2 * C ^ 2 + q ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg q]) (sq_nonneg δ)
  have hbound : p ^ 2 * C' ^ 2 + q' ^ 2 ≤
      ((1 + δ) * Real.sqrt (p ^ 2 * C ^ 2 + q ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hbase]
    nlinarith [mul_nonneg hδ hbase]
  exact (Real.sqrt_le_iff).2 ⟨by positivity, hbound⟩

theorem gluingCollarFinStripClamp_abs_im_le
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (z : ℂ) :
    |(gluingCollarFinStripClamp r ε z).im| ≤ |z.im| := by
  have ha : 0 ≤ ε * gluingCollarWarp r z.re :=
    mul_nonneg hε (gluingCollarWarp_pos hr z.re).le
  have hzero : gluingCollarClampReal (ε * gluingCollarWarp r z.re) 0 = 0 := by
    rw [gluingCollarClampReal, min_eq_right ha, max_eq_right (by linarith)]
  simpa only [gluingCollarFinStripClamp_im, hzero, sub_self, abs_zero,
    sub_zero, max_eq_right (abs_nonneg z.im)] using
      gluingCollarClampReal_abs_sub_le
        (ε * gluingCollarWarp r z.re) (ε * gluingCollarWarp r z.re) z.im 0

/-- Variable-width clipping sends every ordinary Lipschitz slab curve to an
ordinary Lipschitz strip curve. This constant is for admissibility; the
sharper weighted speed comparison is proved separately. -/
theorem gluingCollarFinStripClamp_lipschitzOnWith
    (r : ℝ) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) :
    LipschitzOnWith
      ⟨2 + ε * Real.cosh (|r| + R), by positivity⟩
      (gluingCollarFinStripClamp r ε) {z : ℂ | z.re ∈ Icc (-R) R} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hrad : |z.re - w.re| ≤ dist z w := by
    simpa only [Complex.sub_re, Complex.dist_eq] using Complex.abs_re_le_norm (z - w)
  have hang : |z.im - w.im| ≤ dist z w := by
    simpa only [Complex.sub_im, Complex.dist_eq] using Complex.abs_im_le_norm (z - w)
  have hwidth : |ε * gluingCollarWarp r z.re - ε * gluingCollarWarp r w.re| ≤
      ε * Real.cosh (|r| + R) * dist z w := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hε]
    exact (mul_le_mul_of_nonneg_left
      (gluingCollarWarp_abs_sub_le r hR hz hw) hε).trans
        (by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left hrad
            (mul_nonneg hε (Real.cosh_pos (|r| + R)).le))
  have hclip : |(gluingCollarFinStripClamp r ε z).im -
      (gluingCollarFinStripClamp r ε w).im| ≤
        (1 + ε * Real.cosh (|r| + R)) * dist z w := by
    have h := gluingCollarClampReal_abs_sub_le
      (ε * gluingCollarWarp r z.re) (ε * gluingCollarWarp r w.re) z.im w.im
    refine h.trans (max_le ?_ ?_)
    · nlinarith [dist_nonneg (x := z) (y := w)]
    · nlinarith [mul_nonneg (mul_nonneg hε (Real.cosh_pos (|r| + R)).le)
        (dist_nonneg (x := z) (y := w))]
  calc
    dist (gluingCollarFinStripClamp r ε z) (gluingCollarFinStripClamp r ε w) =
        ‖gluingCollarFinStripClamp r ε z - gluingCollarFinStripClamp r ε w‖ :=
      dist_eq_norm _ _
    _ ≤ |z.re - w.re| + |(gluingCollarFinStripClamp r ε z).im -
        (gluingCollarFinStripClamp r ε w).im| := by
      simpa only [Complex.sub_re, Complex.sub_im, gluingCollarFinStripClamp_re] using
        Complex.norm_le_abs_re_add_abs_im
          (gluingCollarFinStripClamp r ε z - gluingCollarFinStripClamp r ε w)
    _ ≤ dist z w + (1 + ε * Real.cosh (|r| + R)) * dist z w := add_le_add hrad hclip
    _ = _ := by change _ = (2 + ε * Real.cosh (|r| + R)) * dist z w; ring

/-- Variable-width clipping changes the actual Fermi speed by at most
`1+ε*cosh(|r|+R)` almost everywhere on every ordinary Lipschitz slab curve.
The estimate includes positive-measure visits to the radial seam and strip
boundaries; no finite-crossing or differentiable-branch assumption is used. -/
theorem gluingCollarFinStripClamp_speed_le_ae
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    {K : ℝ≥0} {β : ℝ → ℂ} (hβ : LipschitzOnWith K β (Icc 0 1))
    (hwindow : ∀ t ∈ Icc 0 1, (β t).re ∈ Icc (-R) R) :
    ∀ᵐ t ∂volume.restrict (Icc 0 1),
      gluingCollarFiniteStripSpeed lam (fun s => gluingCollarFinStripClamp r ε (β s)) t ≤
        (1 + ε * Real.cosh (|r| + R)) * gluingCollarFiniteStripSpeed lam β t := by
  let α : ℝ → ℂ := fun s => gluingCollarFinStripClamp r ε (β s)
  let a : ℝ → ℝ := fun s => ε * gluingCollarWarp r (β s).re
  have hrad : LipschitzOnWith K (fun s => (β s).re) (Icc 0 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hβ
  have him : LipschitzOnWith K (fun s => (β s).im) (Icc 0 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hβ
  have hα := (gluingCollarFinStripClamp_lipschitzOnWith r hR hε).comp hβ
    (fun t ht => hwindow t ht)
  have hαim := (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  have hwarp := (gluingCollarWarp_lipschitzOnWith r hR).comp hrad hwindow
  have ha : LipschitzOnWith
      (⟨ε, hε⟩ * (⟨Real.cosh (|r| + R), (Real.cosh_pos _).le⟩ * K)) a
      (Icc 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    change |ε * gluingCollarWarp r (β s).re - ε * gluingCollarWarp r (β t).re| ≤
      (ε * (Real.cosh (|r| + R) * (K : ℝ))) * dist s t
    rw [← mul_sub, abs_mul, abs_of_nonneg hε]
    have h := mul_le_mul_of_nonneg_left (hwarp.dist_le_mul s hs t ht) hε
    change ε * dist (gluingCollarWarp r (β s).re) (gluingCollarWarp r (β t).re) ≤
      ε * (Real.cosh (|r| + R) * (K : ℝ) * dist s t) at h
    simpa only [Real.dist_eq, mul_assoc] using h
  have hdiff {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Icc 0 1)) :
      ∀ᵐ t ∂volume.restrict (Icc 0 1), DifferentiableAt ℝ f t := by
    have hf' : LipschitzOnWith L f (uIcc 0 1) := by
      simpa only [uIcc_of_le zero_le_one] using hf
    filter_upwards [ae_restrict_of_ae hf'.absolutelyContinuousOnInterval.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact ht (by simpa only [uIcc_of_le zero_le_one] using hmem)
  have hconst : LipschitzOnWith 0 (fun _ : ℝ => ε) (Icc 0 1) :=
    (LipschitzWith.const ε).lipschitzOnWith
  have hprod := gluingCollarFinBand_product_deriv_ae
    (r := r) (c := 0) zero_le_one hR hrad hconst hwindow
  filter_upwards [hdiff ha, hdiff him, hdiff hαim, hprod,
    ae_restrict_mem measurableSet_Icc] with t hat hut hvt hproduct ht
  have hwidth : |deriv a t| ≤
      ε * Real.cosh (|r| + R) * |deriv (fun s => (β s).re) t| := by
    have heq : (fun s => gluingCollarWarp r (β s).re * (ε - 0)) = a := by
      funext s
      simp only [a, sub_zero, mul_comm]
    rw [heq] at hproduct
    simp only [deriv_const, mul_zero, add_zero, sub_zero] at hproduct
    rw [hproduct, abs_mul, abs_mul, abs_of_nonneg hε]
    have hslope := gluingCollarWarp_deriv_abs_le_all r hR (hwindow t ht)
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hslope (abs_nonneg (deriv (fun s => (β s).re) t))) hε]
  have htrans := gluingCollarClampReal_deriv_abs_le
    hat.hasDerivAt hut.hasDerivAt hvt.hasDerivAt
  have htrans' : |deriv (fun s => (α s).im) t| ≤
      max (ε * Real.cosh (|r| + R) * |deriv (fun s => (β s).re) t|)
        |deriv (fun s => (β s).im) t| :=
    htrans.trans (max_le_max hwidth le_rfl)
  have hweight : Real.cosh (lam * (α t).im) ≤ Real.cosh (lam * (β t).im) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (gluingCollarFinStripClamp_abs_im_le hr hε (β t))
      (abs_nonneg lam)
  have hspeed := gluingCollarFinStripClamp_pointwise_speed_le
    (Real.one_le_cosh (lam * (β t).im)) (Real.cosh_pos (lam * (α t).im)).le
    hweight (mul_nonneg hε (Real.cosh_pos _).le) htrans'
  have hreal : (fun s => (α s).re) = fun s => (β s).re := rfl
  change gluingCollarFiniteStripSpeed lam α t ≤
    (1 + ε * Real.cosh (|r| + R)) * gluingCollarFiniteStripSpeed lam β t
  simp only [gluingCollarFiniteStripSpeed, Complex.norm_def, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
    add_zero, one_mul, hreal]
  simpa only [zero_add, ← sq, mul_pow, mul_comm] using hspeed

/-- Integrating the corner-safe speed estimate bounds the length of every
clipped ambient Fermi curve by the same window-dependent factor. -/
theorem gluingCollarFinStripClamp_length_le
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    {K : ℝ≥0} {β : ℝ → ℂ} (hβ : LipschitzOnWith K β (Icc 0 1))
    (hwindow : ∀ t ∈ Icc 0 1, (β t).re ∈ Icc (-R) R) :
    (∫⁻ t in Icc 0 1, ENNReal.ofReal (gluingCollarFiniteStripSpeed lam
      (fun s => gluingCollarFinStripClamp r ε (β s)) t)) ≤
      ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
        ∫⁻ t in Icc 0 1, ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t) := by
  have hD : 0 ≤ 1 + ε * Real.cosh (|r| + R) := by positivity
  calc
    _ ≤ ∫⁻ t in Icc 0 1, ENNReal.ofReal
        ((1 + ε * Real.cosh (|r| + R)) * gluingCollarFiniteStripSpeed lam β t) := by
      apply lintegral_mono_ae
      filter_upwards [gluingCollarFinStripClamp_speed_le_ae hr hR hε hβ hwindow]
        with t ht
      exact ENNReal.ofReal_le_ofReal ht
    _ = ∫⁻ t in Icc 0 1, ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
        ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t) := by
      congr 1
      funext t
      exact ENNReal.ofReal_mul hD
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem gluingCollarFinStripClamp_mem_strip
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (z : ℂ) :
    |(gluingCollarFinStripClamp r ε z).im| ≤
      ε * gluingCollarWarp r (gluingCollarFinStripClamp r ε z).re := by
  have ha : 0 ≤ ε * gluingCollarWarp r z.re :=
    mul_nonneg hε (gluingCollarWarp_pos hr z.re).le
  change |max (-(ε * gluingCollarWarp r z.re))
    (min (ε * gluingCollarWarp r z.re) z.im)| ≤ ε * gluingCollarWarp r z.re
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem gluingCollarFinStripClamp_eq_self {r ε : ℝ} {z : ℂ}
    (hz : |z.im| ≤ ε * gluingCollarWarp r z.re) :
    gluingCollarFinStripClamp r ε z = z := by
  apply Complex.ext
  · rfl
  · change max (-(ε * gluingCollarWarp r z.re))
      (min (ε * gluingCollarWarp r z.re) z.im) = z.im
    rw [min_eq_right (abs_le.mp hz).2, max_eq_right (abs_le.mp hz).1]

/-- Two consecutive ambient Fermi copies share their whole reflected fin,
not merely the common strip boundary. -/
def gluingCollarFiniteFinRelation (r ε : ℝ) (p q : ℤ × ℂ) : Prop :=
  p.1 + 1 = q.1 ∧ p.2.re = q.2.re ∧ p.2.im = -q.2.im ∧
    ε * gluingCollarWarp r p.2.re ≤ p.2.im

abbrev gluingCollarFiniteFinTarget (r ε : ℝ) : Type :=
  Quotient (Relation.EqvGen.setoid (gluingCollarFiniteFinRelation r ε))

/-- The strip-boundary relation is a special case of the actual fin gluing. -/
theorem gluingCollarFiniteBandTargetSeam_finRelation
    {r ε : ℝ} {p q : ℤ × ℂ}
    (h : gluingCollarFiniteBandTargetSeam r ε p q) :
    gluingCollarFiniteFinRelation r ε p q := by
  obtain ⟨hindex, t, hp, hq⟩ := h
  refine ⟨hindex, ?_, ?_, ?_⟩ <;> simp [hp, hq]

/-- Inclusion of the genuine strip chain into the augmented fin quotient. -/
def gluingCollarFiniteFinTargetOfStrip (r ε : ℝ) :
    gluingCollarFiniteBandTarget r ε → gluingCollarFiniteFinTarget r ε :=
  Quotient.map id (by
    intro p q h
    exact Relation.EqvGen.mono
      (fun _ _ h => gluingCollarFiniteBandTargetSeam_finRelation h) p q h)

@[simp] theorem gluingCollarFiniteFinTargetOfStrip_mk
    (r ε : ℝ) (p : ℤ × ℂ) :
    gluingCollarFiniteFinTargetOfStrip r ε (Quotient.mk _ p) = Quotient.mk _ p := rfl

/-- The inverse band map after clipping the whole ambient Fermi copy to its
strip. Points in an exterior fin retract to that band's boundary. -/
noncomputable def gluingCollarFinClippedInverse (r c ε : ℝ) (z : ℂ) : ℂ :=
  gluingCollarFinBandInverse r c (gluingCollarFinStripClamp r ε z)

theorem gluingCollarFinClippedInverse_eq_inverse
    {r c ε : ℝ} {z : ℂ} (hz : |z.im| ≤ ε * gluingCollarWarp r z.re) :
    gluingCollarFinClippedInverse r c ε z = gluingCollarFinBandInverse r c z := by
  rw [gluingCollarFinClippedInverse, gluingCollarFinStripClamp_eq_self hz]

theorem gluingCollarFiniteFinRelation_inverse_eq
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (c : ℝ) {p q : ℤ × ℂ}
    (h : gluingCollarFiniteFinRelation r ε p q) :
    gluingCollarFinClippedInverse r (c + 2 * (p.1 : ℝ) * ε) ε p.2 =
      gluingCollarFinClippedInverse r (c + 2 * (q.1 : ℝ) * ε) ε q.2 := by
  obtain ⟨hindex, hre, him, hupper⟩ := h
  have hindex' : (q.1 : ℝ) = (p.1 : ℝ) + 1 := by
    exact_mod_cast hindex.symm
  have ha : 0 ≤ ε * gluingCollarWarp r p.2.re :=
    mul_nonneg hε (gluingCollarWarp_pos hr _).le
  have hq : q.2.im ≤ -(ε * gluingCollarWarp r q.2.re) := by
    rw [← hre]
    linarith
  have hpClamp := gluingCollarClampReal_eq_upper ha hupper
  have hqClamp := gluingCollarClampReal_eq_lower (by simpa only [hre] using ha) hq
  have hf := (gluingCollarWarp_pos hr p.2.re).ne'
  apply Complex.ext
  · simpa only [gluingCollarFinClippedInverse, gluingCollarFinBandInverse_re,
      gluingCollarFinStripClamp_re] using hre
  · simp only [gluingCollarFinClippedInverse, gluingCollarFinBandInverse_im,
      gluingCollarFinStripClamp_re, gluingCollarFinStripClamp_im]
    rw [hpClamp, hqClamp, ← hre, hindex']
    field_simp
    ring

/-- The clipped inverse descends through all actual fin identifications. -/
noncomputable def gluingCollarFiniteFinTargetInverse
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (c : ℝ) :
    gluingCollarFiniteFinTarget r ε → ℂ :=
  Quotient.lift
    (fun p : ℤ × ℂ => gluingCollarFinClippedInverse r
      (c + 2 * (p.1 : ℝ) * ε) ε p.2)
    (by
      intro p q h
      induction h with
      | rel p q h => exact gluingCollarFiniteFinRelation_inverse_eq hr hε c h
      | refl => rfl
      | symm p q _ ih => exact ih.symm
      | trans p q s _ _ ihpq ihqs => exact ihpq.trans ihqs)

@[simp] theorem gluingCollarFiniteFinTargetInverse_mk
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (c : ℝ) (p : ℤ × ℂ) :
    gluingCollarFiniteFinTargetInverse hr hε c (Quotient.mk _ p) =
      gluingCollarFinClippedInverse r (c + 2 * (p.1 : ℝ) * ε) ε p.2 := rfl

/-- The actual source map into the full augmented fin quotient. -/
noncomputable def gluingCollarFiniteFinTargetMap
    (r c ε : ℝ) (hε : 0 < ε) (z : ℂ) : gluingCollarFiniteFinTarget r ε :=
  gluingCollarFiniteFinTargetOfStrip r ε
    (gluingCollarFiniteBandTargetMap r c ε hε z)

/-- The augmented target retains every source point exactly. Exterior fin
points may retract to the strip boundary; no source point is collapsed. -/
@[simp] theorem gluingCollarFiniteFinTargetInverse_map
    {r c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (z : ℂ) :
    gluingCollarFiniteFinTargetInverse hr hε.le c
      (gluingCollarFiniteFinTargetMap r c ε hε z) = z := by
  change gluingCollarFinClippedInverse r
    (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε z.im : ℝ) * ε) ε
    (gluingCollarFinBandForward r
      (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε z.im : ℝ) * ε) z) = z
  rw [gluingCollarFinClippedInverse_eq_inverse
    (by simpa only [gluingCollarFinBandForward_re] using
      gluingCollarFiniteBandTargetMap_rep_mem_strip hr hε z),
    gluingCollarFinBandInverse_forward hr]

theorem gluingCollarFiniteFinTargetMap_injective
    {r c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    Function.Injective (gluingCollarFiniteFinTargetMap r c ε hε) := by
  intro z w h
  simpa only [gluingCollarFiniteFinTargetInverse_map hr hε] using
    congrArg (gluingCollarFiniteFinTargetInverse hr hε.le c) h

#print axioms gluingCollarFiniteBandTargetSeam_finRelation
#print axioms gluingCollarFiniteFinRelation_inverse_eq
#print axioms gluingCollarFiniteFinTargetInverse_map
#print axioms gluingCollarFiniteFinTargetMap_injective
#print axioms gluingCollarFinStripClamp_lipschitzOnWith
#print axioms gluingCollarFinStripClamp_abs_im_le
#print axioms gluingCollarClampReal_deriv_abs_le
#print axioms gluingCollarFinStripClamp_pointwise_speed_le
#print axioms gluingCollarFinStripClamp_speed_le_ae
#print axioms gluingCollarFinStripClamp_length_le

end SystolicGrowth
