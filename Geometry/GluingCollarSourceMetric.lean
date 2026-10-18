module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarAdmissibleMetric
public import Geometry.GluingCollarCurveReparametrization

@[expose] public section

/-!
# Real-coordinate warped distance on finite parameter intervals

For the strictly positive real-fiber warp, Alexander–Bishop's admissible
curves have two Lipschitz real coordinates on a finite closed interval
(Definition 4.1, arXiv:1509.00380v2). Their speeds here are actual limits
of endpoint-distance quotients, not renamed derivatives. Almost-everywhere
speed identification and affine normalization prove that this distance
equals the constructed native C¹ collar metric. No curvature theorem is
assumed or asserted.
-/

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace SystolicGrowth

/-- Totalized genuine metric speed of a real coordinate curve. Its value
at exceptional nondifferentiable times is irrelevant to the length integral. -/
noncomputable def realCoordinateMetricSpeed (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  limUnder (nhdsWithin t {t}ᶜ) (fun s => dist (f s) (f t) / dist s t)

/-- Interval Lipschitz continuity identifies genuine metric speed almost
everywhere, without a separately supplied differentiability hypothesis. -/
theorem realCoordinateMetricSpeed_eq_abs_deriv_ae {f : ℝ → ℝ} {K : ℝ≥0}
    {a b : ℝ} (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b)) :
    realCoordinateMetricSpeed f =ᵐ[volume.restrict (Icc a b)] fun t => |deriv f t| := by
  filter_upwards [lipschitzReal_metricSpeed_limit_ae hab hf] with t ht
  exact ht.limUnder_eq

/-- The same genuine speed is the distance-ratio limit along the actual
parameter interval; values outside it and null endpoints do not contribute. -/
theorem realCoordinateMetricSpeed_limitWithin_ae {f : ℝ → ℝ} {K : ℝ≥0}
    {a b : ℝ} (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b)) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun s => dist (f s) (f t) / dist s t)
        (nhdsWithin t (Icc a b \ {t})) (𝓝 (realCoordinateMetricSpeed f t)) := by
  filter_upwards [lipschitzReal_metricSpeed_limit_ae hab hf,
    realCoordinateMetricSpeed_eq_abs_deriv_ae hab hf] with t ht heq
  rw [heq]
  exact ht.mono_left (nhdsWithin_mono t (fun _ hs => hs.2))

/-- The weighted length of paired real coordinates using their genuine
metric speeds on the prescribed closed parameter interval. -/
noncomputable def gluingCollarSourceLength (r a b : ℝ) (u v : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
    (realCoordinateMetricSpeed u t ^ 2 +
      gluingCollarWarp r (u t) ^ 2 * realCoordinateMetricSpeed v t ^ 2))

/-- Genuine coordinate speeds give the ordinary derivative formula almost
everywhere, hence exactly the same weighted integral. -/
theorem gluingCollarSourceLength_eq_deriv_integral {a b : ℝ} (hab : a ≤ b)
    (r : ℝ) {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hu : LipschitzOnWith Ku u (Icc a b)) (hv : LipschitzOnWith Kv v (Icc a b)) :
    gluingCollarSourceLength r a b u v =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
        (deriv u t ^ 2 + gluingCollarWarp r (u t) ^ 2 * deriv v t ^ 2)) := by
  unfold gluingCollarSourceLength
  apply lintegral_congr_ae
  filter_upwards [realCoordinateMetricSpeed_eq_abs_deriv_ae hab hu,
    realCoordinateMetricSpeed_eq_abs_deriv_ae hab hv] with t hut hvt
  rw [hut, hvt, sq_abs, sq_abs]

/-- The real-coordinate source length is the actual complex collar
weighted integral, with genuine derivative components almost everywhere. -/
theorem gluingCollarSourceLength_eq_curve_integral {a b : ℝ} (hab : a ≤ b)
    (r : ℝ) {α : ℝ → ℂ} {K : ℝ≥0} (hα : LipschitzOnWith K α (Icc a b)) :
    gluingCollarSourceLength r a b (fun t => (α t).re) (fun t => (α t).im) =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
        (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  have hu : LipschitzOnWith K (fun t => (α t).re) (Icc a b) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
  have hv : LipschitzOnWith K (fun t => (α t).im) (Icc a b) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  rw [gluingCollarSourceLength_eq_deriv_integral hab r hu hv]
  apply lintegral_congr_ae
  filter_upwards [lipschitzCoordinate_deriv_components_ae hab hα] with t ht
  rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self, ht.1, ht.2]

/-- Every pair of admissible real coordinates has source length equal to
the genuine collar weighted length of its actual complex-coordinate curve. -/
theorem gluingCollarSourceLength_pair_eq_integral {a b : ℝ} (hab : a ≤ b)
    (r : ℝ) {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hu : LipschitzOnWith Ku u (Icc a b)) (hv : LipschitzOnWith Kv v (Icc a b)) :
    gluingCollarSourceLength r a b u v =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
        (gluingComplexCollarTangentForm r ((u t : ℂ) + (v t : ℂ) * Complex.I)
          (deriv (fun s => (u s : ℂ) + (v s : ℂ) * Complex.I) t)
          (deriv (fun s => (u s : ℂ) + (v s : ℂ) * Complex.I) t))) := by
  simpa using gluingCollarSourceLength_eq_curve_integral hab r
    (lipschitzCoordinate_pair hu hv)

/-- Native distance is bounded by the genuine source length of every
admissible pair, on every finite ordered interval, including a singleton. -/
theorem gluingCollarModelEDist_le_sourceLength {r a b : ℝ} (hr : 0 < r)
    (hab : a ≤ b) {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (hu : LipschitzOnWith Ku u (Icc a b)) (hv : LipschitzOnWith Kv v (Icc a b)) :
    gluingCollarModelEDist hr ((u a : ℂ) + (v a : ℂ) * Complex.I)
      ((u b : ℂ) + (v b : ℂ) * Complex.I) ≤ gluingCollarSourceLength r a b u v := by
  rw [gluingCollarSourceLength_pair_eq_integral hab r hu hv]
  exact gluingCollarModelEDist_le_interval_lipschitz_warp_length hr hab
    (lipschitzCoordinate_pair hu hv)

/-- Infimum over actual paired Lipschitz real coordinates on all finite
closed intervals. Endpoint, interval and regularity conditions only index
curves; they do not assume a distance comparison or curvature property. -/
noncomputable def gluingCollarSourceEDist (r : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (a : ℝ) (b : ℝ) (_hab : a ≤ b) (u : ℝ → ℝ) (v : ℝ → ℝ)
    (_h0 : (u a : ℂ) + (v a : ℂ) * Complex.I = z)
    (_h1 : (u b : ℂ) + (v b : ℂ) * Complex.I = w)
    (_hLip : ∃ Ku Kv : ℝ≥0,
      LipschitzOnWith Ku u (Icc a b) ∧ LipschitzOnWith Kv v (Icc a b)),
    gluingCollarSourceLength r a b u v

/-- Each actual admissible pair bounds the source infimum by its length. -/
theorem gluingCollarSourceEDist_le_length {r a b : ℝ} {z w : ℂ} (hab : a ≤ b)
    {u v : ℝ → ℝ} {Ku Kv : ℝ≥0}
    (h0 : (u a : ℂ) + (v a : ℂ) * Complex.I = z)
    (h1 : (u b : ℂ) + (v b : ℂ) * Complex.I = w)
    (hu : LipschitzOnWith Ku u (Icc a b)) (hv : LipschitzOnWith Kv v (Icc a b)) :
    gluingCollarSourceEDist r z w ≤ gluingCollarSourceLength r a b u v := by
  unfold gluingCollarSourceEDist
  exact iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hab
    (iInf_le_of_le u (iInf_le_of_le v (iInf_le_of_le h0 (iInf_le_of_le h1
      (iInf_le_of_le (show ∃ Ku Kv : ℝ≥0,
        LipschitzOnWith Ku u (Icc a b) ∧ LipschitzOnWith Kv v (Icc a b)
          from ⟨Ku, Kv, hu, hv⟩) le_rfl)))))))

/-- Every source admissible length bounds the actual native distance. -/
theorem gluingCollarModelEDist_le_sourceEDist {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarModelEDist hr z w ≤ gluingCollarSourceEDist r z w := by
  unfold gluingCollarSourceEDist
  refine le_iInf fun a => le_iInf fun b => le_iInf fun hab =>
    le_iInf fun u => le_iInf fun v => le_iInf fun h0 => le_iInf fun h1 =>
      le_iInf fun hLip => ?_
  obtain ⟨Ku, Kv, hu, hv⟩ := hLip
  simpa only [h0, h1] using gluingCollarModelEDist_le_sourceLength hr hab hu hv

/-- Unit-interval complex Lipschitz curves are actual source admissible
pairs, with the same genuine metric-speed length. -/
theorem gluingCollarSourceEDist_le_admissible (r : ℝ) (z w : ℂ) :
    gluingCollarSourceEDist r z w ≤ gluingCollarAdmissibleEDist r z w := by
  unfold gluingCollarAdmissibleEDist
  refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hLip => ?_
  obtain ⟨K, hK⟩ := hLip
  have hu : LipschitzOnWith K (fun t => (α t).re) (Icc 0 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hK
  have hv : LipschitzOnWith K (fun t => (α t).im) (Icc 0 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hK
  have hp0 : ((α 0).re : ℂ) + ((α 0).im : ℂ) * Complex.I = z :=
    (Complex.re_add_im (α 0)).trans h0
  have hp1 : ((α 1).re : ℂ) + ((α 1).im : ℂ) * Complex.I = w :=
    (Complex.re_add_im (α 1)).trans h1
  have hbound := gluingCollarSourceEDist_le_length (r := r) zero_le_one hp0 hp1 hu hv
  rw [gluingCollarSourceLength_eq_curve_integral zero_le_one r hK] at hbound
  exact hbound

/-- The real-fiber source metric is exactly the native C¹ collar metric.
The proof includes genuine speeds and all finite parameter intervals; it
does not infer curvature from equality of metrics. -/
theorem gluingCollarSourceEDist_eq_native {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    gluingCollarSourceEDist r z w = gluingCollarModelEDist hr z w := by
  apply le_antisymm
  · exact (gluingCollarSourceEDist_le_admissible r z w).trans
      (gluingCollarAdmissibleEDist_le_native hr z w)
  · exact gluingCollarModelEDist_le_sourceEDist hr z w

/-- Literal native metric consumer, excluding the ambient complex metric. -/
theorem gluingCollarModelMetricSpace_edist_eq_source {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    @edist ℂ (gluingCollarModelMetricSpace hr).toEDist z w =
      gluingCollarSourceEDist r z w :=
  (gluingCollarSourceEDist_eq_native hr z w).symm

#print axioms realCoordinateMetricSpeed_eq_abs_deriv_ae
#print axioms realCoordinateMetricSpeed_limitWithin_ae
#print axioms gluingCollarSourceLength_eq_curve_integral
#print axioms gluingCollarModelEDist_le_sourceLength
#print axioms gluingCollarSourceEDist_eq_native
#print axioms gluingCollarModelMetricSpace_edist_eq_source

end SystolicGrowth
