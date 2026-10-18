module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteMetricBlockDistanceBridge

@[expose] public section

/-!
# Genuine native retractions from the finite-block metric limit

Every limit point has a labelled radial-window representative in the
separated native path space. The original clipped inverse is independent of
that representative and constructs a radial-window retraction. Its metric
bound uses the actual native collar metric, not the Euclidean coordinate
metric. The source map and its exact left inverse are constructed internally.
-/

open Set

namespace SystolicGrowth

/-- The actual source-to-fin map retains a representative with exactly the
source radial coordinate, hence lies in the same fixed radial window. -/
theorem gluingCollarFiniteFinTargetMap_window
    {r R c ε : ℝ} (hε : 0 < ε) (x : ℂ) (hx : x.re ∈ Icc (-R) R) :
    ∃ i : ℤ, ∃ z : ℂ, z.re ∈ Icc (-R) R ∧
      Quotient.mk _ (i, z) = gluingCollarFiniteFinTargetMap r c ε hε x := by
  refine ⟨gluingCollarFiniteBandChoiceIndex c ε hε x.im,
    gluingCollarFinBandForward r
      (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε x.im : ℝ) * ε) x,
    ?_, rfl⟩
  simpa only [gluingCollarFinBandForward_re] using hx

structure Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.MetricBlockNativeWindowRep
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (p : gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam) where
  label : ℤ
  coord : ℂ
  memWindow : coord.re ∈ Icc (-R) R
  pathEq : gluingCollarFiniteFinPathMk r R lam ε (Quotient.mk _ (label, coord)) =
    gluingCollarFiniteMetricBlockLimitPathMap hR hlam p

theorem Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep_nonempty
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (p : gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam) :
    Nonempty (Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.MetricBlockNativeWindowRep hR hlam p) := by
  have hstage : ∃ n, ∃ a : gluingCollarFiniteMetricBlockSpace
      (r := r) (ε := ε) hR hlam n,
      Metric.toInductiveLimit
        (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) n a = p := by
    obtain ⟨⟨n, a⟩, rfl⟩ := Quotient.exists_rep p
    exact ⟨n, a, rfl⟩
  obtain ⟨n, a, rfl⟩ := hstage
  obtain ⟨i, hi, z, rfl⟩ := gluingCollarFiniteMetricBlockCopy_surjective hR hlam n a
  refine ⟨{
    label := i
    coord := gluingCollarFiniteFinPathCoordinates lam z.1
    memWindow := ?_
    pathEq := ?_ }⟩
  · simpa only [gluingCollarFiniteFinPathCoordinates_re,
      gluingFinFermiRadialWindow, Set.mem_setOf_eq] using z.2
  · rw [gluingCollarFiniteMetricBlockLimitPathMap_stage,
      gluingCollarFiniteMetricBlockPathMap_copy]
    rfl

noncomputable def Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (p : gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam) :
    Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.MetricBlockNativeWindowRep hR hlam p :=
  Classical.choice (Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep_nonempty hR hlam p)

private theorem nativeFinInverse_eq_of_pathMk_eq
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (c : ℝ) (p q : gluingCollarFiniteFinTarget r ε)
    (h : gluingCollarFiniteFinPathMk r R lam ε p =
      gluingCollarFiniteFinPathMk r R lam ε q) :
    gluingCollarFiniteFinTargetInverse hr hε c p =
      gluingCollarFiniteFinTargetInverse hr hε c q := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  have hscaled : ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε p q = 0 := by
    rw [← gluingCollarFiniteFinPathMk_edist, h, edist_self]
  have hpos : ENNReal.ofReal lam ≠ 0 := by positivity
  have hchain : gluingCollarFiniteFinChainEDist r R lam ε p q = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hpos
  have hbound := gluingCollarModelEDist_inverse_le_finChain (lam := lam) hr hR hε c p q
  have hzero : gluingCollarModelEDist hr
      (gluingCollarFiniteFinTargetInverse hr hε c p)
      (gluingCollarFiniteFinTargetInverse hr hε c q) = 0 := by
    exact le_antisymm (by simpa only [hchain, mul_zero] using hbound) bot_le
  exact edist_eq_zero.mp (by rw [gluingCollarModelMetricSpace_edist hr]; exact hzero)

/-- A genuine radial-window retraction from the actual block limit, using
the original clipped inverse on an internally constructed representative. -/
noncomputable def gluingCollarFiniteMetricBlockNativeRetraction
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (c : ℝ) :
    gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam →
      {z : ℂ // z.re ∈ Icc (-R) R} := fun p => by
  let P := Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep hR hlam p
  refine ⟨gluingCollarFiniteFinTargetInverse hr hε c (Quotient.mk _ (P.label, P.coord)), ?_⟩
  simpa only [gluingCollarFiniteFinTargetInverse_mk, gluingCollarFinClippedInverse,
    gluingCollarFinBandInverse_re, gluingCollarFinStripClamp_re] using P.memWindow

/-- On every actual radial-window representative, the constructed
retraction equals the original quotient inverse exactly. -/
theorem gluingCollarFiniteMetricBlockNativeRetraction_chainMap_mk
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (c : ℝ) (i : ℤ) (z : ℂ) (hz : z.re ∈ Icc (-R) R) :
    (gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε c
      (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (i, z)))).1 =
        gluingCollarFiniteFinTargetInverse hr hε c (Quotient.mk _ (i, z)) := by
  let P := Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep (r := r) (ε := ε) hR hlam
    (gluingCollarFiniteMetricBlockChainMap (r := r) (ε := ε) hR hlam (Quotient.mk _ (i, z)))
  change gluingCollarFiniteFinTargetInverse hr hε c (Quotient.mk _ (P.label, P.coord)) = _
  apply nativeFinInverse_eq_of_pathMk_eq hr hR hlam hε c
  calc
    _ = gluingCollarFiniteMetricBlockLimitPathMap hR hlam
        (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (i, z))) := P.pathEq
    _ = _ := by
      rw [gluingCollarFiniteMetricBlockChainMap_mk hR hlam i z hz,
        gluingCollarFiniteMetricBlockLimitPathMap_copy]
      exact gluingCollarFiniteFinPathSlabMap_fermi hlam i z hz

/-- Extended native distance is bounded by the limit distance with exactly
the proved clipping/inverse distortion and curvature scale. -/
theorem gluingCollarFiniteMetricBlockNativeRetraction_edist_le
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (c : ℝ)
    (p q : gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    edist (gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε c p)
      (gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε c q) ≤
        ENNReal.ofReal ((1 + ε * Real.cosh (|r| + R)) ^ 2 / lam) * edist p q := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  let P := Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep hR hlam p
  let Q := Internal.GluingCollarFiniteMetricBlockNativeRetractionHelpers.metricBlockNativeWindowRep hR hlam q
  let a : gluingCollarFiniteFinTarget r ε := Quotient.mk _ (P.label, P.coord)
  let b : gluingCollarFiniteFinTarget r ε := Quotient.mk _ (Q.label, Q.coord)
  let D := (1 + ε * Real.cosh (|r| + R)) ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  have hfactor : ENNReal.ofReal (D / lam) * ENNReal.ofReal lam = ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_mul (div_nonneg hD hlam.le), div_mul_cancel₀ _ hlam.ne']
  change edist (gluingCollarFiniteFinTargetInverse hr hε c a)
    (gluingCollarFiniteFinTargetInverse hr hε c b) ≤ ENNReal.ofReal (D / lam) * edist p q
  rw [gluingCollarModelMetricSpace_edist hr]
  calc
    _ ≤ ENNReal.ofReal D * gluingCollarFiniteFinChainEDist r R lam ε a b :=
      gluingCollarModelEDist_inverse_le_finChain hr hR hε c a b
    _ = ENNReal.ofReal (D / lam) *
        (ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε a b) := by
      rw [← mul_assoc, hfactor]
    _ = ENNReal.ofReal (D / lam) *
        edist (gluingCollarFiniteMetricBlockLimitPathMap hR hlam p)
          (gluingCollarFiniteMetricBlockLimitPathMap hR hlam q) := by
      rw [← gluingCollarFiniteFinPathMk_edist, P.pathEq, Q.pathEq]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [ENNReal.coe_one, one_mul] using
        gluingCollarFiniteMetricBlockLimitPathMap_lipschitz hR hlam p q) (by positivity)

/-- The real-distance retraction bound uses the original collar metric on
the same native radial-window carrier. -/
theorem gluingCollarFiniteMetricBlockNativeRetraction_dist_le
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (c : ℝ)
    (p q : gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    letI := (gluingCollarModelMetricSpace hr).toUniformSpace
    dist (gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε c p)
      (gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε c q) ≤
        ((1 + ε * Real.cosh (|r| + R)) ^ 2 / lam) * dist p q := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  have hfactor : 0 ≤ (1 + ε * Real.cosh (|r| + R)) ^ 2 / lam :=
    div_nonneg (sq_nonneg _) hlam.le
  have h := gluingCollarFiniteMetricBlockNativeRetraction_edist_le hr hR hlam hε c p q
  simp only [edist_dist] at h
  rw [← ENNReal.ofReal_mul hfactor] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hfactor dist_nonneg)).mp h

/-- The genuine native radial-window map into the actual block limit. -/
noncomputable def gluingCollarFiniteMetricBlockNativeForward
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (hε : 0 < ε) (c : ℝ) :
    {z : ℂ // z.re ∈ Icc (-R) R} →
      gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam := fun x =>
  gluingCollarFiniteMetricBlockChainMap hR hlam
    (gluingCollarFiniteFinTargetMap r c ε hε x.1)

/-- The constructed retraction is a genuine left inverse of the constructed
source map at every point of the original radial-window carrier. -/
theorem gluingCollarFiniteMetricBlockNativeRetraction_forward
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hε : 0 < ε) (c : ℝ) (x : {z : ℂ // z.re ∈ Icc (-R) R}) :
    gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε.le c
      (gluingCollarFiniteMetricBlockNativeForward hR hlam hε c x) = x := by
  obtain ⟨i, z, hz, hrep⟩ := gluingCollarFiniteFinTargetMap_window (r := r) (c := c) hε x.1 x.2
  apply Subtype.ext
  change (gluingCollarFiniteMetricBlockNativeRetraction hr hR hlam hε.le c
    (gluingCollarFiniteMetricBlockChainMap hR hlam
      (gluingCollarFiniteFinTargetMap r c ε hε x.1))).1 = x.1
  rw [← hrep, gluingCollarFiniteMetricBlockNativeRetraction_chainMap_mk hr hR hlam hε.le c i z hz,
    hrep, gluingCollarFiniteFinTargetInverse_map hr hε]

#print axioms gluingCollarFiniteFinTargetMap_window
#print axioms gluingCollarFiniteMetricBlockNativeRetraction
#print axioms gluingCollarFiniteMetricBlockNativeRetraction_chainMap_mk
#print axioms gluingCollarFiniteMetricBlockNativeRetraction_dist_le
#print axioms gluingCollarFiniteMetricBlockNativeRetraction_forward

end SystolicGrowth
