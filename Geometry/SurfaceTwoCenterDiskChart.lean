module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterSegmentNeighborhood
public import Geometry.SurfaceTwoCenterCutRectangle
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

/-!
# An actual embedded coordinate disk containing both punctures

Normalize the full center segment in its actual global coordinates. A thin
ellipse with a small axial margin fits in its uniformly embedded tube and
contains both centers in its interior. The complex coordinate order is
transverse real part and axial imaginary part.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane unitInterval

namespace SystolicGrowth

noncomputable section

/-- Complex coordinates normalized to a thin, oriented axial ellipse. -/
def orientedEllipseCoordinateHomeomorph (m a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ℂ ≃ₜ ℝ × ℝ where
  toFun z := (m + a * z.im, b * z.re)
  invFun p := ((p.2 / b : ℝ) : ℂ) + ((p.1 - m) / a : ℝ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp <;> field_simp
  right_inv p := by
    apply Prod.ext
    · simp
      field_simp
      ring
    · simp
      field_simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem orientedEllipseCoordinateHomeomorph_apply
    (m a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℂ) :
    orientedEllipseCoordinateHomeomorph m a b ha hb z =
      (m + a * z.im, b * z.re) := rfl

/-- Compactness supplies an actual thin ellipse and axial margin inside any
open neighborhood of the full coordinate axis segment. -/
theorem exists_ellipseCoefficients_in_open_axisNeighborhood (l r : ℝ)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (haxis : uIcc l r ×ˢ {(0 : ℝ)} ⊆ U) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ((l + r) / 2 + a * z.im, b * z.re) ∈ U) ∧
      |l - (l + r) / 2| < a ∧ |r - (l + r) / 2| < a := by
  let K : Set (ℝ × ℝ) := uIcc l r ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_uIcc.prod isCompact_singleton
  obtain ⟨η, hη, hthick⟩ := hK.exists_thickening_subset_open hU haxis
  let δ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let d := |r - l| / 2
  have hd : 0 ≤ d := div_nonneg (abs_nonneg _) (by norm_num)
  have hleft : |l - (l + r) / 2| = d := by
    change |l - (l + r) / 2| = |r - l| / 2
    rw [show l - (l + r) / 2 = -(r - l) / 2 by ring,
      abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hright : |r - (l + r) / 2| = d := by
    change |r - (l + r) / 2| = |r - l| / 2
    rw [show r - (l + r) / 2 = (r - l) / 2 by ring,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine ⟨d + δ, δ, by linarith, hδ, ?_, by rw [hleft]; linarith,
    by rw [hright]; linarith⟩
  intro z hz
  have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hz
  let x := (l + r) / 2 + d * z.im
  have hx : x ∈ uIcc l r := by
    change min l r ≤ x ∧ x ≤ max l r
    have hl : -(1 : ℝ) ≤ z.im := (abs_le.mp him).1
    have hr : z.im ≤ (1 : ℝ) := (abs_le.mp him).2
    have hlo : min l r = (l + r) / 2 - d := by
      dsimp [d]
      rw [min_def]
      split_ifs with h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        ring
      · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
        ring
    have hhi : max l r = (l + r) / 2 + d := by
      dsimp [d]
      rw [max_def]
      split_ifs with h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        ring
      · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
        ring
    rw [hlo, hhi]
    dsimp [x]
    constructor <;> nlinarith [mul_nonneg hd (by linarith : 0 ≤ z.im + 1),
      mul_nonneg hd (by linarith : 0 ≤ 1 - z.im)]
  have hdist : dist ((l + r) / 2 + (d + δ) * z.im, δ * z.re) (x, 0) ≤ δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    apply max_le
    · rw [show (l + r) / 2 + (d + δ) * z.im - x = δ * z.im by dsimp [x]; ring,
        abs_mul, abs_of_pos hδ]
      nlinarith
    · rw [sub_zero, abs_mul, abs_of_pos hδ]
      nlinarith
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(x, 0), ⟨hx, rfl⟩, hdist.trans_lt ?_⟩
  dsimp [δ]
  linarith

#print axioms exists_ellipseCoefficients_in_open_axisNeighborhood

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Both actual puncture centers lie in an actual embedded complex disk.
Its complete closed unit disk lies in the chart domain, and the chart is
the literal original quotient projection in normalized coordinates. This
strengthened producer also records the exact lifted point represented by
each puncture coordinate. -/
theorem exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment_liftedCenters
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hK : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : U → (X i).Carrier), Topology.IsOpenEmbedding f ∧
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (∀ t : I, P.componentCenterGeodPoint i t ∈
        f '' {z : U | ‖z.1‖ < 1}) ∧
      ∃ e : ℂ ≃ₜ ℍ, (∀ z : U, f z = (X i).orbitProjection (e z.1)) ∧
        e 0 = P.componentLiftedCenterGeodPoint i
          ⟨1 / 2, by constructor <;> norm_num⟩ ∧
        (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ z : ℂ,
          e z = P.componentTwoCenterGeodesicCoordinateHomeomorph i
            (((Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
                Real.log (P.componentTwoCenterGeodesicVerticalizer i •
                  (P.componentCenterClosestDeck i • (P.centers i).2)).im) / 2 + a * z.im),
              b * z.re)) ∧
        ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
          f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
          f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
          p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q ∧
          e p.1 = (P.centers i).1 ∧
          e q.1 = P.componentCenterClosestDeck i • (P.centers i).2 := by
  let H := P.componentTwoCenterGeodesicCoordinateHomeomorph i
  let l := Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im
  let r := Real.log (P.componentTwoCenterGeodesicVerticalizer i •
    (P.componentCenterClosestDeck i • (P.centers i).2)).im
  let m := (l + r) / 2
  obtain ⟨ε, hε, hsep⟩ := P.exists_componentLiftedCenterGeodTube_disjoint_translates i
  let Ω := P.componentLiftedCenterGeodTube i ε
  have hΩ : IsOpen Ω := isOpen_Iio.preimage (Metric.continuous_infDist_pt _)
  have hproj := P.componentLiftedCenterGeodTubeProjection_isOpenEmbedding i ε hsep
  have haxis : uIcc l r ×ˢ {(0 : ℝ)} ⊆ H ⁻¹' Ω := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
    subst y
    rw [← segment_eq_uIcc] at hx
    obtain ⟨a, b, ha, hb, hab, hxab⟩ := hx
    have hb1 : b ≤ 1 := by linarith
    let t : I := ⟨b, hb, hb1⟩
    have hcore : H (x, 0) = P.componentLiftedCenterGeodPoint i t := by
      have hx' : x = (1 - b) * l + b * r := by
        simp only [smul_eq_mul] at hxab
        have ha' : a = 1 - b := by linarith
        rw [ha'] at hxab
        exact hxab.symm
      rw [hx']
      exact P.componentTwoCenterGeodesicCoordinateHomeomorph_core i t
    change Metric.infDist (H (x, 0)) (P.componentLiftedCenterGeodSet i) < ε
    rw [hcore, Metric.infDist_zero_of_mem
      (show P.componentLiftedCenterGeodPoint i t ∈ P.componentLiftedCenterGeodSet i
        from ⟨t, rfl⟩)]
    exact hε
  obtain ⟨a, b, ha, hb, hclosed, hl, hr⟩ :=
    exists_ellipseCoefficients_in_open_axisNeighborhood l r
      (hΩ.preimage H.continuous) haxis
  let φ := orientedEllipseCoordinateHomeomorph m a b ha.ne' hb.ne'
  let e : ℂ ≃ₜ ℍ := φ.trans H
  let U : Set ℂ := e ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage e.continuous
  have hK : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    intro z hz
    exact hclosed z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  let j : U ≃ₜ Ω := e.subtype (fun _ => Iff.rfl)
  let f : U → (X i).Carrier := fun z => (X i).orbitProjection (e z.1)
  have hf : Topology.IsOpenEmbedding f := hproj.comp j.isOpenEmbedding
  let zL : ℂ := ((l - m) / a : ℝ) * Complex.I
  let zR : ℂ := ((r - m) / a : ℝ) * Complex.I
  have hnL : ‖zL‖ < 1 := by
    change ‖(((l - m) / a : ℝ) : ℂ) * Complex.I‖ < 1
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos ha]
    exact (div_lt_one ha).mpr hl
  have hnR : ‖zR‖ < 1 := by
    change ‖(((r - m) / a : ℝ) : ℂ) * Complex.I‖ < 1
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos ha]
    exact (div_lt_one ha).mpr hr
  have hzL : zL ∈ U := hK (by simpa only [Metric.mem_closedBall, dist_zero_right]
    using hnL.le)
  have hzR : zR ∈ U := hK (by simpa only [Metric.mem_closedBall, dist_zero_right]
    using hnR.le)
  have hL : e zL = (P.centers i).1 := by
    have hφ : φ zL = (l, 0) := by
      apply Prod.ext
      · change m + a * (zL.im) = l
        simp only [zL, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
        field_simp
        ring
      · simp [φ, orientedEllipseCoordinateHomeomorph, zL]
    change H (φ zL) = _
    rw [hφ]
    have hcoord : H.symm (P.centers i).1 = (l, 0) :=
      P.componentTwoCenterGeodesicCoordinateHomeomorph_left_center i
    rw [← hcoord]
    exact H.apply_symm_apply _
  have hR : e zR = P.componentCenterClosestDeck i • (P.centers i).2 := by
    have hφ : φ zR = (r, 0) := by
      apply Prod.ext
      · change m + a * (zR.im) = r
        simp only [zR, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
        field_simp
        ring
      · simp [φ, orientedEllipseCoordinateHomeomorph, zR]
    change H (φ zR) = _
    rw [hφ]
    have hcoord : H.symm (P.componentCenterClosestDeck i • (P.centers i).2) = (r, 0) :=
      P.componentTwoCenterGeodesicCoordinateHomeomorph_right_center i
    rw [← hcoord]
    exact H.apply_symm_apply _
  have hQL : f ⟨zL, hzL⟩ = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
    change (X i).orbitProjection (e zL) = _
    rw [hL]
    rfl
  have hQR : f ⟨zR, hzR⟩ = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
    change (X i).orbitProjection (e zR) = _
    rw [hR]
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨P.componentCenterClosestDeck i, rfl⟩)
  have hpq : (⟨zL, hzL⟩ : U) ≠ ⟨zR, hzR⟩ := by
    intro hpq
    have hcent := hQL.symm.trans ((congrArg f hpq).trans hQR)
    have hsep := P.carrier_centers_outer_add_inner_le_dist i
    rw [hcent, dist_self] at hsep
    have hRpos : 0 < gluingEmbeddedRadius C g :=
      lt_trans P.radius_pos P.radius_lt_embeddedRadius
    linarith [P.radius_pos]
  have hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈
      f '' {z : U | ‖z.1‖ < 1} := by
    intro t
    let zt : ℂ := (1 - (t : ℝ)) • zL + (t : ℝ) • zR
    have hzt : ‖zt‖ < 1 := by
      have hmem := (convex_ball (0 : ℂ) 1)
        (by simpa only [mem_ball, dist_zero_right] using hnL)
        (by simpa only [mem_ball, dist_zero_right] using hnR)
        (sub_nonneg.mpr t.2.2) t.2.1 (by ring : 1 - (t : ℝ) + (t : ℝ) = 1)
      simpa only [mem_ball, dist_zero_right] using hmem
    have hztU : zt ∈ U := hK (by
      simpa only [mem_closedBall, dist_zero_right] using hzt.le)
    have hφ : φ zt = ((1 - (t : ℝ)) * l + (t : ℝ) * r, 0) := by
      apply Prod.ext
      · change m + a * zt.im = (1 - (t : ℝ)) * l + (t : ℝ) * r
        simp [zt, zL, zR]
        field_simp
        ring
      · simp [φ, orientedEllipseCoordinateHomeomorph, zt, zL, zR]
    have hezt : e zt = P.componentLiftedCenterGeodPoint i t := by
      change H (φ zt) = _
      rw [hφ]
      exact P.componentTwoCenterGeodesicCoordinateHomeomorph_core i t
    refine ⟨⟨zt, hztU⟩, hzt, ?_⟩
    change (X i).orbitProjection (e zt) = P.componentCenterGeodPoint i t
    rw [hezt]
    rfl
  refine ⟨U, hU, hK, f, hf, ⟨⟨zL, hzL⟩, hnL, hQL⟩,
    ⟨⟨zR, hzR⟩, hnR, hQR⟩, hsegment, e, (fun _ => rfl), ?_,
    ⟨a, b, ha, hb, (fun _ => rfl)⟩,
    ⟨⟨zL, hzL⟩, ⟨zR, hzR⟩, hnL, hnR, hQL, hQR,
      by simp [zL], by simp [zR], hpq, hL, hR⟩⟩
  · change H (φ 0) = P.componentLiftedCenterGeodPoint i _
    have hφ0 : φ 0 = (m, 0) := by simp [φ, orientedEllipseCoordinateHomeomorph]
    rw [hφ0]
    have hcore := P.componentTwoCenterGeodesicCoordinateHomeomorph_core i
      (⟨1 / 2, by constructor <;> norm_num⟩ : I)
    change H (((1 - (1 / 2 : ℝ)) * l + (1 / 2 : ℝ) * r), 0) =
      P.componentLiftedCenterGeodPoint i _ at hcore
    rw [show (1 - (1 / 2 : ℝ)) * l + (1 / 2 : ℝ) * r = m by dsimp [m]; ring] at hcore
    exact hcore

/-- The original center-segment chart API, projected from the stronger
producer that retains its two exact lifted-center equations. -/
theorem exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hK : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : U → (X i).Carrier), Topology.IsOpenEmbedding f ∧
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (∀ t : I, P.componentCenterGeodPoint i t ∈
        f '' {z : U | ‖z.1‖ < 1}) ∧
      ∃ e : ℂ ≃ₜ ℍ, (∀ z : U, f z = (X i).orbitProjection (e z.1)) ∧
        e 0 = P.componentLiftedCenterGeodPoint i
          ⟨1 / 2, by constructor <;> norm_num⟩ ∧
        (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ z : ℂ,
          e z = P.componentTwoCenterGeodesicCoordinateHomeomorph i
            (((Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
                Real.log (P.componentTwoCenterGeodesicVerticalizer i •
                  (P.componentCenterClosestDeck i • (P.centers i).2)).im) / 2 + a * z.im),
              b * z.re)) ∧
        ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
          f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
          f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
          p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q := by
  obtain ⟨U, hU, hK, f, hf, hL, hR, hsegment, e, he, hm,
      hformula, p, q, hp, hq, hpmap, hqmap, hpre, hqre, hpq, _heL, _heR⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment_liftedCenters i
  exact ⟨U, hU, hK, f, hf, hL, hR, hsegment, e, he, hm, hformula,
    p, q, hp, hq, hpmap, hqmap, hpre, hqre, hpq⟩

/-- The original axis-puncture chart API, obtained from the actual chart
whose open disk contains the whole minimizing center segment. -/
theorem exists_componentTwoCenterEmbeddedDiskChart_axisPunctures
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hK : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : U → (X i).Carrier), Topology.IsOpenEmbedding f ∧
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      ∃ e : ℂ ≃ₜ ℍ, (∀ z : U, f z = (X i).orbitProjection (e z.1)) ∧
        e 0 = P.componentLiftedCenterGeodPoint i
          ⟨1 / 2, by constructor <;> norm_num⟩ ∧
        (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ z : ℂ,
          e z = P.componentTwoCenterGeodesicCoordinateHomeomorph i
            (((Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
                Real.log (P.componentTwoCenterGeodesicVerticalizer i •
                  (P.componentCenterClosestDeck i • (P.centers i).2)).im) / 2 + a * z.im),
              b * z.re)) ∧
        ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
          f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
          f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
          p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q := by
  obtain ⟨U, hU, hK, f, hf, hL, hR, _hsegment, he⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment i
  exact ⟨U, hU, hK, f, hf, hL, hR, he⟩

/-- The actual embedded disk retains its explicit oriented Fermi formula. -/
theorem exists_componentTwoCenterEmbeddedDiskChart_oriented
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hK : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : U → (X i).Carrier), Topology.IsOpenEmbedding f ∧
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      ∃ e : ℂ ≃ₜ ℍ, (∀ z : U, f z = (X i).orbitProjection (e z.1)) ∧
        e 0 = P.componentLiftedCenterGeodPoint i
          ⟨1 / 2, by constructor <;> norm_num⟩ ∧
        ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ z : ℂ,
          e z = P.componentTwoCenterGeodesicCoordinateHomeomorph i
            (((Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
                Real.log (P.componentTwoCenterGeodesicVerticalizer i •
                  (P.componentCenterClosestDeck i • (P.centers i).2)).im) / 2 + a * z.im),
              b * z.re) := by
  obtain ⟨U, hU, hK, f, hf, hL, hR, e, he, hm, hformula, _⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart_axisPunctures i
  exact ⟨U, hU, hK, f, hf, hL, hR, e, he, hm, hformula⟩

/-- The embedded disk chart without its additional oriented coordinate formula. -/
theorem exists_componentTwoCenterEmbeddedDiskChart
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hK : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : U → (X i).Carrier), Topology.IsOpenEmbedding f ∧
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
        f '' {z : U | ‖z.1‖ < 1} ∧
      ∃ e : ℂ ≃ₜ ℍ, (∀ z : U, f z = (X i).orbitProjection (e z.1)) ∧
        e 0 = P.componentLiftedCenterGeodPoint i
          ⟨1 / 2, by constructor <;> norm_num⟩ := by
  obtain ⟨U, hU, hK, f, hf, hL, hR, e, he, hm, _⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart_oriented i
  exact ⟨U, hU, hK, f, hf, hL, hR, e, he, hm⟩

#print axioms exists_componentTwoCenterEmbeddedDiskChart_oriented
#print axioms exists_componentTwoCenterEmbeddedDiskChart_axisPunctures
#print axioms exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment_liftedCenters
#print axioms exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment
#print axioms exists_componentTwoCenterEmbeddedDiskChart

end ExerciseGluingPreparation

end

end SystolicGrowth
