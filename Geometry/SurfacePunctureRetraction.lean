module

public import Geometry.GluingPolarCollar
public import Geometry.SurfaceOrbitBallLift

@[expose] public section

/-!
# Radial pushing at an actual surface puncture

On the original quotient with one actual disk center removed, interpolate
the hyperbolic radius to its maximum with the disk radius. The interpolation
is positive and lies in the existing embedded outer chart. Outside the inner
disk it fixes every point, including the entire boundary, at every time.
-/

open Set Metric Filter
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth

noncomputable section

def Internal.SurfacePunctureRetractionHelpers.puncturePolarAngle (o : ℍ) (z : {z : ℍ // z ≠ o}) : Circle :=
  ⟨hyperbolicRadialDirection o z.1, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [hyperbolicRadialDirection, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr (Vendored.RiemannDynamics.discChart_ne_zero z.2))]⟩

private theorem puncturePolarAngle_continuous (o : ℍ) :
    Continuous (Internal.SurfacePunctureRetractionHelpers.puncturePolarAngle o) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun z : {z : ℍ // z ≠ o} =>
      Vendored.RiemannDynamics.discChart o z.1) :=
    (continuous_discChart o).comp continuous_subtype_val
  exact hc.div (Complex.continuous_ofReal.comp hc.norm) (fun z =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (Vendored.RiemannDynamics.discChart_ne_zero z.2)))

private theorem puncturePolarPoint_self (o : ℍ) (z : {z : ℍ // z ≠ o}) :
    gluingPolarPoint o (Internal.SurfacePunctureRetractionHelpers.puncturePolarAngle o z) (dist o z.1) = z.1 := by
  apply discChart_injective o
  rw [discChart_gluingPolarPoint, ← norm_discChart_eq_tanh_half_dist]
  change (‖Vendored.RiemannDynamics.discChart o z.1‖ : ℂ) *
    (Vendored.RiemannDynamics.discChart o z.1 /
      (‖Vendored.RiemannDynamics.discChart o z.1‖ : ℂ)) = _
  have hne : (‖Vendored.RiemannDynamics.discChart o z.1‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (Vendored.RiemannDynamics.discChart_ne_zero z.2))
  field_simp

def Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate (r d : ℝ) (t : I) : ℝ :=
  (1 - (t : ℝ)) * d + (t : ℝ) * max r d

private theorem punctureRadialInterpolate_mem {r R d : ℝ}
    (hrR : r < R) (hd : d ∈ Ioo 0 R) (t : I) :
    Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r d t ∈ Ioo 0 R := by
  have hmax : max r d ∈ Ioo 0 R :=
    ⟨hd.1.trans_le (le_max_right _ _), max_lt hrR hd.2⟩
  simpa only [Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate, smul_eq_mul] using
    (convex_Ioo (0 : ℝ) R) hd hmax (sub_nonneg.mpr t.2.2) t.2.1 (by ring)

namespace ClosedHyperbolicSurface

/-- The original quotient with this actual disk center, and only the center, removed. -/
abbrev CenterPuncturedCarrier {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :=
  {q : X.Carrier // q ≠ (Quotient.mk'' o : X.Carrier)}

abbrev PuncturedOrbitBall {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) :=
  {q : X.Carrier // q ∈ X.orbitBall o R ∧ q ≠ (Quotient.mk'' o : X.Carrier)}

def punctureBallLift {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole)
    (q : X.PuncturedOrbitBall o R) : {z : ℍ // z ≠ o} :=
  ⟨((X.orbitBallHomeomorph o R hR).symm ⟨q.1, q.2.1⟩).1, by
    intro h
    apply q.2.2
    have he := congrArg Subtype.val
      ((X.orbitBallHomeomorph o R hR).apply_symm_apply ⟨q.1, q.2.1⟩)
    change (Quotient.mk'' _ : X.Carrier) = q.1 at he
    rw [h] at he
    exact he.symm⟩

private theorem punctureBallLift_continuous {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) :
    Continuous (X.punctureBallLift o R hR) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp ((X.orbitBallHomeomorph o R hR).symm.continuous.comp
    (continuous_subtype_val.subtype_mk (fun q => q.2.1)))

private theorem punctureBallLift_mem {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) (q : X.PuncturedOrbitBall o R) :
    (X.punctureBallLift o R hR q).1 ∈ ball o R :=
  ((X.orbitBallHomeomorph o R hR).symm ⟨q.1, q.2.1⟩).2

private theorem punctureBallLift_projection {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) (q : X.PuncturedOrbitBall o R) :
    (Quotient.mk'' (X.punctureBallLift o R hR q).1 : X.Carrier) = q.1 :=
  congrArg Subtype.val ((X.orbitBallHomeomorph o R hR).apply_symm_apply ⟨q.1, q.2.1⟩)

private theorem punctureBallLift_dist {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) (q : X.PuncturedOrbitBall o R) :
    dist (Quotient.mk'' o : X.Carrier) q.1 = dist o (X.punctureBallLift o R hR q).1 := by
  rw [← X.punctureBallLift_projection o R hR q]
  exact X.carrier_dist_mk_center_eq_of_mem_closedBall o R hR
    (ball_subset_closedBall (X.punctureBallLift_mem o R hR q))

def punctureBallRadialPoint {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (_hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.PuncturedOrbitBall o R) : ℍ :=
  gluingPolarPoint o (Internal.SurfacePunctureRetractionHelpers.puncturePolarAngle o (X.punctureBallLift o R hR p.2))
    (Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r (dist o (X.punctureBallLift o R hR p.2).1) p.1)

private theorem punctureBallRadialPoint_radius_mem {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.PuncturedOrbitBall o R) :
    Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r (dist o (X.punctureBallLift o R hR p.2).1) p.1 ∈ Ioo 0 R := by
  apply punctureRadialInterpolate_mem hrR
  exact ⟨dist_pos.mpr (X.punctureBallLift o R hR p.2).2.symm,
    by simpa only [mem_ball, dist_comm] using X.punctureBallLift_mem o R hR p.2⟩

private theorem punctureBallRadialPoint_mem {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.PuncturedOrbitBall o R) : X.punctureBallRadialPoint o r R hrR hR p ∈ ball o R := by
  have hradius := X.punctureBallRadialPoint_radius_mem o r R hrR hR p
  rw [mem_ball, dist_comm]
  exact (dist_gluingPolarPoint o _ hradius.1.le).trans_lt hradius.2

private theorem punctureBallRadialPoint_continuous {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole) :
    Continuous (X.punctureBallRadialPoint o r R hrR hR) := by
  have ha : Continuous (fun p : I × X.PuncturedOrbitBall o R =>
      Internal.SurfacePunctureRetractionHelpers.puncturePolarAngle o (X.punctureBallLift o R hR p.2)) :=
    (puncturePolarAngle_continuous o).comp
      ((X.punctureBallLift_continuous o R hR).comp continuous_snd)
  have ht : Continuous (fun p : I × X.PuncturedOrbitBall o R => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hl : Continuous (fun p : I × X.PuncturedOrbitBall o R =>
      (X.punctureBallLift o R hR p.2).1) :=
    ((X.punctureBallLift_continuous o R hR).comp continuous_snd).subtype_val
  have hd : Continuous (fun p : I × X.PuncturedOrbitBall o R =>
      dist o (X.punctureBallLift o R hR p.2).1) := continuous_const.dist hl
  have h1 : Continuous (fun _ : I × X.PuncturedOrbitBall o R => (1 : ℝ)) := continuous_const
  have hr : Continuous (fun _ : I × X.PuncturedOrbitBall o R => r) := continuous_const
  have hc : Continuous (fun p : I × X.PuncturedOrbitBall o R =>
      Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r (dist o (X.punctureBallLift o R hR p.2).1) p.1) :=
    ((h1.sub ht).mul hd).add (ht.mul (hr.max hd))
  have h := (gluingPolarPoint_continuous o).comp (ha.prodMk hc)
  exact h

/-- Radial push in the actual outer orbit chart, extended by the identity.
The outer chart need not be disjoint from other outer charts. -/
def puncturePushFn {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.CenterPuncturedCarrier o) : X.Carrier := by
  classical
  exact if hq : p.2.1 ∈ X.orbitBall o R then
    Quotient.mk'' (X.punctureBallRadialPoint o r R hrR hR
      (p.1, ⟨p.2.1, hq, p.2.2⟩)) else p.2.1

/-- The push fixes the complete complement of the actual inner open disk
at every time, including its boundary. -/
theorem puncturePushFn_fixed {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.CenterPuncturedCarrier o) (hp : p.2.1 ∉ X.orbitBall o r) :
    X.puncturePushFn o r R hrR hR p = p.2.1 := by
  classical
  unfold puncturePushFn
  split_ifs with hq
  · let q : X.PuncturedOrbitBall o R := ⟨p.2.1, hq, p.2.2⟩
    have hd : r ≤ dist o (X.punctureBallLift o R hR q).1 := by
      rw [← X.punctureBallLift_dist o R hR q]
      rw [← X.carrier_ball_eq_orbitBall] at hp
      rw [mem_ball, dist_comm] at hp
      exact le_of_not_gt hp
    have hinterp : Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r
        (dist o (X.punctureBallLift o R hR q).1) p.1 =
        dist o (X.punctureBallLift o R hR q).1 := by
      unfold Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate
      rw [max_eq_right hd]
      ring
    change (Quotient.mk'' (gluingPolarPoint o _ _) : X.Carrier) = p.2.1
    rw [hinterp, puncturePolarPoint_self]
    exact X.punctureBallLift_projection o R hR q
  · rfl

/-- The local radial formula and the exterior identity form an actual
continuous map on the original center-punctured quotient. -/
theorem puncturePushFn_continuous {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole) :
    Continuous (X.puncturePushFn o r R hrR hR) := by
  classical
  let s : Set (I × X.CenterPuncturedCarrier o) := {p | p.2.1 ∈ X.orbitBall o R}
  have hs : IsOpen s := (X.isOpen_orbitBall o R).preimage
    (continuous_subtype_val.comp continuous_snd)
  have hc : ContinuousOn (X.puncturePushFn o r R hrR hR) s := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hf : Continuous (fun p : s =>
        (p.1.1, (⟨p.1.2.1, p.2, p.1.2.2⟩ : X.PuncturedOrbitBall o R))) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        (((continuous_subtype_val.comp continuous_snd).comp
          continuous_subtype_val).subtype_mk _)
    have h : Continuous (fun p : s => (Quotient.mk''
        (X.punctureBallRadialPoint o r R hrR hR
          (p.1.1, ⟨p.1.2.1, p.2, p.1.2.2⟩)) : X.Carrier)) := continuous_quotient_mk'.comp
      ((X.punctureBallRadialPoint_continuous o r R hrR hR).comp hf)
    apply h.congr
    intro p
    have hp : p.1.2.1 ∈ X.orbitBall o R := p.2
    simp only [Set.domRestrict_apply, puncturePushFn, dite_eq_left hp]
  let v : Set (I × X.CenterPuncturedCarrier o) :=
    {p | r < dist (Quotient.mk'' o : X.Carrier) p.2.1}
  have hv : IsOpen v := isOpen_lt continuous_const
    (continuous_const.dist (continuous_subtype_val.comp continuous_snd))
  have hd : ContinuousOn (X.puncturePushFn o r R hrR hR) v := by
    apply (continuous_subtype_val.comp continuous_snd).continuousOn.congr
    intro p hp
    apply X.puncturePushFn_fixed o r R hrR hR
    rw [← X.carrier_ball_eq_orbitBall]
    rw [mem_ball, dist_comm]
    exact not_lt_of_ge (show r < dist (Quotient.mk'' o : X.Carrier) p.2.1 from hp).le
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ s
  · exact hc.continuousAt (hs.mem_nhds hp)
  · have hdist : R ≤ dist (Quotient.mk'' o : X.Carrier) p.2.1 := by
      change p.2.1 ∉ X.orbitBall o R at hp
      rw [← X.carrier_ball_eq_orbitBall] at hp
      rw [mem_ball, dist_comm] at hp
      exact le_of_not_gt hp
    exact hd.continuousAt (hv.mem_nhds (hrR.trans_le hdist))

@[simp]
theorem puncturePushFn_zero {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (q : X.CenterPuncturedCarrier o) : X.puncturePushFn o r R hrR hR (0, q) = q.1 := by
  classical
  unfold puncturePushFn
  split_ifs with hq
  · change (Quotient.mk'' (gluingPolarPoint o _
      (Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r _ 0)) : X.Carrier) = q.1
    simp only [Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate, show ((0 : I) : ℝ) = 0 from rfl, sub_zero, one_mul,
      zero_mul, add_zero, puncturePolarPoint_self]
    exact X.punctureBallLift_projection o R hR ⟨q.1, hq, q.2⟩
  · rfl

/-- A moved point remains in the original outer orbit chart; every other
point is unchanged. This is the support bound used for multiple punctures. -/
theorem puncturePushFn_mem_outer_or_eq {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.CenterPuncturedCarrier o) :
    X.puncturePushFn o r R hrR hR p ∈ X.orbitBall o R ∨
      X.puncturePushFn o r R hrR hR p = p.2.1 := by
  classical
  unfold puncturePushFn
  split_ifs with hq
  · exact Or.inl ⟨_, X.punctureBallRadialPoint_mem o r R hrR hR
      (p.1, ⟨p.2.1, hq, p.2.2⟩), rfl⟩
  · exact Or.inr rfl

/-- Honest positive-radius interpolation never crosses the actual removed center. -/
theorem puncturePushFn_ne_center {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.CenterPuncturedCarrier o) :
    X.puncturePushFn o r R hrR hR p ≠ (Quotient.mk'' o : X.Carrier) := by
  classical
  unfold puncturePushFn
  split_ifs with hq
  · let p' : I × X.PuncturedOrbitBall o R := (p.1, ⟨p.2.1, hq, p.2.2⟩)
    have hm := X.punctureBallRadialPoint_radius_mem o r R hrR hR p'
    have hd := X.carrier_dist_mk_center_eq_of_mem_closedBall o R hR
      (ball_subset_closedBall (X.punctureBallRadialPoint_mem o r R hrR hR p'))
    intro h
    have h' : (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)
        (X.punctureBallRadialPoint o r R hrR hR p') : X.Carrier) =
        Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) o := h
    rw [h', dist_self] at hd
    have hrad := dist_gluingPolarPoint o
      (Internal.SurfacePunctureRetractionHelpers.puncturePolarAngle o (X.punctureBallLift o R hR p'.2)) hm.1.le
    exact (ne_of_gt hm.1) (hd.trans hrad).symm
  · exact p.2.2

/-- At time one every point is outside the original inner open disk. -/
theorem puncturePushFn_one_not_mem_inner {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (q : X.CenterPuncturedCarrier o) :
    X.puncturePushFn o r R hrR hR (1, q) ∉ X.orbitBall o r := by
  classical
  unfold puncturePushFn
  split_ifs with hq
  · let p : I × X.PuncturedOrbitBall o R := (1, ⟨q.1, hq, q.2⟩)
    have hm := X.punctureBallRadialPoint_radius_mem o r R hrR hR p
    rw [← X.carrier_ball_eq_orbitBall, mem_ball, dist_comm,
      X.carrier_dist_mk_center_eq_of_mem_closedBall o R hR
        (ball_subset_closedBall (X.punctureBallRadialPoint_mem o r R hrR hR p))]
    change ¬ dist o (gluingPolarPoint o _ _) < r
    rw [dist_gluingPolarPoint o _ hm.1.le]
    rw [not_lt]
    change r ≤ Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate r (dist o
      (X.punctureBallLift o R hR ⟨q.1, hq, q.2⟩).1) 1
    simp only [Internal.SurfacePunctureRetractionHelpers.punctureRadialInterpolate, show ((1 : I) : ℝ) = 1 from rfl,
      sub_self, zero_mul, one_mul, zero_add]
    exact le_max_left _ _
  · intro h
    apply hq
    rw [← X.carrier_ball_eq_orbitBall] at h ⊢
    exact ball_subset_ball hrR.le h

/-- A radial push at one center preserves avoidance of any actual disk
disjoint from its outer chart. No outer-chart separation is required. -/
theorem puncturePushFn_preserves_not_mem {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r R : ℝ) (hrR : r < R) (hR : 2 * R < X.systole)
    (p : I × X.CenterPuncturedCarrier o) (s : Set X.Carrier)
    (hs : Disjoint (X.orbitBall o R) s) (hp : p.2.1 ∉ s) :
    X.puncturePushFn o r R hrR hR p ∉ s := by
  rcases X.puncturePushFn_mem_outer_or_eq o r R hrR hR p with h | h
  · exact Set.disjoint_left.mp hs h
  · rwa [h]

end ClosedHyperbolicSurface

end

end SystolicGrowth
