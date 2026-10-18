module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingComponentTangentTransport

@[expose] public section

/-!
# True component deck equivariance of native interior unit vectors

All local transition witnesses lie in the original component's actual deck
subgroup. They are not arbitrary elements of `SL₂(ℝ)`.
-/

open Set Metric UpperHalfPlane Filter Bundle
open scoped UpperHalfPlane MatrixGroups Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Actual interior ball charts in the same component differ locally by an
element of that original component's genuine deck subgroup. -/
theorem gluedInteriorBallChart_transition_eventually_eq_componentDeck
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ, (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (hf : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))
    (z' : ℍ) (ρ' : ℝ) (hρ' : 0 < ρ')
    (hq' : ∀ w : ball z' ρ', (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (hf' : Topology.IsOpenEmbedding (fun w : ball z' ρ' =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq' w⟩)))
    (x : ℂ) (hx : x ∈ ((P.gluedInteriorComplexChart i z ρ hρ hq hf).symm.trans
      (P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf')).source) :
    0 < x.im ∧ ∃ γ : (X i).deckGroup,
      ((P.gluedInteriorComplexChart i z ρ hρ hq hf).symm.trans
        (P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf') : ℂ → ℂ) =ᶠ[𝓝 x]
          gluingDeckComplex γ.val := by
  have htarget := hx.1
  change x ∈ (P.gluedInteriorComplexChart i z ρ hρ hq hf).target at htarget
  rw [P.gluedInteriorComplexChart_target] at htarget
  obtain ⟨u, hu⟩ := htarget
  have hxim : 0 < x.im := by rw [← hu]; exact u.val.im_pos
  have hF : ∀ᶠ y in 𝓝 x, ∃ hy :
      (Quotient.mk'' (UpperHalfPlane.ofComplex y) : (X i).Carrier) ∈ P.componentInteriorSet i,
      (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm y =
        P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' (UpperHalfPlane.ofComplex y), hy⟩) := by
    filter_upwards [(P.gluedInteriorComplexChart i z ρ hρ hq hf).open_target.mem_nhds hx.1]
      with y hy
    rw [P.gluedInteriorComplexChart_target] at hy
    obtain ⟨w, rfl⟩ := hy
    simpa only [UpperHalfPlane.ofComplex_apply] using
      (show ∃ hw : (Quotient.mk'' w.val : (X i).Carrier) ∈ P.componentInteriorSet i,
        (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm (w.val : ℂ) =
          P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.val, hw⟩) from
        ⟨hq w, P.gluedInteriorComplexChart_symm_apply i z ρ hρ hq hf w⟩)
  obtain ⟨γ, hγ⟩ := P.gluedInteriorComplexChart_eventually_eq_deck i z' ρ' hρ' hq' hf'
    UpperHalfPlane.ofComplex (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm x
    (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) hxim).continuousAt hx.2 hF
  refine ⟨hxim, γ, ?_⟩
  filter_upwards [hγ, UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hxim] with y hy hy'
  exact hy.trans ((gluingDeckComplex_coe γ.val _).symm.trans
    (congrArg (gluingDeckComplex γ.val) hy'))

/-- The actual component deck differential sends the literal physical
hyperbolic unit vector to its true transformed height times tangent phase. -/
theorem componentDeck_fderiv_physical_unit
    (_P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (A : (X i).deckGroup) (z : ℍ) (u : ℂ) :
    fderiv ℝ (gluingDeckComplex A.val) (z : ℂ) ((z.im : ℂ) * u) =
      ((A • z : ℍ).im : ℂ) * ((halfPlaneSpinCircle A.val z : ℂ) ^ 2 * u) := by
  rw [(gluingDeckComplex_hasFDerivAt_equiv A.val z.im_pos).fderiv]
  change gluingDeckComplexDeriv A.val (z : ℂ) * ((z.im : ℂ) * u) =
    ((A.val • z : ℍ).im : ℂ) * ((halfPlaneSpinCircle A.val z : ℂ) ^ 2 * u)
  rw [gluingDeckComplex_im_smul, halfPlaneSpinCircle_coe]
  unfold gluingDeckComplexDeriv halfPlaneSpinMultiplier halfPlaneSpinDenominator
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  have hD := gluingDeckComplex_denom_ne_zero A.val z.im_pos
  have hN : (‖(A.val 1 0 : ℂ) * (z : ℂ) + (A.val 1 1 : ℂ)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hD)
  field_simp [hD, hN]

private theorem nativeInterior_coord_physical
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (u : Circle) :
    P.nativeUnitTangentCoord e (Or.inl he) b (P.nativeUnitTangentParam e (Or.inl he) b hb u) =
      ((e b).im : ℂ) * (u : ℂ) := by
  have him := P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hb)
  rw [P.nativeUnitTangentCoord_param, P.gluingChartTangentForm_interior _ he,
    gluingComplexHalfPlaneTangentForm_apply, Complex.mul_conj', Circle.norm_coe]
  simp only [Complex.ofReal_one, one_pow, Complex.one_re]
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq_eq_abs,
    abs_of_pos him, one_div, inv_inv]
  rfl

section Interior

variable (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
  (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ) (h4 : 4 * ρ < (X i).systole)
  (hq : ∀ w : ball z ρ, (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
  (hf : Topology.IsOpenEmbedding (fun w : ball z ρ =>
    P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))
  (z' : ℍ) (ρ' : ℝ) (hρ' : 0 < ρ') (h4' : 4 * ρ' < (X i).systole)
  (hq' : ∀ w : ball z' ρ', (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
  (hf' : Topology.IsOpenEmbedding (fun w : ball z' ρ' =>
    P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq' w⟩)))

/-- The actual native unit-fiber transition between two component ball charts
is the physical tangent action of an element of the original deck subgroup. -/
theorem nativeInteriorBallUnitTangentParam_overlap
    (b : P.GluedCarrier)
    (hb : b ∈ (P.gluedInteriorComplexChart i z ρ hρ hq hf).source)
    (hb' : b ∈ (P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf').source) (u : Circle) :
    ∃ A : (X i).deckGroup,
      P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf' b =
        ((A • UpperHalfPlane.ofComplex (P.gluedInteriorComplexChart i z ρ hρ hq hf b) : ℍ) : ℂ) ∧
      P.nativeUnitTangentParam (P.gluedInteriorComplexChart i z ρ hρ hq hf)
        (Or.inl ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩) b hb u =
      P.nativeUnitTangentParam (P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf')
        (Or.inl ⟨i, z', ρ', hρ', h4', hq', hf', rfl⟩) b hb'
        (halfPlaneSpinCircle A.val
          (UpperHalfPlane.ofComplex (P.gluedInteriorComplexChart i z ρ hρ hq hf b)) ^ 2 * u) := by
  let e := P.gluedInteriorComplexChart i z ρ hρ hq hf
  let e' := P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf'
  have he : P.IsGluedInteriorComplexChart e := ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩
  have he' : P.IsGluedInteriorComplexChart e' := ⟨i, z', ρ', hρ', h4', hq', hf', rfl⟩
  have hx : e b ∈ (e.symm.trans e').source := by
    refine ⟨e.map_source hb, ?_⟩
    change e.symm (e b) ∈ e'.source
    rw [e.left_inv hb]
    exact hb'
  obtain ⟨him, A, hA⟩ := P.gluedInteriorBallChart_transition_eventually_eq_componentDeck
    i z ρ hρ hq hf z' ρ' hρ' hq' hf' (e b) hx
  let w := UpperHalfPlane.ofComplex (e b)
  have hw : (w : ℂ) = e b :=
    congrArg (fun q : ℍ => (q : ℂ)) (UpperHalfPlane.ofComplex_apply_of_im_pos him)
  have hAw : ((A • w : ℍ) : ℂ) = e' b := by
    change ((A.val • w : ℍ) : ℂ) = e' b
    rw [← gluingDeckComplex_coe A.val, hw]
    have hv : (e.symm.trans e') (e b) = e' b := by
      change e' (e.symm (e b)) = e' b
      rw [e.left_inv hb]
    exact hA.self_of_nhds.symm.trans hv
  refine ⟨A, hAw.symm, ?_⟩
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e', Or.inl he'⟩ : atlas ℂ P.GluedCarrier)
  apply Subtype.ext
  apply (t.continuousLinearEquivAt ℝ b (by exact hb')).injective
  rw [t.coe_continuousLinearEquivAt_eq (by exact hb')]
  change P.nativeUnitTangentCoord e' (Or.inl he') b
    (P.nativeUnitTangentParam e (Or.inl he) b hb u) =
    P.nativeUnitTangentCoord e' (Or.inl he') b
      (P.nativeUnitTangentParam e' (Or.inl he') b hb' (halfPlaneSpinCircle A.val w ^ 2 * u))
  rw [P.nativeUnitTangentCoord_change e e' (Or.inl he) (Or.inl he') b hb hb',
    nativeInterior_coord_physical P e he b hb,
    nativeInterior_coord_physical P e' he' b hb', hA.fderiv_eq, ← hw,
    Circle.coe_mul, Circle.coe_pow]
  have hheight : (A • w : ℍ).im = (e' b).im := congrArg Complex.im hAw
  change fderiv ℝ (gluingDeckComplex A.val) (w : ℂ) ((w.im : ℂ) * (u : ℂ)) = _
  rw [← hheight]
  exact P.componentDeck_fderiv_physical_unit i A w u

/-- Two genuine preferred ball sheets of the same actual component frame
orbit give the same true native unit tangent, independently of chart choice. -/
theorem interiorBallNativeUnitHomeomorph_eq_of_frame_orbit
    (w : ball z ρ) (u : Circle) (w' : ball z' ρ') (u' : Circle)
    (horbit : (Quotient.mk _ (⟨w.val, u⟩ : HalfPlaneTangentFrame) : (X i).TangentFrameCarrier) =
      Quotient.mk _ (⟨w'.val, u'⟩ : HalfPlaneTangentFrame)) :
    (P.interiorBallNativeUnitHomeomorph i z ρ hρ h4 hq hf (w, u)).val =
      (P.interiorBallNativeUnitHomeomorph i z' ρ' hρ' h4' hq' hf' (w', u')).val := by
  let e := P.gluedInteriorComplexChart i z ρ hρ hq hf
  let e' := P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf'
  let b := P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.val, hq w⟩)
  let b' := P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w'.val, hq' w'⟩)
  have hquot : (Quotient.mk'' w.val : (X i).Carrier) = Quotient.mk'' w'.val :=
    congrArg (X i).tangentFrameBase horbit
  have hbase : b = b' := congrArg
    (fun q : P.componentInteriorSet i => P.gluedMk (P.componentInteriorPoint i q))
      (Subtype.ext hquot)
  have hb : b ∈ e.source := (P.interiorBallSourceHomeomorph i z ρ hρ hq hf w).property
  have hbr : b' ∈ e'.source := (P.interiorBallSourceHomeomorph i z' ρ' hρ' hq' hf' w').property
  have hb' : b ∈ e'.source := hbase.symm ▸ hbr
  have heval : e b = (w.val : ℂ) := P.gluedInteriorComplexChart_apply i z ρ hρ hq hf w
  have heval' : e' b = (w'.val : ℂ) :=
    hbase.symm ▸ P.gluedInteriorComplexChart_apply i z' ρ' hρ' hq' hf' w'
  obtain ⟨A, hApoint, hAunit⟩ := P.nativeInteriorBallUnitTangentParam_overlap
    i z ρ hρ h4 hq hf z' ρ' hρ' h4' hq' hf' b hb hb' u
  have hpoint : A • w.val = w'.val := by
    apply UpperHalfPlane.coe_injective
    change e' b = ((A • UpperHalfPlane.ofComplex (e b) : ℍ) : ℂ) at hApoint
    simpa only [heval, heval', UpperHalfPlane.ofComplex_apply] using hApoint.symm
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact horbit.symm))
  have hBpoint : B • w.val = w'.val := congrArg HalfPlaneTangentFrame.point hB
  have hfix : (B⁻¹ * A) • w.val = w.val := by
    rw [mul_smul, hpoint, ← hBpoint, inv_smul_smul]
  have hAB : A = B := (inv_mul_eq_one.mp ((X i).free (B⁻¹ * A) w.val hfix)).symm
  subst B
  have hphase : halfPlaneSpinCircle A.val w.val ^ 2 * u = u' :=
    congrArg HalfPlaneTangentFrame.phase hB
  have hphase' : halfPlaneSpinCircle A.val (UpperHalfPlane.ofComplex (e b)) ^ 2 * u = u' := by
    simpa only [heval, UpperHalfPlane.ofComplex_apply] using hphase
  rw [hphase'] at hAunit
  have hsame (b₁ b₂ : P.GluedCarrier) (h : b₁ = b₂) (h₁ : b₁ ∈ e'.source)
      (h₂ : b₂ ∈ e'.source) :
      TotalSpace.mk' ℂ b₁ (P.nativeUnitTangentParam e'
        (Or.inl ⟨i, z', ρ', hρ', h4', hq', hf', rfl⟩) b₁ h₁ u').val =
      TotalSpace.mk' ℂ b₂ (P.nativeUnitTangentParam e'
        (Or.inl ⟨i, z', ρ', hρ', h4', hq', hf', rfl⟩) b₂ h₂ u').val := by
    subst b₂
    rfl
  apply Subtype.ext
  exact (congrArg (fun v : P.NativeUnitTangentFiber b => TotalSpace.mk' ℂ b v.val) hAunit).trans
    (hsame b b' hbase hb' hbr)

end Interior

section InteriorTransport

variable (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
  (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ) (h4 : 4 * ρ < (X i).systole)
  (hq : ∀ w : ball z ρ, (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
  (hf : Topology.IsOpenEmbedding (fun w : ball z ρ =>
    P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))

/-- Native transport preserves the original component base exactly. -/
theorem interiorTangentNativeUnitHomeomorph_proj
    (q : (X i).TangentBallCarrier z ρ) :
    ∃ hqbase : (X i).tangentFrameBase q.val ∈ P.componentInteriorSet i,
      (P.interiorTangentNativeUnitHomeomorph i z ρ hρ h4 hq hf q).val.val.proj =
        P.gluedMk (P.componentInteriorPoint i ⟨(X i).tangentFrameBase q.val, hqbase⟩) := by
  let T := (X i).tangentBallHomeomorph z (show 2 * ρ < (X i).systole by linarith)
  let p := T.symm q
  have heq : T p = q := T.apply_symm_apply q
  have hbase : (Quotient.mk'' p.1.val : (X i).Carrier) = (X i).tangentFrameBase q.val :=
    congrArg (fun t : (X i).TangentBallCarrier z ρ => (X i).tangentFrameBase t.val) heq
  refine ⟨hbase ▸ hq p.1, ?_⟩
  change P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' p.1.val, hq p.1⟩) = _
  exact congrArg (fun b : P.componentInteriorSet i => P.gluedMk (P.componentInteriorPoint i b))
    (Subtype.ext hbase)

/-- The local homeomorphisms agree on actual tangent-orbit intersections. -/
theorem interiorTangentNativeUnitHomeomorph_overlap
    (z' : ℍ) (ρ' : ℝ) (hρ' : 0 < ρ') (h4' : 4 * ρ' < (X i).systole)
    (hq' : ∀ w : ball z' ρ', (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (hf' : Topology.IsOpenEmbedding (fun w : ball z' ρ' =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq' w⟩)))
    (q : (X i).TangentBallCarrier z ρ) (q' : (X i).TangentBallCarrier z' ρ')
    (heq : q.val = q'.val) :
    (P.interiorTangentNativeUnitHomeomorph i z ρ hρ h4 hq hf q).val =
      (P.interiorTangentNativeUnitHomeomorph i z' ρ' hρ' h4' hq' hf' q').val := by
  let T := (X i).tangentBallHomeomorph z (show 2 * ρ < (X i).systole by linarith)
  let T' := (X i).tangentBallHomeomorph z' (show 2 * ρ' < (X i).systole by linarith)
  let p := T.symm q
  let p' := T'.symm q'
  have hp : (Quotient.mk _ (⟨p.1.val, p.2⟩ : HalfPlaneTangentFrame) :
      (X i).TangentFrameCarrier) = q.val := congrArg Subtype.val (T.apply_symm_apply q)
  have hp' : (Quotient.mk _ (⟨p'.1.val, p'.2⟩ : HalfPlaneTangentFrame) :
      (X i).TangentFrameCarrier) = q'.val := congrArg Subtype.val (T'.apply_symm_apply q')
  exact P.interiorBallNativeUnitHomeomorph_eq_of_frame_orbit
    i z ρ hρ h4 hq hf z' ρ' hρ' h4' hq' hf' p.1 p.2 p'.1 p'.2
      (hp.trans (heq.trans hp'.symm))

end InteriorTransport

noncomputable section

/-- Actual component frame orbits lying over its retained open interior. -/
abbrev ComponentInteriorTangentCarrier
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  {q : (X i).TangentFrameCarrier // (X i).tangentFrameBase q ∈ P.componentInteriorSet i}

/-- Actual native unit vectors over the image of that original interior. -/
abbrev NativeComponentInteriorUnitTangentOver
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  {v : P.NativeUnitTangentCarrier // v.val.proj ∈
    Set.range (fun q : P.componentInteriorSet i => P.gluedMk (P.componentInteriorPoint i q))}

/-- Verified local geometric data used to descend the actual component
frame carrier; the existence theorem supplies every field. -/
structure ComponentInteriorBallChart
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) where
  center : ℍ
  radius : ℝ
  radius_pos : 0 < radius
  radius_small : 4 * radius < (X i).systole
  interior : ∀ w : ball center radius,
    (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i
  open_embedding : Topology.IsOpenEmbedding (fun w : ball center radius =>
    P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, interior w⟩))

variable (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)

theorem exists_componentInteriorBallChart (q : P.componentInteriorSet i) :
    ∃ D : P.ComponentInteriorBallChart i,
      (Quotient.mk'' D.center : (X i).Carrier) = q.val := by
  obtain ⟨z, ρ, hρ, h4, hz, hq, hf⟩ := P.exists_gluedComponentInterior_ball_chart i q
  exact ⟨⟨z, ρ, hρ, h4, hq, hf⟩, hz⟩

def componentInteriorBallChartAt (q : P.componentInteriorSet i) :
    P.ComponentInteriorBallChart i :=
  Classical.choose (P.exists_componentInteriorBallChart i q)

theorem componentInteriorBallChartAt_base (q : P.componentInteriorSet i) :
    (Quotient.mk'' (P.componentInteriorBallChartAt i q).center : (X i).Carrier) = q.val :=
  Classical.choose_spec (P.exists_componentInteriorBallChart i q)

namespace ComponentInteriorBallChart

variable {P i} (D : P.ComponentInteriorBallChart i)

def nativeChart : OpenPartialHomeomorph P.GluedCarrier ℂ :=
  P.gluedInteriorComplexChart i D.center D.radius D.radius_pos D.interior D.open_embedding

def tangentHomeomorph :
    (X i).TangentBallCarrier D.center D.radius ≃ₜ P.NativeUnitTangentOver D.nativeChart :=
  P.interiorTangentNativeUnitHomeomorph i D.center D.radius D.radius_pos D.radius_small
    D.interior D.open_embedding

theorem tangent_interior (q : (X i).TangentBallCarrier D.center D.radius) :
    (X i).tangentFrameBase q.val ∈ P.componentInteriorSet i := by
  obtain ⟨w, hw, heq⟩ := q.property
  exact heq ▸ D.interior ⟨w, hw⟩

def tangentInclusion (q : (X i).TangentBallCarrier D.center D.radius) :
    P.ComponentInteriorTangentCarrier i := ⟨q.val, D.tangent_interior q⟩

theorem native_source_interior (b : P.GluedCarrier) (hb : b ∈ D.nativeChart.source) :
    b ∈ Set.range (fun q : P.componentInteriorSet i => P.gluedMk (P.componentInteriorPoint i q)) := by
  change b ∈ (P.gluedInteriorComplexChart i D.center D.radius D.radius_pos
    D.interior D.open_embedding).source at hb
  rw [P.gluedInteriorComplexChart_source] at hb
  obtain ⟨w, hw⟩ := hb
  exact ⟨⟨Quotient.mk'' w.val, D.interior w⟩, hw⟩

def nativeInclusion (v : P.NativeUnitTangentOver D.nativeChart) :
    P.NativeComponentInteriorUnitTangentOver i :=
  ⟨v.val, D.native_source_interior v.val.val.proj v.property⟩

theorem tangentInclusion_isOpenEmbedding : Topology.IsOpenEmbedding D.tangentInclusion := by
  apply Topology.IsOpenEmbedding.inclusion
  · intro q hq
    exact D.tangent_interior ⟨q, hq⟩
  have hopen : IsOpen ((X i).orbitProjection '' ball D.center D.radius) :=
    isOpenMap_quotient_mk'_mul _ Metric.isOpen_ball
  exact (hopen.preimage (X i).continuous_tangentFrameBase).preimage continuous_subtype_val

theorem nativeInclusion_isOpenEmbedding : Topology.IsOpenEmbedding D.nativeInclusion := by
  apply Topology.IsOpenEmbedding.inclusion
  · intro v hv
    exact D.native_source_interior v.val.proj hv
  exact (D.nativeChart.open_source.preimage
    ((FiberBundle.continuous_proj ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)).comp
        continuous_subtype_val)).preimage continuous_subtype_val

theorem tangentHomeomorph_proj (q : (X i).TangentBallCarrier D.center D.radius) :
    (D.tangentHomeomorph q).val.val.proj =
      P.gluedMk (P.componentInteriorPoint i
        ⟨(X i).tangentFrameBase q.val, D.tangent_interior q⟩) := by
  obtain ⟨h, heq⟩ := P.interiorTangentNativeUnitHomeomorph_proj
    i D.center D.radius D.radius_pos D.radius_small D.interior D.open_embedding q
  exact heq

theorem tangentHomeomorph_overlap (D' : P.ComponentInteriorBallChart i)
    (q : (X i).TangentBallCarrier D.center D.radius)
    (q' : (X i).TangentBallCarrier D'.center D'.radius) (h : q.val = q'.val) :
    (D.tangentHomeomorph q).val = (D'.tangentHomeomorph q').val :=
  P.interiorTangentNativeUnitHomeomorph_overlap i D.center D.radius D.radius_pos D.radius_small
    D.interior D.open_embedding D'.center D'.radius D'.radius_pos D'.radius_small
    D'.interior D'.open_embedding q q' h

end ComponentInteriorBallChart

/-- The selected genuine ball contains every actual tangent orbit over its
center's original component base. -/
def componentInteriorTangentLocal (q : P.ComponentInteriorTangentCarrier i) :
    (X i).TangentBallCarrier
      (P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase q.val, q.property⟩).center
      (P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase q.val, q.property⟩).radius :=
  ⟨q.val, _, Metric.mem_ball_self (P.componentInteriorBallChartAt i
    ⟨(X i).tangentFrameBase q.val, q.property⟩).radius_pos,
    P.componentInteriorBallChartAt_base i ⟨(X i).tangentFrameBase q.val, q.property⟩⟩

/-- Chart-independent native transport on the entire original component
interior, defined using verified real ball sheets. -/
def nativeComponentInteriorUnitTangent (q : P.ComponentInteriorTangentCarrier i) :
    P.NativeComponentInteriorUnitTangentOver i :=
  let D := P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase q.val, q.property⟩
  D.nativeInclusion (D.tangentHomeomorph (P.componentInteriorTangentLocal i q))

theorem nativeComponentInteriorUnitTangent_local
    (D : P.ComponentInteriorBallChart i) (q : (X i).TangentBallCarrier D.center D.radius) :
    P.nativeComponentInteriorUnitTangent i (D.tangentInclusion q) =
      D.nativeInclusion (D.tangentHomeomorph q) := by
  apply Subtype.ext
  exact ComponentInteriorBallChart.tangentHomeomorph_overlap _ D
    (P.componentInteriorTangentLocal i (D.tangentInclusion q)) q rfl

theorem nativeComponentInteriorUnitTangent_proj (q : P.ComponentInteriorTangentCarrier i) :
    (P.nativeComponentInteriorUnitTangent i q).val.val.proj =
      P.gluedMk (P.componentInteriorPoint i ⟨(X i).tangentFrameBase q.val, q.property⟩) :=
  ComponentInteriorBallChart.tangentHomeomorph_proj _ (P.componentInteriorTangentLocal i q)

theorem continuous_nativeComponentInteriorUnitTangent :
    Continuous (P.nativeComponentInteriorUnitTangent i) := by
  rw [continuous_iff_continuousAt]
  intro q
  let D := P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase q.val, q.property⟩
  let qlocal := P.componentInteriorTangentLocal i q
  have hcomp : Continuous ((P.nativeComponentInteriorUnitTangent i) ∘ D.tangentInclusion) := by
    have heq : (P.nativeComponentInteriorUnitTangent i) ∘ D.tangentInclusion =
        D.nativeInclusion ∘ D.tangentHomeomorph :=
      funext (P.nativeComponentInteriorUnitTangent_local i D)
    rw [heq]
    exact D.nativeInclusion_isOpenEmbedding.continuous.comp D.tangentHomeomorph.continuous
  exact D.tangentInclusion_isOpenEmbedding.continuousAt_iff.mp (hcomp.continuousAt (x := qlocal))

theorem nativeComponentInteriorUnitTangent_injective :
    Function.Injective (P.nativeComponentInteriorUnitTangent i) := by
  intro q q' h
  have hb := congrArg (fun v : P.NativeComponentInteriorUnitTangentOver i => v.val.val.proj) h
  rw [P.nativeComponentInteriorUnitTangent_proj, P.nativeComponentInteriorUnitTangent_proj] at hb
  have hbase : (X i).tangentFrameBase q.val = (X i).tangentFrameBase q'.val :=
    congrArg Subtype.val ((P.gluedComponentInterior_isOpenEmbedding i).injective hb)
  let D := P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase q.val, q.property⟩
  let r := P.componentInteriorTangentLocal i q
  let r' : (X i).TangentBallCarrier D.center D.radius :=
    ⟨q'.val, hbase ▸ r.property⟩
  have hq : D.tangentInclusion r = q := rfl
  have hq' : D.tangentInclusion r' = q' := rfl
  rw [← hq, ← hq', P.nativeComponentInteriorUnitTangent_local,
    P.nativeComponentInteriorUnitTangent_local] at h
  have hlocal := D.nativeInclusion_isOpenEmbedding.injective h
  apply Subtype.ext
  exact congrArg (fun t : (X i).TangentBallCarrier D.center D.radius => t.val)
    (D.tangentHomeomorph.injective hlocal)

theorem componentInteriorBallChartAt_native_source (q : P.componentInteriorSet i) :
    P.gluedMk (P.componentInteriorPoint i q) ∈
      (P.componentInteriorBallChartAt i q).nativeChart.source := by
  let D := P.componentInteriorBallChartAt i q
  let w : ball D.center D.radius := ⟨D.center, Metric.mem_ball_self D.radius_pos⟩
  have hsource := (P.interiorBallSourceHomeomorph i D.center D.radius D.radius_pos
    D.interior D.open_embedding w).property
  change P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' D.center, D.interior w⟩) ∈
    D.nativeChart.source at hsource
  have heq : (⟨Quotient.mk'' D.center, D.interior w⟩ : P.componentInteriorSet i) = q :=
    Subtype.ext (P.componentInteriorBallChartAt_base i q)
  have hpoint := congrArg
    (fun b : P.componentInteriorSet i => P.gluedMk (P.componentInteriorPoint i b)) heq
  change P.gluedMk (P.componentInteriorPoint i q) ∈ D.nativeChart.source
  rw [← hpoint]
  exact hsource

theorem nativeComponentInteriorUnitTangent_surjective :
    Function.Surjective (P.nativeComponentInteriorUnitTangent i) := by
  intro v
  obtain ⟨q, hq⟩ := v.property
  let D := P.componentInteriorBallChartAt i q
  have hv : v.val.val.proj ∈ D.nativeChart.source :=
    hq ▸ P.componentInteriorBallChartAt_native_source i q
  let vlocal : P.NativeUnitTangentOver D.nativeChart := ⟨v.val, hv⟩
  refine ⟨D.tangentInclusion (D.tangentHomeomorph.symm vlocal), ?_⟩
  rw [P.nativeComponentInteriorUnitTangent_local, D.tangentHomeomorph.apply_symm_apply]
  rfl

theorem nativeComponentInteriorUnitTangent_isOpenMap :
    IsOpenMap (P.nativeComponentInteriorUnitTangent i) := by
  intro s hs
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨q, hq, rfl⟩
  let D := P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase q.val, q.property⟩
  let qlocal := P.componentInteriorTangentLocal i q
  let t := D.nativeInclusion '' (D.tangentHomeomorph '' (D.tangentInclusion ⁻¹' s))
  have ht : IsOpen t := D.nativeInclusion_isOpenEmbedding.isOpenMap _
    (D.tangentHomeomorph.isOpenMap _ (hs.preimage D.tangentInclusion_isOpenEmbedding.continuous))
  have hmem : P.nativeComponentInteriorUnitTangent i q ∈ t := by
    rw [← show D.tangentInclusion qlocal = q from rfl,
      P.nativeComponentInteriorUnitTangent_local]
    exact ⟨D.tangentHomeomorph qlocal, ⟨qlocal, hq, rfl⟩, rfl⟩
  have hsub : t ⊆ P.nativeComponentInteriorUnitTangent i '' s := by
    rintro v ⟨vlocal, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨D.tangentInclusion r, hr, P.nativeComponentInteriorUnitTangent_local i D r⟩
  exact mem_of_superset (ht.mem_nhds hmem) hsub

/-- Entire original component-interior tangent-orbit carrier identified
homeomorphically with the prescribed native unit bundle, not a phase model. -/
def nativeComponentInteriorUnitTangentHomeomorph :
    P.ComponentInteriorTangentCarrier i ≃ₜ P.NativeComponentInteriorUnitTangentOver i :=
  IsHomeomorph.homeomorph (P.nativeComponentInteriorUnitTangent i)
    ⟨P.continuous_nativeComponentInteriorUnitTangent i,
      P.nativeComponentInteriorUnitTangent_isOpenMap i,
      P.nativeComponentInteriorUnitTangent_injective i,
      P.nativeComponentInteriorUnitTangent_surjective i⟩

@[simp] theorem nativeComponentInteriorUnitTangentHomeomorph_apply
    (q : P.ComponentInteriorTangentCarrier i) :
    P.nativeComponentInteriorUnitTangentHomeomorph i q =
      P.nativeComponentInteriorUnitTangent i q := rfl

theorem nativeComponentInteriorUnitTangentHomeomorph_proj
    (q : P.ComponentInteriorTangentCarrier i) :
    (P.nativeComponentInteriorUnitTangentHomeomorph i q).val.val.proj =
      P.gluedMk (P.componentInteriorPoint i ⟨(X i).tangentFrameBase q.val, q.property⟩) :=
  P.nativeComponentInteriorUnitTangent_proj i q

/-- On every genuine component ball sheet, the global identification is
exactly the previously verified physical local native homeomorphism. -/
theorem nativeComponentInteriorUnitTangentHomeomorph_local_apply
    (D : P.ComponentInteriorBallChart i) (q : (X i).TangentBallCarrier D.center D.radius) :
    P.nativeComponentInteriorUnitTangentHomeomorph i (D.tangentInclusion q) =
      D.nativeInclusion (D.tangentHomeomorph q) :=
  P.nativeComponentInteriorUnitTangent_local i D q

/-- The inverse reads the actual component frame orbit using any valid
physical local sheet; it does not depend on a newly selected phase atlas. -/
theorem nativeComponentInteriorUnitTangentHomeomorph_symm_local_apply
    (D : P.ComponentInteriorBallChart i) (v : P.NativeUnitTangentOver D.nativeChart) :
    (P.nativeComponentInteriorUnitTangentHomeomorph i).symm (D.nativeInclusion v) =
      D.tangentInclusion (D.tangentHomeomorph.symm v) := by
  apply (P.nativeComponentInteriorUnitTangentHomeomorph i).injective
  rw [(P.nativeComponentInteriorUnitTangentHomeomorph i).apply_symm_apply,
    P.nativeComponentInteriorUnitTangentHomeomorph_local_apply,
    D.tangentHomeomorph.apply_symm_apply]

theorem nativeComponentInteriorUnitTangentHomeomorph_symm_proj
    (v : P.NativeComponentInteriorUnitTangentOver i) :
    P.gluedMk (P.componentInteriorPoint i
      ⟨(X i).tangentFrameBase ((P.nativeComponentInteriorUnitTangentHomeomorph i).symm v).val,
        ((P.nativeComponentInteriorUnitTangentHomeomorph i).symm v).property⟩) = v.val.val.proj := by
  have h := P.nativeComponentInteriorUnitTangentHomeomorph_proj i
    ((P.nativeComponentInteriorUnitTangentHomeomorph i).symm v)
  rw [(P.nativeComponentInteriorUnitTangentHomeomorph i).apply_symm_apply] at h
  exact h.symm

end

#print axioms gluedInteriorBallChart_transition_eventually_eq_componentDeck
#print axioms nativeInteriorBallUnitTangentParam_overlap
#print axioms interiorBallNativeUnitHomeomorph_eq_of_frame_orbit
#print axioms nativeComponentInteriorUnitTangentHomeomorph
#print axioms nativeComponentInteriorUnitTangentHomeomorph_local_apply
#print axioms nativeComponentInteriorUnitTangentHomeomorph_symm_local_apply

end SystolicGrowth.ExerciseGluingPreparation
