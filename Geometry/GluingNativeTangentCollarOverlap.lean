module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingNativeTangentDescent
public import Geometry.GluingNativeComponentTangentEquivariance

@[expose] public section

/-!
# Literal physical frame agreement on retained collar overlaps

The transition witnesses belong to the original component deck subgroup.
Its free action identifies the actual tangent phase, not merely the base.
-/

open Set Metric UpperHalfPlane Filter Bundle
open scoped UpperHalfPlane MatrixGroups Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem seamPoint_mem_chart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularPoint k θ p ∈ (P.seamAngularComplexChart k θ).source := by
  rw [P.seamAngularComplexChart_source]
  exact ⟨p, rfl⟩

private theorem nativeUnitCoord_injective
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) :
    Function.Injective (P.nativeUnitTangentCoord e he b) := by
  intro v w h
  apply Subtype.ext
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  apply (t.continuousLinearEquivAt ℝ b (by exact hb)).injective
  rw [t.coe_continuousLinearEquivAt_eq (by exact hb)]
  exact h

private theorem incoming_actualDeck_unit_overlap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hs : 0 < p.1.1)
    (D : P.ComponentInteriorBallChart (gluingChainEdgeRight k))
    (hb : P.seamAngularPoint k θ p ∈ D.nativeChart.source) :
    ∃ A : (X (gluingChainEdgeRight k)).deckGroup,
      D.nativeChart (P.seamAngularPoint k θ p) =
        ((A • gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
          (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1) : ℍ) : ℂ) ∧
      ∀ u : Circle,
        P.incomingNativeUnitTangent k (P.centers (gluingChainEdgeRight k)).1 θ p hs.le u =
          P.nativeUnitTangentParam D.nativeChart
            (Or.inl ⟨_, D.center, D.radius, D.radius_pos, D.radius_small,
              D.interior, D.open_embedding, rfl⟩)
            (P.seamAngularPoint k θ p) hb
            (halfPlaneSpinCircle A.val (gluingPolarPoint
              (P.centers (gluingChainEdgeRight k)).1 (Circle.exp (-p.2.1))
                (gluingRadius C g + p.1.1)) ^ 2 * u) := by
  let x := gluingSeamAngularModel C g θ p
  let b := P.seamAngularPoint k θ p
  let o := (P.centers (gluingChainEdgeRight k)).1
  let z := gluingPolarPoint o (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1)
  have hsource := seamPoint_mem_chart P k θ p
  have htarget : x ∈ (P.seamAngularComplexChart k θ).target := by
    dsimp only [x]
    rw [← P.seamAngularComplexChart_apply k θ p]
    exact (P.seamAngularComplexChart k θ).map_source hsource
  have hsymm : (P.seamAngularComplexChart k θ).symm x = b :=
    P.seamAngularComplexChart_symm_apply k θ p
  obtain ⟨A, hA⟩ := P.incomingSeamInteriorTransition_eventually_eq_deck k θ
    D.center D.radius D.radius_pos D.interior D.open_embedding x htarget hs
      (hsymm.symm ▸ hb)
  have hAz : ((A • z : ℍ) : ℂ) = D.nativeChart b := by
    change ((A.val • z : ℍ) : ℂ) = D.nativeChart b
    rw [← gluingDeckComplex_coe A.val]
    exact hA.self_of_nhds.symm.trans (congrArg D.nativeChart hsymm)
  have hA' : ((P.seamAngularComplexChart k θ).symm.trans D.nativeChart : ℂ → ℂ) =ᶠ[𝓝 x]
      gluingDeckComplex A.val ∘ gluingIncomingPolarLift o (gluingRadius C g) := hA
  refine ⟨A, hAz.symm, ?_⟩
  intro u
  have he : P.IsGluedInteriorComplexChart D.nativeChart :=
    ⟨_, D.center, D.radius, D.radius_pos, D.radius_small,
      D.interior, D.open_embedding, rfl⟩
  apply nativeUnitCoord_injective P D.nativeChart (Or.inl he) b hb
  rw [P.nativeInteriorUnitTangentParam_coordinates D.nativeChart he b hb]
  rw [P.nativeUnitTangentCoord_change (P.seamAngularComplexChart k θ) D.nativeChart
    (Or.inr ⟨k, θ, rfl⟩) (Or.inl he) b hsource hb]
  have hc : P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b (P.incomingNativeUnitTangent k o θ p hs.le u) =
      P.incomingNativeUnitCoordinates o θ p hs.le u :=
    P.nativeUnitTangentCoord_ofCoordinates _ _ _ _ _ _
  rw [hc, P.seamAngularComplexChart_apply]
  change fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans D.nativeChart : ℂ → ℂ) x
    (P.incomingNativeUnitCoordinates o θ p hs.le u) = _
  rw [hA'.fderiv_eq,
    fderiv_comp (f := gluingIncomingPolarLift o (gluingRadius C g))
      (g := gluingDeckComplex A.val) x
      (gluingDeckComplex_hasFDerivAt_equiv A.val z.im_pos).differentiableAt
      ((gluingIncomingPolarLift_contDiff o (gluingRadius C g)).differentiable
        (by simp)).differentiableAt,
    ContinuousLinearMap.comp_apply]
  dsimp only [x]
  rw [P.incomingNativeUnitCoordinates_fderiv o θ p hs.le u,
    Circle.coe_mul, Circle.coe_pow]
  change fderiv ℝ (gluingDeckComplex A.val) (z : ℂ) ((z.im : ℂ) * (u : ℂ)) =
    ((D.nativeChart b).im : ℂ) * ((halfPlaneSpinCircle A.val z : ℂ) ^ 2 * (u : ℂ))
  rw [← (show (A • z : ℍ).im = (D.nativeChart b).im from congrArg Complex.im hAz)]
  exact P.componentDeck_fderiv_physical_unit _ A z u

private theorem outgoing_actualDeck_unit_overlap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hs : p.1.1 < 0)
    (D : P.ComponentInteriorBallChart (gluingChainEdgeLeft k))
    (hb : P.seamAngularPoint k θ p ∈ D.nativeChart.source) :
    ∃ A : (X (gluingChainEdgeLeft k)).deckGroup,
      D.nativeChart (P.seamAngularPoint k θ p) =
        ((A • gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
          (Circle.exp p.2.1) (gluingRadius C g - p.1.1) : ℍ) : ℂ) ∧
      ∀ u : Circle,
        P.outgoingNativeUnitTangent k (P.centers (gluingChainEdgeLeft k)).2 θ p hs.le u =
          P.nativeUnitTangentParam D.nativeChart
            (Or.inl ⟨_, D.center, D.radius, D.radius_pos, D.radius_small,
              D.interior, D.open_embedding, rfl⟩)
            (P.seamAngularPoint k θ p) hb
            (halfPlaneSpinCircle A.val (gluingPolarPoint
              (P.centers (gluingChainEdgeLeft k)).2 (Circle.exp p.2.1)
                (gluingRadius C g - p.1.1)) ^ 2 * u) := by
  let x := gluingSeamAngularModel C g θ p
  let b := P.seamAngularPoint k θ p
  let o := (P.centers (gluingChainEdgeLeft k)).2
  let z := gluingPolarPoint o (Circle.exp p.2.1) (gluingRadius C g - p.1.1)
  have hsource := seamPoint_mem_chart P k θ p
  have htarget : x ∈ (P.seamAngularComplexChart k θ).target := by
    dsimp only [x]
    rw [← P.seamAngularComplexChart_apply k θ p]
    exact (P.seamAngularComplexChart k θ).map_source hsource
  have hsymm : (P.seamAngularComplexChart k θ).symm x = b :=
    P.seamAngularComplexChart_symm_apply k θ p
  obtain ⟨A, hA⟩ := P.outgoingSeamInteriorTransition_eventually_eq_deck k θ
    D.center D.radius D.radius_pos D.interior D.open_embedding x htarget hs
      (hsymm.symm ▸ hb)
  have hAz : ((A • z : ℍ) : ℂ) = D.nativeChart b := by
    change ((A.val • z : ℍ) : ℂ) = D.nativeChart b
    rw [← gluingDeckComplex_coe A.val]
    exact hA.self_of_nhds.symm.trans (congrArg D.nativeChart hsymm)
  have hA' : ((P.seamAngularComplexChart k θ).symm.trans D.nativeChart : ℂ → ℂ) =ᶠ[𝓝 x]
      gluingDeckComplex A.val ∘ gluingOutgoingPolarLift o (gluingRadius C g) := hA
  refine ⟨A, hAz.symm, ?_⟩
  intro u
  have he : P.IsGluedInteriorComplexChart D.nativeChart :=
    ⟨_, D.center, D.radius, D.radius_pos, D.radius_small,
      D.interior, D.open_embedding, rfl⟩
  apply nativeUnitCoord_injective P D.nativeChart (Or.inl he) b hb
  rw [P.nativeInteriorUnitTangentParam_coordinates D.nativeChart he b hb]
  rw [P.nativeUnitTangentCoord_change (P.seamAngularComplexChart k θ) D.nativeChart
    (Or.inr ⟨k, θ, rfl⟩) (Or.inl he) b hsource hb]
  have hc : P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b (P.outgoingNativeUnitTangent k o θ p hs.le u) =
      P.outgoingNativeUnitCoordinates o θ p hs.le u :=
    P.nativeUnitTangentCoord_ofCoordinates _ _ _ _ _ _
  rw [hc, P.seamAngularComplexChart_apply]
  change fderiv ℝ ((P.seamAngularComplexChart k θ).symm.trans D.nativeChart : ℂ → ℂ) x
    (P.outgoingNativeUnitCoordinates o θ p hs.le u) = _
  rw [hA'.fderiv_eq,
    fderiv_comp (f := gluingOutgoingPolarLift o (gluingRadius C g))
      (g := gluingDeckComplex A.val) x
      (gluingDeckComplex_hasFDerivAt_equiv A.val z.im_pos).differentiableAt
      ((gluingOutgoingPolarLift_contDiff o (gluingRadius C g)).differentiable
        (by simp)).differentiableAt,
    ContinuousLinearMap.comp_apply]
  dsimp only [x]
  rw [P.outgoingNativeUnitCoordinates_fderiv o θ p hs.le u,
    Circle.coe_mul, Circle.coe_pow]
  change fderiv ℝ (gluingDeckComplex A.val) (z : ℂ) ((z.im : ℂ) * (u : ℂ)) =
    ((D.nativeChart b).im : ℂ) * ((halfPlaneSpinCircle A.val z : ℂ) ^ 2 * (u : ℂ))
  rw [← (show (A • z : ℍ).im = (D.nativeChart b).im from congrArg Complex.im hAz)]
  exact P.componentDeck_fderiv_physical_unit _ A z u

private theorem incomingNativeUnitTangentTotal_eq_interiorBall
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hs : 0 < p.1.1)
    (D : P.ComponentInteriorBallChart (gluingChainEdgeRight k))
    (w : ball D.center D.radius) (u u' : Circle)
    (horbit : (Quotient.mk _ (⟨gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
        (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1), u⟩ : HalfPlaneTangentFrame) :
          (X (gluingChainEdgeRight k)).TangentFrameCarrier) =
        Quotient.mk _ (⟨w.val, u'⟩ : HalfPlaneTangentFrame)) :
    P.incomingNativeUnitTangentTotal k (P.centers (gluingChainEdgeRight k)).1 θ p hs.le u =
      (P.interiorBallNativeUnitHomeomorph _ D.center D.radius D.radius_pos D.radius_small
        D.interior D.open_embedding (w, u')).val := by
  let i := gluingChainEdgeRight k
  let z := gluingPolarPoint (P.centers i).1 (Circle.exp (-p.2.1))
    (gluingRadius C g + p.1.1)
  let b := P.seamAngularPoint k θ p
  let b' := P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.val, D.interior w⟩)
  have hquot : (Quotient.mk'' z : (X i).Carrier) = Quotient.mk'' w.val :=
    congrArg (X i).tangentFrameBase horbit
  have hbase : b = b' := by
    dsimp only [b]
    rw [P.seamAngularPoint_of_nonneg k θ p hs.le]
    apply congrArg P.gluedMk
    have hquot' : (Quotient.mk'' (gluingPolarPoint (P.centers i).1
        (Circle.exp p.2.val)⁻¹ (gluingRadius C g + p.1.val)) : (X i).Carrier) =
        Quotient.mk'' w.val := by
      simpa only [z, Circle.exp_neg] using hquot
    exact congrArg (fun q : P.ChainComponent i => (⟨i, q⟩ : P.ChainPieces))
      (Subtype.ext hquot')
  have hb' : b' ∈ D.nativeChart.source :=
    (P.interiorBallSourceHomeomorph i D.center D.radius D.radius_pos
      D.interior D.open_embedding w).property
  have hb : b ∈ D.nativeChart.source := hbase.symm ▸ hb'
  have heval : D.nativeChart b = (w.val : ℂ) :=
    hbase.symm ▸ P.gluedInteriorComplexChart_apply i D.center D.radius D.radius_pos
      D.interior D.open_embedding w
  obtain ⟨A, hApoint, hAunit⟩ := P.incoming_actualDeck_unit_overlap k θ p hs D hb
  have hpoint : A • z = w.val := by
    apply UpperHalfPlane.coe_injective
    exact hApoint.symm.trans heval
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact horbit.symm))
  have hBpoint : B • z = w.val := congrArg HalfPlaneTangentFrame.point hB
  have hfix : (B⁻¹ * A) • z = z := by
    rw [mul_smul, hpoint, ← hBpoint, inv_smul_smul]
  have hAB : A = B := (inv_mul_eq_one.mp ((X i).free (B⁻¹ * A) z hfix)).symm
  subst B
  have hphase : halfPlaneSpinCircle A.val z ^ 2 * u = u' :=
    congrArg HalfPlaneTangentFrame.phase hB
  have hunit := hAunit u
  rw [hphase] at hunit
  have hsame (b₁ b₂ : P.GluedCarrier) (h : b₁ = b₂)
      (h₁ : b₁ ∈ D.nativeChart.source) (h₂ : b₂ ∈ D.nativeChart.source) :
      TotalSpace.mk' ℂ b₁ (P.nativeUnitTangentParam D.nativeChart
        (Or.inl ⟨i, D.center, D.radius, D.radius_pos, D.radius_small,
          D.interior, D.open_embedding, rfl⟩) b₁ h₁ u').val =
      TotalSpace.mk' ℂ b₂ (P.nativeUnitTangentParam D.nativeChart
        (Or.inl ⟨i, D.center, D.radius, D.radius_pos, D.radius_small,
          D.interior, D.open_embedding, rfl⟩) b₂ h₂ u').val := by
    subst b₂
    rfl
  apply Subtype.ext
  exact (congrArg (fun v : P.NativeUnitTangentFiber b => TotalSpace.mk' ℂ b v.val) hunit).trans
    (hsame b b' hbase hb hb')

private theorem outgoingNativeUnitTangentTotal_eq_interiorBall
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hs : p.1.1 < 0)
    (D : P.ComponentInteriorBallChart (gluingChainEdgeLeft k))
    (w : ball D.center D.radius) (u u' : Circle)
    (horbit : (Quotient.mk _ (⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
        (Circle.exp p.2.1) (gluingRadius C g - p.1.1), u⟩ : HalfPlaneTangentFrame) :
          (X (gluingChainEdgeLeft k)).TangentFrameCarrier) =
        Quotient.mk _ (⟨w.val, u'⟩ : HalfPlaneTangentFrame)) :
    P.outgoingNativeUnitTangentTotal k (P.centers (gluingChainEdgeLeft k)).2 θ p hs.le u =
      (P.interiorBallNativeUnitHomeomorph _ D.center D.radius D.radius_pos D.radius_small
        D.interior D.open_embedding (w, u')).val := by
  let i := gluingChainEdgeLeft k
  let z := gluingPolarPoint (P.centers i).2 (Circle.exp p.2.1)
    (gluingRadius C g - p.1.1)
  let b := P.seamAngularPoint k θ p
  let b' := P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.val, D.interior w⟩)
  have hquot : (Quotient.mk'' z : (X i).Carrier) = Quotient.mk'' w.val :=
    congrArg (X i).tangentFrameBase horbit
  have hbase : b = b' := by
    dsimp only [b]
    rw [P.seamAngularPoint_of_nonpos k θ p hs.le]
    apply congrArg P.gluedMk
    exact congrArg (fun q : P.ChainComponent i => (⟨i, q⟩ : P.ChainPieces))
      (Subtype.ext hquot)
  have hb' : b' ∈ D.nativeChart.source :=
    (P.interiorBallSourceHomeomorph i D.center D.radius D.radius_pos
      D.interior D.open_embedding w).property
  have hb : b ∈ D.nativeChart.source := hbase.symm ▸ hb'
  have heval : D.nativeChart b = (w.val : ℂ) :=
    hbase.symm ▸ P.gluedInteriorComplexChart_apply i D.center D.radius D.radius_pos
      D.interior D.open_embedding w
  obtain ⟨A, hApoint, hAunit⟩ := P.outgoing_actualDeck_unit_overlap k θ p hs D hb
  have hpoint : A • z = w.val := by
    apply UpperHalfPlane.coe_injective
    exact hApoint.symm.trans heval
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact horbit.symm))
  have hBpoint : B • z = w.val := congrArg HalfPlaneTangentFrame.point hB
  have hfix : (B⁻¹ * A) • z = z := by
    rw [mul_smul, hpoint, ← hBpoint, inv_smul_smul]
  have hAB : A = B := (inv_mul_eq_one.mp ((X i).free (B⁻¹ * A) z hfix)).symm
  subst B
  have hphase : halfPlaneSpinCircle A.val z ^ 2 * u = u' :=
    congrArg HalfPlaneTangentFrame.phase hB
  have hunit := hAunit u
  rw [hphase] at hunit
  have hsame (b₁ b₂ : P.GluedCarrier) (h : b₁ = b₂)
      (h₁ : b₁ ∈ D.nativeChart.source) (h₂ : b₂ ∈ D.nativeChart.source) :
      TotalSpace.mk' ℂ b₁ (P.nativeUnitTangentParam D.nativeChart
        (Or.inl ⟨i, D.center, D.radius, D.radius_pos, D.radius_small,
          D.interior, D.open_embedding, rfl⟩) b₁ h₁ u').val =
      TotalSpace.mk' ℂ b₂ (P.nativeUnitTangentParam D.nativeChart
        (Or.inl ⟨i, D.center, D.radius, D.radius_pos, D.radius_small,
          D.interior, D.open_embedding, rfl⟩) b₂ h₂ u').val := by
    subst b₂
    rfl
  apply Subtype.ext
  exact (congrArg (fun v : P.NativeUnitTangentFiber b => TotalSpace.mk' ℂ b v.val) hunit).trans
    (hsame b b' hbase hb hb')

private theorem incoming_polar_radius_strict_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (a : Circle) (R : Ico (gluingRadius C g) (gluingEmbeddedRadius C g))
    (hi : (Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1 a R) :
      (X (gluingChainEdgeRight k)).Carrier) ∈ P.componentInteriorSet (gluingChainEdgeRight k)) :
    gluingRadius C g < R.val := by
  refine lt_of_le_of_ne R.property.1 ?_
  intro heq
  have hcircle : (Quotient.mk''
      (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1 a R) :
      (X (gluingChainEdgeRight k)).Carrier) ∈
        (X (gluingChainEdgeRight k)).punctureCircle
          (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) := by
    refine ⟨_, ?_, rfl⟩
    rw [mem_sphere, dist_comm, dist_gluingPolarPoint _ _ (P.radius_pos.le.trans R.property.1)]
    exact heq.symm
  have hindex : 0 < (gluingChainEdgeRight k).val := by
    change 0 < k.val + 1
    omega
  have hball : (X (gluingChainEdgeRight k)).orbitBall
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) ⊆
      (X (gluingChainEdgeRight k)).punctureDeletedSet
        (P.centers (gluingChainEdgeRight k)).1 (P.centers (gluingChainEdgeRight k)).2
          (gluingRadius C g) (gluingChainEdgeRight k) := by
    intro q hq
    simp only [ClosedHyperbolicSurface.punctureDeletedSet, if_pos hindex, Set.mem_union]
    exact Or.inl hq
  exact punctureCircle_not_mem_interior _ _ _ _ P.radius_pos _ hball hcircle hi

private theorem outgoing_polar_radius_strict_of_interior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (a : Circle) (R : Ico (gluingRadius C g) (gluingEmbeddedRadius C g))
    (hi : (Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 a R) :
      (X (gluingChainEdgeLeft k)).Carrier) ∈ P.componentInteriorSet (gluingChainEdgeLeft k)) :
    gluingRadius C g < R.val := by
  refine lt_of_le_of_ne R.property.1 ?_
  intro heq
  have hcircle : (Quotient.mk''
      (gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 a R) :
      (X (gluingChainEdgeLeft k)).Carrier) ∈
        (X (gluingChainEdgeLeft k)).punctureCircle
          (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) := by
    refine ⟨_, ?_, rfl⟩
    rw [mem_sphere, dist_comm, dist_gluingPolarPoint _ _ (P.radius_pos.le.trans R.property.1)]
    exact heq.symm
  have hindex : (gluingChainEdgeLeft k).val + 1 < n := by
    change k.val + 1 < n
    omega
  have hball : (X (gluingChainEdgeLeft k)).orbitBall
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) ⊆
      (X (gluingChainEdgeLeft k)).punctureDeletedSet
        (P.centers (gluingChainEdgeLeft k)).1 (P.centers (gluingChainEdgeLeft k)).2
          (gluingRadius C g) (gluingChainEdgeLeft k) := by
    intro q hq
    simp only [ClosedHyperbolicSurface.punctureDeletedSet, if_pos hindex, Set.mem_union]
    exact Or.inr hq
  exact punctureCircle_not_mem_interior _ _ _ _ P.radius_pos _ hball hcircle hi

/-- A literal incoming retained frame has the same actual native unit vector
whether transported through its component interior or its physical collar. -/
theorem incomingTangentCollarNativeUnit_eq_componentInterior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.IncomingTangentCollar (gluingChainEdgeRight k))
    (hi : (X (gluingChainEdgeRight k)).tangentFrameBase q.val.val ∈
      P.componentInteriorSet (gluingChainEdgeRight k)) :
    P.incomingTangentCollarNativeUnit k q =
      (P.nativeComponentInteriorUnitTangentHomeomorph (gluingChainEdgeRight k)
        ⟨q.val.val, hi⟩).val := by
  obtain ⟨c, rfl⟩ := (P.incomingTangentCollarPolarHomeomorph _).surjective q
  let i := gluingChainEdgeRight k
  let a := c.1.1
  let R := c.1.2
  have hr : gluingRadius C g < R.val := P.incoming_polar_radius_strict_of_interior k a R hi
  let θ := -(a : ℂ).arg
  let p : GluingSeamAngularDomain C g θ :=
    (⟨R.val - gluingRadius C g, by
      constructor
      · linarith [P.depth_pos]
      · change R.val - gluingRadius C g < gluingDepth C g
        have hR : R.val < gluingRadius C g + gluingDepth C g := R.property.2
        linarith⟩, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  have hs : 0 < p.1.val := sub_pos.mpr hr
  have hpol : ((Circle.exp (-p.2.val), ⟨gluingRadius C g + p.1.val, by
      constructor
      · linarith
      · change gluingRadius C g + p.1.val < gluingRadius C g + gluingDepth C g
        linarith [p.1.property.2]⟩), c.2) = c := by
    apply Prod.ext
    · apply Prod.ext
      · change Circle.exp (-(-(a : ℂ).arg)) = a
        rw [neg_neg, Circle.exp_arg]
      · apply Subtype.ext
        change gluingRadius C g + (R.val - gluingRadius C g) = R.val
        ring
    · rfl
  have hleft := P.incomingTangentCollarNativeUnit_local_apply k θ p hs.le c.2
  rw [hpol] at hleft
  rw [hleft]
  let qi : P.ComponentInteriorTangentCarrier i :=
    ⟨(P.incomingTangentCollarPolarHomeomorph i c).val.val, hi⟩
  let D := P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase qi.val, qi.property⟩
  let qlocal := P.componentInteriorTangentLocal i qi
  let T := (X i).tangentBallHomeomorph D.center
    (show 2 * D.radius < (X i).systole by linarith [D.radius_small, D.radius_pos])
  let w := T.symm qlocal
  have hw : (Quotient.mk _ (⟨w.1.val, w.2⟩ : HalfPlaneTangentFrame) :
      (X i).TangentFrameCarrier) = qi.val :=
    congrArg Subtype.val (T.apply_symm_apply qlocal)
  rw [P.nativeComponentInteriorUnitTangentHomeomorph_apply]
  change _ = (P.interiorBallNativeUnitHomeomorph i D.center D.radius D.radius_pos
    D.radius_small D.interior D.open_embedding w).val
  apply P.incomingNativeUnitTangentTotal_eq_interiorBall k θ p hs D w.1 c.2 w.2
  have hpc := congrArg (fun d => (P.incomingTangentCollarPolarHomeomorph i d).val.val) hpol
  exact hpc.trans hw.symm

/-- The outgoing physical collar and component interior transport agree on
their literal retained-frame overlap, including the corrected orientation. -/
theorem outgoingTangentCollarNativeUnit_eq_componentInterior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.OutgoingTangentCollar (gluingChainEdgeLeft k))
    (hi : (X (gluingChainEdgeLeft k)).tangentFrameBase q.val.val ∈
      P.componentInteriorSet (gluingChainEdgeLeft k)) :
    P.outgoingTangentCollarNativeUnit k q =
      (P.nativeComponentInteriorUnitTangentHomeomorph (gluingChainEdgeLeft k)
        ⟨q.val.val, hi⟩).val := by
  obtain ⟨c, rfl⟩ := (P.outgoingTangentCollarPolarHomeomorph _).surjective q
  let i := gluingChainEdgeLeft k
  let a := c.1.1
  let R := c.1.2
  have hr : gluingRadius C g < R.val := P.outgoing_polar_radius_strict_of_interior k a R hi
  let θ := (a : ℂ).arg
  let p : GluingSeamAngularDomain C g θ :=
    (⟨gluingRadius C g - R.val, by
      constructor
      · change -gluingDepth C g < gluingRadius C g - R.val
        have hR : R.val < gluingRadius C g + gluingDepth C g := R.property.2
        linarith
      · linarith [P.depth_pos]⟩, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  have hs : p.1.val < 0 := sub_neg.mpr hr
  have hpol : ((Circle.exp p.2.val, ⟨gluingRadius C g - p.1.val, by
      constructor
      · linarith
      · change gluingRadius C g - p.1.val < gluingRadius C g + gluingDepth C g
        linarith [p.1.property.1]⟩), c.2) = c := by
    apply Prod.ext
    · apply Prod.ext
      · exact Circle.exp_arg a
      · apply Subtype.ext
        change gluingRadius C g - (gluingRadius C g - R.val) = R.val
        ring
    · rfl
  have hleft := P.outgoingTangentCollarNativeUnit_local_apply k θ p hs.le c.2
  rw [hpol] at hleft
  rw [hleft]
  let qi : P.ComponentInteriorTangentCarrier i :=
    ⟨(P.outgoingTangentCollarPolarHomeomorph i c).val.val, hi⟩
  let D := P.componentInteriorBallChartAt i ⟨(X i).tangentFrameBase qi.val, qi.property⟩
  let qlocal := P.componentInteriorTangentLocal i qi
  let T := (X i).tangentBallHomeomorph D.center
    (show 2 * D.radius < (X i).systole by linarith [D.radius_small, D.radius_pos])
  let w := T.symm qlocal
  have hw : (Quotient.mk _ (⟨w.1.val, w.2⟩ : HalfPlaneTangentFrame) :
      (X i).TangentFrameCarrier) = qi.val :=
    congrArg Subtype.val (T.apply_symm_apply qlocal)
  rw [P.nativeComponentInteriorUnitTangentHomeomorph_apply]
  change _ = (P.interiorBallNativeUnitHomeomorph i D.center D.radius D.radius_pos
    D.radius_small D.interior D.open_embedding w).val
  apply P.outgoingNativeUnitTangentTotal_eq_interiorBall k θ p hs D w.1 c.2 w.2
  have hpc := congrArg (fun d => (P.outgoingTangentCollarPolarHomeomorph i d).val.val) hpol
  exact hpc.trans hw.symm

end

end SystolicGrowth.ExerciseGluingPreparation

#print axioms SystolicGrowth.ExerciseGluingPreparation.incomingTangentCollarNativeUnit_eq_componentInterior
#print axioms SystolicGrowth.ExerciseGluingPreparation.outgoingTangentCollarNativeUnit_eq_componentInterior
