module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.FermiDiskPositiveWinding
public import Geometry.SurfaceEmbeddedDiskExterior
public import Geometry.DirichletPuncturePolarLoop

@[expose] public section

/-!
# Boundary comparison in the original punctured surface

The coordinate homotopies are projected through the actual embedded chart.
Injectivity of that chart keeps every projected point away from its original
center. No whole-plane homotopy is projected through the quotient.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane ContinuousMap unitInterval MatrixGroups

namespace SystolicGrowth

noncomputable section

/-- The literal coordinate circle in the punctured closed unit disk. -/
def puncturedClosedUnitDiskCircle (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    C(Circle, convexPuncturedDomain (closedBall (0 : ℂ) 1)) :=
  convexPuncturedCircleInclusion (closedBall (0 : ℂ) 1) s hs
    (fun θ => by
      simpa only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs, Circle.norm_coe, mul_one] using hs1)

/-- Actual positive-radius interpolation from one coordinate circle to another. -/
def puncturedClosedUnitDiskCircleRadiusHomotopy
    (s₀ s₁ : ℝ) (h₀ : 0 < s₀) (h₁ : 0 < s₁) (h₀1 : s₀ ≤ 1) (h₁1 : s₁ ≤ 1) :
    (puncturedClosedUnitDiskCircle s₀ h₀ h₀1).Homotopy
      (puncturedClosedUnitDiskCircle s₁ h₁ h₁1) := by
  let radius : I → ℝ := fun t => (1 - (t : ℝ)) * s₀ + (t : ℝ) * s₁
  have hr : ∀ t : I, 0 < radius t := by
    intro t
    by_cases ht : (t : ℝ) = 1
    · simpa [radius, ht] using h₁
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne t.2.2 ht)) h₀)
        (mul_nonneg t.2.1 h₁.le)
  have hr1 : ∀ t : I, radius t ≤ 1 := by
    intro t
    calc
      radius t ≤ (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h₀1 (sub_nonneg.mpr t.2.2))
          (mul_le_mul_of_nonneg_left h₁1 t.2.1)
      _ = 1 := by ring
  have hmem : ∀ p : I × Circle,
      radius p.1 • (p.2 : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    intro p
    simpa only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr p.1), Circle.norm_coe, mul_one] using hr1 p.1
  have hne : ∀ p : I × Circle, radius p.1 • (p.2 : ℂ) ≠ 0 := by
    intro p
    exact smul_ne_zero (hr p.1).ne' (norm_ne_zero_iff.mp (by simp [Circle.norm_coe]))
  refine
    { toContinuousMap :=
        { toFun p := ⟨radius p.1 • (p.2 : ℂ), hmem p, hne p⟩
          continuous_toFun := ?_ }
      map_zero_left := ?_
      map_one_left := ?_ }
  · have hrad : Continuous (fun p : I × Circle => radius p.1) := by
      dsimp [radius]
      fun_prop
    have hθ : Continuous (fun p : I × Circle => (p.2 : ℂ)) :=
      (continuous_subtype_val : Continuous (fun θ : Circle => (θ : ℂ))).comp continuous_snd
    exact (hrad.smul hθ).subtype_mk _
  · intro θ
    apply Subtype.ext
    simp [radius, puncturedClosedUnitDiskCircle, convexPuncturedCircleInclusion]
  · intro θ
    apply Subtype.ext
    simp [radius, puncturedClosedUnitDiskCircle, convexPuncturedCircleInclusion]

/-- The literal inclusion from the open punctured coordinate disk into the
closed punctured coordinate disk. -/
def puncturedOpenUnitDiskToClosed :
    C(convexPuncturedDomain (ball (0 : ℂ) 1),
      convexPuncturedDomain (closedBall (0 : ℂ) 1)) where
  toFun z := ⟨z.1, ball_subset_closedBall z.2.1, z.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}

/-- Project the actual chart coordinates into the original center-punctured
surface. Chart injectivity, not a plane-puncture assertion, removes the center. -/
def embeddedFermiPuncturedCoordinateMap
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    C(convexPuncturedDomain (closedBall (0 : ℂ) 1),
      X.CenterPuncturedCarrier (γ • orientedFermiDiskPoint m a b 0)) := by
  let coord : convexPuncturedDomain (closedBall (0 : ℂ) 1) → U :=
    fun z => ⟨z.1, hball z.2.1⟩
  have hc : Continuous coord := continuous_subtype_val.subtype_mk _
  have hnot : ∀ z : convexPuncturedDomain (closedBall (0 : ℂ) 1),
      f (coord z) ≠ (Quotient.mk'' (γ • orientedFermiDiskPoint m a b 0) : X.Carrier) := by
    intro z heq
    have hzero := hformula (embeddedCoordinatePunctureOrigin hball)
    have hval : f (coord z) = f (embeddedCoordinatePunctureOrigin hball) :=
      heq.trans hzero.symm
    exact z.2.2 (congrArg Subtype.val (hf.injective hval))
  exact ⟨fun z => ⟨f (coord z), hnot z⟩, (f.continuous.comp hc).subtype_mk hnot⟩

/-- The actual unit coordinate boundary viewed in the original punctured
surface, retaining the coordinate parameter exactly. -/
def embeddedFermiDiskBoundaryInPuncture
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    C(Circle, X.CenterPuncturedCarrier (γ • orientedFermiDiskPoint m a b 0)) :=
  (embeddedFermiPuncturedCoordinateMap hball f hf γ m a b hformula).comp
    (puncturedClosedUnitDiskCircle 1 one_pos le_rfl)

/-- The literal actual quotient point on that unchanged unit boundary. -/
@[simp]
theorem embeddedFermiDiskBoundaryInPuncture_val
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (θ : Circle) :
    (embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula θ).1 =
      f ⟨(θ : ℂ), hball (by simpa using (Circle.norm_coe θ).le)⟩ := by
  change f ⟨1 • (θ : ℂ), _⟩ = _
  simp

#print axioms embeddedFermiPuncturedCoordinateMap
#print axioms puncturedClosedUnitDiskCircleRadiusHomotopy

/-- Both actual orientation-preserving phases in the chart-to-polar comparison. -/
def fermiSLPolarAngleMap (γ : SL(2, ℝ)) (o : ℍ) : C(Circle, Circle) where
  toFun θ := gluingPolarSLPhase γ o * fermiPositivePolarAngle θ
  continuous_toFun := continuous_const.mul fermiPositivePolarAngle_continuous

/-- The full phase map commutes with positive circle multiplication. -/
theorem fermiSLPolarAngleMap_mul (γ : SL(2, ℝ)) (o : ℍ) (θ φ : Circle) :
    fermiSLPolarAngleMap γ o (θ * φ) = fermiSLPolarAngleMap γ o θ * φ := by
  apply Circle.ext
  change (gluingPolarSLPhase γ o : ℂ) * (-Complex.I * ((θ : ℂ) * (φ : ℂ))) =
    ((gluingPolarSLPhase γ o : ℂ) * (-Complex.I * (θ : ℂ))) * (φ : ℂ)
  ring

/-- The two actual unit phases preserve the literal positive one-turn path. -/
theorem circleOneTurnLoop_map_fermiSLPolarAngleMap
    (γ : SL(2, ℝ)) (o : ℍ) (θ : Circle) :
    (circleOneTurnLoop θ).map (fermiSLPolarAngleMap γ o).continuous =
      circleOneTurnLoop (fermiSLPolarAngleMap γ o θ) := by
  apply Path.ext
  funext t
  simp only [Path.map_coe, Function.comp_apply, circleOneTurnLoop_apply,
    Circle.exp_add, Circle.exp_arg]
  exact fermiSLPolarAngleMap_mul γ o θ _

/-- The comparison map's endpoint is the original positive polar circle,
with its exact two unit phases and no parameter reversal. -/
theorem embeddedFermiPuncturedCoordinateMap_positivePolar
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (ρ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < 1) :
    (embeddedFermiPuncturedCoordinateMap hball f hf γ m a b hformula).comp
        (puncturedOpenUnitDiskToClosed.comp
          (fermiPositivePolarCoordinateMap m a b ha hb ρ 1 hρ hq)) =
      (X.dirichletPuncturePolarCircle (γ • orientedFermiDiskPoint m a b 0) ρ hρ hsys).comp
        (fermiSLPolarAngleMap γ (orientedFermiDiskPoint m a b 0)) := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  change f ⟨fermiPositivePolarCoordinate m a b ha hb ρ θ, _⟩ =
    (Quotient.mk'' (gluingPolarPoint (γ • orientedFermiDiskPoint m a b 0)
      (gluingPolarSLPhase γ (orientedFermiDiskPoint m a b 0) *
        fermiPositivePolarAngle θ) ρ) : X.Carrier)
  rw [hformula, orientedFermiDiskPoint_positivePolarCoordinate, gluingPolarPoint_smul]
  rfl

/-- A homotopy of the unchanged unit chart boundary to the original positive
polar circle, entirely through the actual embedded punctured surface. -/
def embeddedFermiDiskBoundaryPolarHomotopy
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (ρ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < 1) :
    (embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula).Homotopy
      ((X.dirichletPuncturePolarCircle (γ • orientedFermiDiskPoint m a b 0) ρ hρ hsys).comp
        (fermiSLPolarAngleMap γ (orientedFermiDiskPoint m a b 0))) := by
  let F := embeddedFermiPuncturedCoordinateMap hball f hf γ m a b hformula
  let H₁ := puncturedClosedUnitDiskCircleRadiusHomotopy 1 (1 / 2)
    one_pos (by norm_num) le_rfl (by norm_num)
  let H₂ := fermiPositivePolarCoordinateHomotopy m a b ha hb (1 / 2) ρ 1
    (by norm_num) (by norm_num) hρ hq
  let H₃ := (ContinuousMap.Homotopy.refl puncturedOpenUnitDiskToClosed).comp H₂
  have hstart : puncturedOpenUnitDiskToClosed.comp
      (convexPuncturedCircleInclusion (ball (0 : ℂ) 1) (1 / 2) (by norm_num)
        (fun θ => by simpa [norm_smul, Real.norm_eq_abs, Circle.norm_coe]
          using (show (1 / 2 : ℝ) < 1 by norm_num))) =
      puncturedClosedUnitDiskCircle (1 / 2) (by norm_num) (by norm_num) := by
    apply ContinuousMap.ext
    intro θ
    apply Subtype.ext
    rfl
  let H₄ := H₃.cast hstart rfl
  let H₅ := H₁.trans H₄
  exact ((ContinuousMap.Homotopy.refl F).comp H₅).cast rfl
    (embeddedFermiPuncturedCoordinateMap_positivePolar hball f hf γ m a b ha hb
      hformula ρ hρ hsys hq)

#print axioms embeddedFermiDiskBoundaryPolarHomotopy

/-- Transport of the untouched coordinate boundary one-turn class to the
original positive polar class by the actual projected comparison track. -/
theorem embeddedFermiDiskBoundaryPolarHomotopy_fundamentalGroup
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (ρ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < 1)
    (θ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((embeddedFermiDiskBoundaryPolarHomotopy hball f hf γ m a b ha hb
          hformula ρ hρ hsys hq).evalAt θ)
      ⟦(circleOneTurnLoop θ).map
        (embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula).continuous⟧ =
      ⟦X.dirichletPuncturePolarOneTurn (γ • orientedFermiDiskPoint m a b 0)
        ρ hρ hsys (fermiSLPolarAngleMap γ (orientedFermiDiskPoint m a b 0) θ)⟧ := by
  let H := embeddedFermiDiskBoundaryPolarHomotopy hball f hf γ m a b ha hb
    hformula ρ hρ hsys hq
  let B := embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula
  let P := X.dirichletPuncturePolarCircle (γ • orientedFermiDiskPoint m a b 0) ρ hρ hsys
  let A := fermiSLPolarAngleMap γ (orientedFermiDiskPoint m a b 0)
  let p := (circleOneTurnLoop θ).map B.continuous
  let q := (circleOneTurnLoop θ).map (P.comp A).continuous
  let τ := H.evalAt θ
  have hhom : (p.trans τ).Homotopic (τ.trans q) :=
    Path.Homotopic.map_trans_evalAt H (circleOneTurnLoop θ)
  have heq := Path.Homotopic.Quotient.eq.mpr hhom
  have hloop : q = X.dirichletPuncturePolarOneTurn
      (γ • orientedFermiDiskPoint m a b 0) ρ hρ hsys (A θ) := by
    change (circleOneTurnLoop θ).map (P.continuous.comp A.continuous) = _
    rw [← Path.map_map (circleOneTurnLoop θ) A.continuous P.continuous,
      circleOneTurnLoop_map_fermiSLPolarAngleMap]
    rfl
  change Path.Homotopic.Quotient.mk (τ.symm.trans (p.trans τ)) = _
  rw [Path.Homotopic.Quotient.mk_trans, heq,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans, hloop]
  rfl

/-- Choose the actual fitting polar radius below a pre-existing systolic
cutoff, so none of the homotopy's domain or cutoff conditions is assumed. -/
theorem exists_embeddedFermiDiskBoundaryPolarHomotopy
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (r : ℝ) (hr : 0 < r) (hsysr : 2 * r < X.systole) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ r,
      ∃ _hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < 1,
        Nonempty ((embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula).Homotopy
          ((X.dirichletPuncturePolarCircle (γ • orientedFermiDiskPoint m a b 0)
            ρ hρ (by linarith)).comp
            (fermiSLPolarAngleMap γ (orientedFermiDiskPoint m a b 0)))) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    exists_small_fermiPositivePolarCoordinate_norm_lt m a b ha hb zero_lt_one
  let ρ := min ε r / 2
  have hρ : 0 < ρ := half_pos (lt_min hε hr)
  have hρr : ρ ≤ r := by
    dsimp [ρ]
    have h := min_le_right ε r
    linarith
  have hρε : ρ < ε := by
    dsimp [ρ]
    have h := min_le_left ε r
    linarith
  have hq : ∀ θ : Circle, ‖fermiPositivePolarCoordinate m a b ha hb ρ θ‖ < 1 :=
    hsmall ρ hρ.le hρε
  exact ⟨ρ, hρ, hρr, hq,
    ⟨embeddedFermiDiskBoundaryPolarHomotopy hball f hf γ m a b ha hb
      hformula ρ hρ (by linarith) hq⟩⟩

#print axioms embeddedFermiDiskBoundaryPolarHomotopy_fundamentalGroup
#print axioms exists_embeddedFermiDiskBoundaryPolarHomotopy

/-- The same untouched coordinate boundary as a map into its actual exterior.
Its quotient values are definitionally those of the punctured-surface map. -/
def embeddedFermiDiskBoundaryExteriorCircle
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    C(Circle, embeddedCoordinatePunctureExterior f) := by
  let B := embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula
  have hnot : ∀ θ : Circle, (B θ).1 ∉ embeddedCoordinatePunctureDisk f := by
    intro θ
    change (embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula θ).1 ∉ _
    rw [embeddedFermiDiskBoundaryInPuncture_val]
    exact (embeddedSurfaceDiskBoundaryCircle hball f hf θ).2
  exact ⟨fun θ => ⟨(B θ).1, hnot θ⟩,
    (continuous_subtype_val.comp B.continuous).subtype_mk hnot⟩

/-- The literal exterior inclusion induces its actual based group equivalence
at the unchanged coordinate boundary basepoint. -/
def embeddedFermiDiskExteriorBoundaryFundamentalGroupEquiv
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (θ : Circle) :
    FundamentalGroup (embeddedCoordinatePunctureExterior f)
        (embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula θ) ≃*
      FundamentalGroup (X.CenterPuncturedCarrier (γ • orientedFermiDiskPoint m a b 0))
        (embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula θ) :=
  embeddedSurfaceDiskExteriorFundamentalGroupEquiv hball f hf
    (γ • orientedFermiDiskPoint m a b 0)
    (hformula (embeddedCoordinatePunctureOrigin hball))
    (embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula θ)

/-- No extra conjugator occurs in the exterior inclusion: the literal
coordinate one-turn loop is mapped to its literal punctured-surface loop. -/
theorem embeddedFermiDiskExteriorBoundaryFundamentalGroupEquiv_oneTurn
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (θ : Circle) :
    embeddedFermiDiskExteriorBoundaryFundamentalGroupEquiv hball f hf γ m a b hformula θ
      ⟦(circleOneTurnLoop θ).map
        (embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (embeddedFermiDiskBoundaryInPuncture hball f hf γ m a b hformula).continuous⟧ := by
  rfl

#print axioms embeddedFermiDiskExteriorBoundaryFundamentalGroupEquiv_oneTurn

/-- This is literally the existing exterior boundary map, not a replacement
circle with merely the same image. -/
theorem embeddedFermiDiskBoundaryExteriorCircle_eq
    (hball : closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula =
      embeddedSurfaceDiskBoundaryCircle hball f hf := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  exact embeddedFermiDiskBoundaryInPuncture_val hball f hf γ m a b hformula θ

end

end SystolicGrowth
