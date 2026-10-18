module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.PuncturedSideConnectorIndependence

@[expose] public section

/-!
# Positive Fermi generators from actual side membership

If the literal Fermi positive circle and a literal circle about the same
puncture lie in one convex side, straight interpolation compares their
positive turns without choosing an auxiliary norm cutoff.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

/-- The actual translated Fermi positive circle as a map into the punctured
convex side. Membership is supplied directly, with no auxiliary ball. -/
def convexSideFermiPositivePolarCoordinateMap (B : Set ℂ) (c : ℂ)
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ρ : ℝ) (hρ : 0 < ρ)
    (hmem : ∀ θ : Circle,
      c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ ∈ B) :
    C(Circle, puncturedBaseAt B c) where
  toFun θ := ⟨c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ,
    ⟨hmem θ, by
      intro h
      have h' : c + fermiPositivePolarCoordinate
          (m + a * c.im) a b ha hb ρ θ = c + 0 := by simpa using h
      have hz : fermiPositivePolarCoordinate
          (m + a * c.im) a b ha hb ρ θ = 0 := add_left_cancel h'
      exact fermiPositivePolarCoordinate_ne_zero (m + a * c.im) a b ha hb hρ θ hz⟩⟩
  continuous_toFun :=
    (continuous_const.add (fermiPositivePolarCoordinate_continuous
      (m + a * c.im) a b ha hb ρ)).subtype_mk _

/-- Convex interpolation between a literal positive circle in `B` and the
actual Fermi positive circle stays in the punctured side. -/
def convexSideFermiPositivePolarCoordinateHomotopy
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ℓ ρ : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hmem : ∀ θ : Circle,
      c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ ∈ B) :
    (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).Homotopy
      (convexSideFermiPositivePolarCoordinateMap B c m a b ha hb ρ hρ hmem) := by
  let Ω := puncturedBaseTranslated B c
  have hΩconv : Convex ℝ Ω := puncturedBaseTranslated_convex hB c
  have hΩcircle : ∀ θ : Circle, ℓ • (θ : ℂ) ∈ Ω := by
    intro θ
    change (ℓ • (θ : ℂ)) + c ∈ B
    rw [add_comm]
    exact hcircle θ
  have hΩfermi : ∀ θ : Circle,
      fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ ∈ Ω := by
    intro θ
    change fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ + c ∈ B
    simpa [add_comm] using hmem θ
  have hpoint : ∀ p : I × Circle,
      c + fermiPositiveCoordinateInterpolation (m + a * c.im) a b ha hb ℓ ρ
        p.1 p.2 ∈ B := by
    intro p
    have hinterp : fermiPositiveCoordinateInterpolation
        (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 ∈ Ω := by
      simpa [fermiPositiveCoordinateInterpolation] using
        (hΩconv (hΩcircle p.2) (hΩfermi p.2)
          (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring))
    change fermiPositiveCoordinateInterpolation
      (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 + c ∈ B at hinterp
    simpa [add_comm] using hinterp
  have hne : ∀ p : I × Circle,
      fermiPositiveCoordinateInterpolation (m + a * c.im) a b ha hb ℓ ρ
        p.1 p.2 ≠ 0 := by
    intro p
    exact fermiPositiveCoordinateInterpolation_ne_zero
      (m + a * c.im) a b ha hb hℓ hρ p.1 p.2
  refine
    { toContinuousMap :=
        { toFun p := ⟨c + fermiPositiveCoordinateInterpolation
            (m + a * c.im) a b ha hb ℓ ρ p.1 p.2,
            ⟨hpoint p, ?_⟩⟩,
          continuous_toFun := ?_ }
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro h
    have h' : c + fermiPositiveCoordinateInterpolation
        (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 = c + 0 := by simpa using h
    exact hne p (add_left_cancel h')
  · have ht : Continuous (fun p : I × Circle => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hθ : Continuous (fun p : I × Circle => ℓ • (p.2 : ℂ)) :=
      (continuous_const : Continuous (fun _ : I × Circle => ℓ)).smul
        (continuous_subtype_val.comp continuous_snd)
    have hq' := (fermiPositivePolarCoordinate_continuous
      (m + a * c.im) a b ha hb ρ).comp
        (continuous_snd : Continuous (fun p : I × Circle => p.2))
    have hinterp : Continuous (fun p : I × Circle =>
        fermiPositiveCoordinateInterpolation
          (m + a * c.im) a b ha hb ℓ ρ p.1 p.2) := by
      change Continuous (fun p : I × Circle =>
        ((1 - (p.1 : ℝ)) • (ℓ • (p.2 : ℂ)) +
          (p.1 : ℝ) • fermiPositivePolarCoordinate
            (m + a * c.im) a b ha hb ρ p.2))
      exact (((continuous_const.sub ht).smul hθ).add (ht.smul hq'))
    exact (continuous_const.add hinterp).subtype_mk _
  · intro θ
    apply Subtype.ext
    simp [fermiPositiveCoordinateInterpolation, puncturedBaseCircleInclusion,
      convexPuncturedCircleInclusion, puncturedBaseTranslationHomeomorph, add_comm]
  · intro θ
    apply Subtype.ext
    simp [fermiPositiveCoordinateInterpolation,
      convexSideFermiPositivePolarCoordinateMap]

/-- The convex homotopy transports a positive turn at every Circle angle. -/
theorem convexSideFermiPositivePolarCoordinateHomotopy_oneTurn
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ℓ ρ : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hmem : ∀ θ : Circle,
      c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ ∈ B)
    (θ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((convexSideFermiPositivePolarCoordinateHomotopy
          B c hB m a b ha hb ℓ ρ hℓ hρ hcircle hmem).evalAt θ)
      ⟦(circleOneTurnLoop θ).map
        (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (convexSideFermiPositivePolarCoordinateMap B c m a b ha hb ρ hρ hmem).continuous⟧ := by
  let H := convexSideFermiPositivePolarCoordinateHomotopy
    B c hB m a b ha hb ℓ ρ hℓ hρ hcircle hmem
  let p := (circleOneTurnLoop θ).map
    (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).continuous
  let q := (circleOneTurnLoop θ).map
    (convexSideFermiPositivePolarCoordinateMap B c m a b ha hb ρ hρ hmem).continuous
  let τ := H.evalAt θ
  have hhom : (p.trans τ).Homotopic (τ.trans q) :=
    Path.Homotopic.map_trans_evalAt H (circleOneTurnLoop θ)
  have heq := Path.Homotopic.Quotient.eq.mpr hhom
  change Path.Homotopic.Quotient.mk (τ.symm.trans (p.trans τ)) =
    Path.Homotopic.Quotient.mk q
  rw [Path.Homotopic.Quotient.mk_trans, heq,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

private theorem mapped_circleOneTurn_conjugate_eq_of_map
    {Y : Type*} [TopologicalSpace Y] (F : C(Circle, Y)) (θ φ : Circle) :
    Path.Homotopic.Quotient.mk
      (((Circle.path θ φ).map F.continuous).trans
        (((circleOneTurnLoop φ).map F.continuous).trans
          ((Circle.path θ φ).map F.continuous).symm)) =
      Path.Homotopic.Quotient.mk ((circleOneTurnLoop θ).map F.continuous) := by
  let cpath := Circle.path θ φ
  let spath := cpath.map F.continuous
  let Lθ := (circleOneTurnLoop θ).map F.continuous
  let Lφ := (circleOneTurnLoop φ).map F.continuous
  have hreb : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (cpath.trans ((circleOneTurnLoop φ).trans cpath.symm))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (circleOneTurnLoop θ)) := by
    apply (FundamentalGroup.fundamentalGroupMulEquivOfPath cpath).injective
    change FundamentalGroup.fundamentalGroupMulEquivOfPath cpath
      ⟦cpath.trans ((circleOneTurnLoop φ).trans cpath.symm)⟧ =
        FundamentalGroup.fundamentalGroupMulEquivOfPath cpath
          ⟦circleOneTurnLoop θ⟧
    rw [fundamentalGroupMulEquivOfPath_conjugate_apply,
      circleOneTurnLoop_rebase_circlePath]
  have hmap : ((cpath.trans ((circleOneTurnLoop φ).trans cpath.symm)).map
      F.continuous).Homotopic ((circleOneTurnLoop θ).map F.continuous) := by
    exact Path.Homotopic.map (Path.Homotopic.Quotient.eq.mp hreb) F
  have hpath : (cpath.trans ((circleOneTurnLoop φ).trans cpath.symm)).map
      F.continuous = spath.trans (Lφ.trans spath.symm) := by
    simp [spath, Lφ, Path.map_trans, Path.map_symm]
  change Path.Homotopic.Quotient.mk (spath.trans (Lφ.trans spath.symm)) =
    Path.Homotopic.Quotient.mk Lθ
  rw [← hpath]
  exact Path.Homotopic.Quotient.eq.mpr hmap

/-- The literal Fermi positive turn represents the positive circle generator
after any actual path from the chosen basepoint to any angle on that circle.
Only actual endpoint membership in the convex side is needed. -/
theorem convexSideFermiPositivePolarCoordinateBasedFreeGenerator_of_connector
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (ℓ ρ : ℝ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmem : ∀ θ : Circle,
      c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ ∈ B)
    (z : puncturedBaseAt B c) (φ : Circle)
    (p : Path z (convexSideFermiPositivePolarCoordinateMap
      B c m a b ha hb ρ hρ hmem φ)) :
    let θ := puncturedBaseCircleRetraction B c z
    let E := (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z).trans
      (circleFundamentalGroupFreeEquiv θ)
    let F := convexSideFermiPositivePolarCoordinateMap B c m a b ha hb ρ hρ hmem
    E ⟦p.trans (((circleOneTurnLoop φ).map F.continuous).trans p.symm)⟧ =
      FreeGroup.of () := by
  let θ := puncturedBaseCircleRetraction B c z
  let E := (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z).trans
    (circleFundamentalGroupFreeEquiv θ)
  let F := convexSideFermiPositivePolarCoordinateMap B c m a b ha hb ρ hρ hmem
  let inc := puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle
  let H := convexSideFermiPositivePolarCoordinateHomotopy
    B c hB m a b ha hb ℓ ρ hℓ hρ hcircle hmem
  let t := puncturedBaseCircleActualTrack B c ℓ hB hℓ hcircle z
  let τ := H.evalAt θ
  let p₀ := t.trans τ
  let L₀ := (circleOneTurnLoop θ).map F.continuous
  let Lφ := (circleOneTurnLoop φ).map F.continuous
  let s := (Circle.path θ φ).map F.continuous
  let q := p₀.trans s
  have hbase : E ⟦p₀.trans (L₀.trans p₀.symm)⟧ = FreeGroup.of () := by
    let L := puncturedBaseCircleBasedPositiveLoop B c ℓ hB hℓ hcircle z
    let γ := (circleOneTurnLoop θ).map inc.continuous
    have htrack : FundamentalGroup.fundamentalGroupMulEquivOfPath t ⟦L⟧ = ⟦γ⟧ := by
      dsimp [L, γ, t, θ, inc]
      exact fundamentalGroupMulEquivOfPath_conjugate_apply _ _
    have hH : FundamentalGroup.fundamentalGroupMulEquivOfPath τ ⟦γ⟧ = ⟦L₀⟧ := by
      dsimp [τ, γ, F, H, θ, inc]
      exact convexSideFermiPositivePolarCoordinateHomotopy_oneTurn
        B c hB m a b ha hb ℓ ρ hℓ hρ hcircle hmem θ
    have htransport : FundamentalGroup.fundamentalGroupMulEquivOfPath p₀ ⟦L⟧ = ⟦L₀⟧ := by
      change FundamentalGroup.fundamentalGroupMulEquivOfPath (t.trans τ) ⟦L⟧ = ⟦L₀⟧
      rw [fundamentalGroupMulEquivOfPath_trans_apply, htrack]
      exact hH
    have hbased : FundamentalGroup.fundamentalGroupMulEquivOfPath p₀
        ⟦p₀.trans (L₀.trans p₀.symm)⟧ = ⟦L₀⟧ := by
      exact fundamentalGroupMulEquivOfPath_conjugate_apply p₀ L₀
    have hloop : ⟦p₀.trans (L₀.trans p₀.symm)⟧ = ⟦L⟧ :=
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p₀).injective (by
        rw [hbased, htransport])
    have hpositive :
        puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z ⟦L⟧ =
          ⟦circleOneTurnLoop θ⟧ :=
      puncturedBaseCircleFundamentalGroupEquiv_actualPositiveLoop
        B c ℓ hB hℓ hcircle z
    change circleFundamentalGroupFreeEquiv θ
      (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z
        ⟦p₀.trans (L₀.trans p₀.symm)⟧) = _
    rw [hloop, hpositive]
    exact circleFundamentalGroupFreeEquiv_oneTurn θ
  have hcircleLoop : Path.Homotopic.Quotient.mk (s.trans (Lφ.trans s.symm)) =
      Path.Homotopic.Quotient.mk L₀ := by
    dsimp [s, Lφ, L₀, F]
    exact mapped_circleOneTurn_conjugate_eq_of_map
      (convexSideFermiPositivePolarCoordinateMap B c m a b ha hb ρ hρ hmem)
      θ φ
  have hqPath : Path.Homotopic.Quotient.mk (q.trans (Lφ.trans q.symm)) =
      (Path.Homotopic.Quotient.mk p₀).trans
        ((Path.Homotopic.Quotient.mk (s.trans (Lφ.trans s.symm))).trans
          (Path.Homotopic.Quotient.mk p₀.symm)) := by
    dsimp [q]
    change Path.Homotopic.Quotient.mk
        ((p₀.trans s).trans (Lφ.trans (p₀.trans s).symm)) = _
    rw [Path.trans_symm]
    simp only [Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.trans_assoc
        (Path.Homotopic.Quotient.mk p₀)
        (Path.Homotopic.Quotient.mk s),
      ← Path.Homotopic.Quotient.trans_assoc
        (Path.Homotopic.Quotient.mk Lφ)
        (Path.Homotopic.Quotient.mk s.symm),
      ← Path.Homotopic.Quotient.trans_assoc
        (Path.Homotopic.Quotient.mk s)
        ((Path.Homotopic.Quotient.mk Lφ).trans
          (Path.Homotopic.Quotient.mk s.symm))]
    simp only [Path.Homotopic.Quotient.mk_symm]
  have hq : Path.Homotopic.Quotient.mk (q.trans (Lφ.trans q.symm)) =
      Path.Homotopic.Quotient.mk (p₀.trans (L₀.trans p₀.symm)) := by
    calc
      _ = (Path.Homotopic.Quotient.mk p₀).trans
          ((Path.Homotopic.Quotient.mk (s.trans (Lφ.trans s.symm))).trans
            (Path.Homotopic.Quotient.mk p₀.symm)) := hqPath
      _ = (Path.Homotopic.Quotient.mk p₀).trans
          ((Path.Homotopic.Quotient.mk L₀).trans
            (Path.Homotopic.Quotient.mk p₀.symm)) := by rw [hcircleLoop]
      _ = Path.Homotopic.Quotient.mk (p₀.trans (L₀.trans p₀.symm)) := by rfl
  have hcomm : ∀ x y : FundamentalGroup (puncturedBaseAt B c) z, x * y = y * x :=
    puncturedBaseFundamentalGroup_commutative B c ℓ hB hℓ hcircle z
  have hpq : ⟦p.trans (Lφ.trans p.symm)⟧ = ⟦q.trans (Lφ.trans q.symm)⟧ :=
    pathConjugateLoop_eq_of_commutative hcomm p q Lφ
  have hpqGroup : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (p.trans (Lφ.trans p.symm))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (q.trans (Lφ.trans q.symm))) :=
    congrArg FundamentalGroup.fromPath hpq
  have hqGroup : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (q.trans (Lφ.trans q.symm))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p₀.trans (L₀.trans p₀.symm))) :=
    congrArg FundamentalGroup.fromPath hq
  change E (FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (p.trans (Lφ.trans p.symm)))) = FreeGroup.of ()
  rw [hpqGroup, hqGroup]
  exact hbase

#print axioms convexSideFermiPositivePolarCoordinateHomotopy
#print axioms convexSideFermiPositivePolarCoordinateHomotopy_oneTurn
#print axioms convexSideFermiPositivePolarCoordinateBasedFreeGenerator_of_connector

end

end SystolicGrowth
