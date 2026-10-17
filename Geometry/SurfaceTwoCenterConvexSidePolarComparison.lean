module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.CircleOneTurnRebase
public import Geometry.SurfaceTwoCenterLocalPolarComparison
public import Geometry.TwoPuncturedDiskSideCircle

@[expose] public section

/-!
# Uniform polar comparison inside actual convex two-puncture sides

Choose a coordinate radius using the uniform Fermi-smallness theorem, then
intersect it with any gluing or connector cutoff. Convex interpolation only
needs the two actual endpoint circles in the side; the selected side-circle
radius therefore need not be smaller than the auxiliary ball radius.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups unitInterval

namespace SystolicGrowth

noncomputable section

/-- The straight Fermi interpolation is a homotopy in an actual convex side
whenever its two endpoint circles lie in that side. This allows the literal
side-generator radius to be kept unchanged. -/
def translatedFermiPositivePolarCoordinateHomotopy_convex
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ)
    (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).Homotopy
      (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq) := by
  let Ω := puncturedBaseTranslated B c
  have hΩconv : Convex ℝ Ω := puncturedBaseTranslated_convex hB c
  have hstart : ∀ θ : Circle, ℓ • (θ : ℂ) ∈ Ω := by
    intro θ
    change ℓ • (θ : ℂ) + c ∈ B
    rw [add_comm]
    exact hcircle θ
  have hend : ∀ θ : Circle,
      fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ ∈ Ω := by
    intro θ
    change fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ + c ∈ B
    rw [add_comm]
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : c + fermiPositivePolarCoordinate
        (m + a * c.im) a b ha hb ρ θ - c =
        fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ := by abel
    rw [heq]
    exact hq θ
  have hmem : ∀ p : I × Circle,
      c + fermiPositiveCoordinateInterpolation (m + a * c.im) a b ha hb ℓ ρ
        p.1 p.2 ∈ B := by
    intro p
    have hinterp : fermiPositiveCoordinateInterpolation
        (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 ∈ Ω := by
      simpa [fermiPositiveCoordinateInterpolation] using
        (hΩconv (hstart p.2) (hend p.2)
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
            hmem p, ?_⟩
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
    simp [fermiPositiveCoordinateInterpolation, translatedFermiPositivePolarCoordinateMap]

/-- The based positive one-turn loop is transported literally through the
coordinate-side homotopy, before projecting to the surface. -/
theorem translatedFermiPositivePolarCoordinateHomotopy_convex_oneTurn
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ)
    (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((translatedFermiPositivePolarCoordinateHomotopy_convex B c hB m a b
          ha hb ℓ ρ δ hℓ hρ hcircle hball hq).evalAt θ)
      ⟦(circleOneTurnLoop θ).map
        (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq).continuous⟧ := by
  let H := translatedFermiPositivePolarCoordinateHomotopy_convex B c hB m a b
    ha hb ℓ ρ δ hℓ hρ hcircle hball hq
  let p := (circleOneTurnLoop θ).map
    (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).continuous
  let q := (circleOneTurnLoop θ).map
    (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq).continuous
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

/-- Based fundamental-group transport composes in the same order as paths. -/
theorem fundamentalGroupMulEquivOfPath_apply_generic
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (p : Path x y) (γ : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p ⟦γ⟧ =
      ⟦p.symm.trans (γ.trans p)⟧ := by
  rfl

/-- Based fundamental-group transport composes in the same order as paths. -/
theorem fundamentalGroupMulEquivOfPath_trans_apply
    {Y : Type*} [TopologicalSpace Y] {x y z : Y}
    (p : Path x y) (q : Path y z) (γ : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.trans q) ⟦γ⟧ =
      FundamentalGroup.fundamentalGroupMulEquivOfPath q
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p ⟦γ⟧) := by
  rw [fundamentalGroupMulEquivOfPath_apply_generic,
    fundamentalGroupMulEquivOfPath_apply_generic,
    fundamentalGroupMulEquivOfPath_apply_generic]
  change Path.Homotopic.Quotient.mk
      ((p.trans q).symm.trans (γ.trans (p.trans q))) =
    Path.Homotopic.Quotient.mk
      (q.symm.trans ((p.symm.trans (γ.trans p)).trans q))
  rw [Path.trans_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  simp only [Path.Homotopic.Quotient.trans_assoc]

/-- Transport sends a loop conjugated along its own path back to the original
loop at the path endpoint. -/
theorem fundamentalGroupMulEquivOfPath_conjugate_apply
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (p : Path x y) (γ : Path y y) :
  FundamentalGroup.fundamentalGroupMulEquivOfPath p
      ⟦p.trans (γ.trans p.symm)⟧ = ⟦γ⟧ := by
  rw [fundamentalGroupMulEquivOfPath_apply_generic]
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc]
  simp only [Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]
  rw [← Path.Homotopic.Quotient.trans_assoc]
  simp only [Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- At any actual punctured-side point, the Fermi positive loop, conjugated
by the literal radial track and the homotopy evaluation path, is the positive
generator of the side's actual free-unit marking. -/
theorem translatedFermiPositivePolarCoordinateBasedFreeGenerator
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (ℓ ρ δ : ℝ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (z : puncturedBaseAt B c) :
    let θ := puncturedBaseCircleRetraction B c z
    let H := translatedFermiPositivePolarCoordinateHomotopy_convex B c hB m a b
      ha hb ℓ ρ δ hℓ hρ hcircle hball hq
    let t := puncturedBaseCircleActualTrack B c ℓ hB hℓ hcircle z
    let p := t.trans (H.evalAt θ)
    let L := (circleOneTurnLoop θ).map
      (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq).continuous
    let based := p.trans (L.trans p.symm)
    ((puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z).trans
      (circleFundamentalGroupFreeEquiv θ)) ⟦based⟧ = FreeGroup.of () := by
  let θ := puncturedBaseCircleRetraction B c z
  let inc := puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle
  let F := translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq
  let H := translatedFermiPositivePolarCoordinateHomotopy_convex B c hB m a b
    ha hb ℓ ρ δ hℓ hρ hcircle hball hq
  let t := puncturedBaseCircleActualTrack B c ℓ hB hℓ hcircle z
  let τ := H.evalAt θ
  let p := t.trans τ
  let γ := (circleOneTurnLoop θ).map inc.continuous
  let Fγ := (circleOneTurnLoop θ).map F.continuous
  let L := puncturedBaseCircleBasedPositiveLoop B c ℓ hB hℓ hcircle z
  let based := p.trans (Fγ.trans p.symm)
  have htrack :
      FundamentalGroup.fundamentalGroupMulEquivOfPath t ⟦L⟧ = ⟦γ⟧ := by
    dsimp [L, γ, t, θ, inc]
    exact fundamentalGroupMulEquivOfPath_conjugate_apply _ _
  have hH :
      FundamentalGroup.fundamentalGroupMulEquivOfPath τ ⟦γ⟧ = ⟦Fγ⟧ := by
    dsimp [τ, γ, F, H, θ, inc]
    exact translatedFermiPositivePolarCoordinateHomotopy_convex_oneTurn
      B c hB m a b ha hb ℓ ρ δ hℓ hρ hcircle hball hq θ
  have htransport :
      FundamentalGroup.fundamentalGroupMulEquivOfPath p ⟦L⟧ = ⟦Fγ⟧ := by
    change FundamentalGroup.fundamentalGroupMulEquivOfPath (t.trans τ) ⟦L⟧ = ⟦Fγ⟧
    rw [fundamentalGroupMulEquivOfPath_trans_apply, htrack]
    exact hH
  have hbased :
      FundamentalGroup.fundamentalGroupMulEquivOfPath p ⟦based⟧ = ⟦Fγ⟧ := by
    change FundamentalGroup.fundamentalGroupMulEquivOfPath (t.trans τ)
      ⟦(t.trans τ).trans (Fγ.trans (t.trans τ).symm)⟧ = ⟦Fγ⟧
    exact fundamentalGroupMulEquivOfPath_conjugate_apply (t.trans τ) Fγ
  have hloop : ⟦based⟧ = ⟦L⟧ :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).injective (by
      rw [hbased, htransport])
  have hpositive :
      puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z ⟦L⟧ =
        ⟦circleOneTurnLoop θ⟧ := by
    exact puncturedBaseCircleFundamentalGroupEquiv_actualPositiveLoop
      B c ℓ hB hℓ hcircle z
  change circleFundamentalGroupFreeEquiv θ
      (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z ⟦based⟧) = _
  rw [hloop, hpositive]
  exact circleFundamentalGroupFreeEquiv_oneTurn θ

/-- Project the endpoint-convex Fermi interpolation through the literal
embedded chart, retaining both deleted surface centers. -/
def translatedFermiSideSurfaceHomotopy_convex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U)
    (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hB : Convex ℝ B) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
        (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).Homotopy
      (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
        hformula ρ δ hρ hball hq) :=
  (ContinuousMap.Homotopy.refl
      (translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula)).comp
    (translatedFermiPositivePolarCoordinateHomotopy_convex
      B c hB m a b ha hb ℓ ρ δ hℓ hρ hcircle hball hq)

/-- The actual based one-turn transport for the convex-endpoint interpolation
homotopy in the original twice-center-punctured surface. -/
theorem translatedFermiSideSurfaceHomotopy_convex_oneTurn
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U)
    (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hB : Convex ℝ B) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((translatedFermiSideSurfaceHomotopy_convex B c c₂ hBU hcB hc₂ hBother f hf
          γ m a b ha hb hformula hB ℓ ρ δ hℓ hρ hcircle hball hq).evalAt θ)
      ⟦(circleOneTurnLoop θ).map
        ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
          (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
          hformula ρ δ hρ hball hq).continuous⟧ := by
  let H := translatedFermiSideSurfaceHomotopy_convex B c c₂ hBU hcB hc₂ hBother f hf
    γ m a b ha hb hformula hB ℓ ρ δ hℓ hρ hcircle hball hq
  let p := (circleOneTurnLoop θ).map
    ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
      (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).continuous
  let q := (circleOneTurnLoop θ).map
    (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
      hformula ρ δ hρ hball hq).continuous
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

/-- Choose one radius threshold controlling every Fermi-polar circle in an
open convex side; for each positive smaller radius it yields the actual
twice-punctured-surface homotopy. The imported one-turn and literal-coordinate
formulae can then be applied with the returned `hball` and `hq`. -/
abbrev UniformTranslatedFermiSideSurfaceComparison
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hB : Convex ℝ B)
    (hcB : c ∈ B) (hBU : B ⊆ U) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B) : Prop :=
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∃ hball : Metric.ball c δ ⊆ B,
      ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ ε →
        ∃ hq : ∀ θ : Circle,
          ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ,
        ∃ H : ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
              hformula).comp
            (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).Homotopy
            (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
              hformula ρ δ hρ hball hq),
          ∀ θ : Circle,
            FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt θ)
              ⟦(circleOneTurnLoop θ).map
                ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
                  hformula).comp
                  (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).continuous⟧ =
              ⟦(circleOneTurnLoop θ).map
                (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
                  ha hb hformula ρ δ hρ hball hq).continuous⟧

theorem exists_uniform_translatedFermiSideSurfaceComparison
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBopen : IsOpen B) (hB : Convex ℝ B)
    (hcB : c ∈ B) (hBU : B ⊆ U) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B) :
    UniformTranslatedFermiSideSurfaceComparison B c c₂ hB hcB hBU hc₂ hBother
      f hf γ m a b ha hb hformula ℓ hℓ hcircle := by
  obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.mp hBopen c hcB
  let δ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hball : Metric.ball c δ ⊆ B := by
    intro z hz
    apply hηball
    have hz' : dist z c < δ := by simpa only [Metric.mem_ball] using hz
    exact hz'.trans (by dsimp [δ]; linarith)
  obtain ⟨ε₀, hε₀, hsmall⟩ :=
    exists_small_fermiPositivePolarCoordinate_norm_lt
      (m + a * c.im) a b ha hb hδ
  let ε := ε₀ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  refine ⟨ε, δ, hε, hδ, hball, ?_⟩
  intro ρ hρ hρε
  have hρε₀ : ρ < ε₀ := by dsimp [ε] at hρε; linarith
  have hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ := by
    intro θ
    exact hsmall ρ hρ.le hρε₀ θ
  let H := translatedFermiSideSurfaceHomotopy_convex
    B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb hformula hB ℓ ρ δ hℓ hρ
      hcircle hball hq
  refine ⟨hq, H, ?_⟩
  · intro θ
    exact translatedFermiSideSurfaceHomotopy_convex_oneTurn
      B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb hformula hB ℓ ρ δ
      hℓ hρ hcircle hball hq θ

/-- The generic comparison instantiated on the actual lower half of the
unit-disk cover, using its selected literal circle around the lower puncture.
The input chart contains the full unit disk, as in the marked local-disk
construction. -/
theorem twoPuncturedDiskLowerSide_uniformSurfaceComparison
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (hunit : Metric.ball (0 : ℂ) 1 ⊆ U)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    UniformTranslatedFermiSideSurfaceComparison
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      (twoPuncturedDiskRightCenter β)
      (twoPuncturedDiskLowerBase_convex α β)
      (twoPuncturedDiskLeftCenter_mem_lowerBase hα hα1 hαβ)
      (by
        intro z hz
        exact hunit hz.1)
      (hunit (by
        change dist (twoPuncturedDiskRightCenter β) 0 < 1
        rw [dist_zero_right, twoPuncturedDiskRightCenter_norm]
        exact abs_lt.mpr ⟨hβ, hβ1⟩))
      (by
        intro z hz heq
        apply twoPuncturedDiskRightCenter_not_lowerBase hαβ
        rw [← heq]
        exact hz)
      f hf γ m a b ha hb hformula
      (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
      (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
      (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) := by
  exact exists_uniform_translatedFermiSideSurfaceComparison
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskLowerBase_isOpen α β)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLeftCenter_mem_lowerBase hα hα1 hαβ)
    (by
      intro z hz
      exact hunit hz.1)
    (hunit (by
      change dist (twoPuncturedDiskRightCenter β) 0 < 1
      rw [dist_zero_right, twoPuncturedDiskRightCenter_norm]
      exact abs_lt.mpr ⟨hβ, hβ1⟩))
    (by
      intro z hz heq
      apply twoPuncturedDiskRightCenter_not_lowerBase hαβ
      rw [← heq]
      exact hz)
    f hf γ m a b ha hb hformula
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)

/-- The generic comparison instantiated on the actual upper half of the
unit-disk cover, using its selected literal circle around the upper puncture. -/
theorem twoPuncturedDiskUpperSide_uniformSurfaceComparison
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (hunit : Metric.ball (0 : ℂ) 1 ⊆ U)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    UniformTranslatedFermiSideSurfaceComparison
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      (twoPuncturedDiskLeftCenter α)
      (twoPuncturedDiskUpperBase_convex α β)
      (twoPuncturedDiskRightCenter_mem_upperBase hβ hβ1 hαβ)
      (by
        intro z hz
        exact hunit hz.1)
      (hunit (by
        change dist (twoPuncturedDiskLeftCenter α) 0 < 1
        rw [dist_zero_right, twoPuncturedDiskLeftCenter_norm]
        exact abs_lt.mpr ⟨hα, hα1⟩))
      (by
        intro z hz heq
        apply twoPuncturedDiskLeftCenter_not_upperBase hαβ
        rw [← heq]
        exact hz)
      f hf γ m a b ha hb hformula
      (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
      (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
      (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) := by
  exact exists_uniform_translatedFermiSideSurfaceComparison
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskUpperBase_isOpen α β)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskRightCenter_mem_upperBase hβ hβ1 hαβ)
    (by
      intro z hz
      exact hunit hz.1)
    (hunit (by
      change dist (twoPuncturedDiskLeftCenter α) 0 < 1
      rw [dist_zero_right, twoPuncturedDiskLeftCenter_norm]
      exact abs_lt.mpr ⟨hα, hα1⟩))
    (by
      intro z hz heq
      apply twoPuncturedDiskLeftCenter_not_upperBase hαβ
      rw [← heq]
      exact hz)
    f hf γ m a b ha hb hformula
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)

#print axioms translatedFermiPositivePolarCoordinateHomotopy_convex
#print axioms translatedFermiPositivePolarCoordinateBasedFreeGenerator
#print axioms translatedFermiSideSurfaceHomotopy_convex_oneTurn
#print axioms exists_uniform_translatedFermiSideSurfaceComparison
#print axioms twoPuncturedDiskLowerSide_uniformSurfaceComparison
#print axioms twoPuncturedDiskUpperSide_uniformSurfaceComparison

end

end SystolicGrowth
