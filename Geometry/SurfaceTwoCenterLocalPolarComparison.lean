module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.FermiDiskPositiveWinding
public import Geometry.SurfaceFermiDiskBoundaryComparison
public import Geometry.TwoPuncturedDiskGeometricGenerators
public import Geometry.DirichletPuncturePolarLoop
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Translate the local positive-polar comparison to an actual side domain

At an imaginary-axis puncture, the oriented Fermi chart is translated only
in its axial parameter. The existing nonvanishing Fermi comparison therefore
gives a genuine homotopy inside the actual convex side, and the chart formula
identifies its endpoint with the original surface's positive polar circle.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups unitInterval

namespace SystolicGrowth

noncomputable section

/-- The original quotient carrier with both local chart centers removed. -/
abbrev OriginalTwoCenterPuncturedCarrier {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o₁ o₂ : ℍ) :=
  {q : X.Carrier // q ≠ (Quotient.mk'' o₁ : X.Carrier) ∧
    q ≠ (Quotient.mk'' o₂ : X.Carrier)}

/-- Shifting the axial coordinate to an imaginary-axis point is exactly a
translation of the Fermi parameter `m`. -/
theorem orientedFermiDiskPoint_shift_axis (m a b : ℝ) (c z : ℂ)
    (hc : c.re = 0) :
    orientedFermiDiskPoint m a b (c + z) =
      orientedFermiDiskPoint (m + a * c.im) a b z := by
  change gluingFinFermiPoint 1 (m + a * (c + z).im) (b * (c + z).re) =
    gluingFinFermiPoint 1 (m + a * c.im + a * z.im) (b * z.re)
  have hcoords : (m + a * (c + z).im, b * (c + z).re) =
      (m + a * c.im + a * z.im, b * z.re) := by
    apply Prod.ext
    · rw [Complex.add_im]
      ring
    · rw [Complex.add_re, hc, zero_add]
  exact congrArg (fun p : ℝ × ℝ => gluingFinFermiPoint 1 p.1 p.2) hcoords

/-- The pulled-back Fermi polar point remains a literal point of the
imaginary-axis translated side, not an inverse-defined loop. -/
def translatedFermiPositivePolarCoordinateMap (B : Set ℂ) (c : ℂ)
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ρ δ : ℝ) (hρ : 0 < ρ)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    C(Circle, puncturedBaseAt B c) where
  toFun := fun θ => ⟨c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ,
    ⟨hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      have heq : c + fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ - c =
          fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ := by abel
      rw [heq]
      exact hq θ), by
        intro h
        have h' : c + fermiPositivePolarCoordinate
            (m + a * c.im) a b ha hb ρ θ = c + 0 := by simpa using h
        have hz : fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ = 0 :=
          add_left_cancel h'
        exact fermiPositivePolarCoordinate_ne_zero (m + a * c.im) a b ha hb hρ θ hz⟩⟩
  continuous_toFun :=
    (continuous_const.add
      (fermiPositivePolarCoordinate_continuous (m + a * c.im) a b ha hb ρ)).subtype_mk _

/-- The translated straight Fermi interpolation is a homotopy inside the
actual punctured convex side between its literal small circle and the actual
polar pullback. -/
def translatedFermiPositivePolarCoordinateHomotopy
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ)
    (hℓδ : ℓ < δ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).Homotopy
      (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq) where
  toContinuousMap :=
    { toFun p := ⟨c + fermiPositiveCoordinateInterpolation
        (m + a * c.im) a b ha hb ℓ ρ p.1 p.2,
        ⟨hball (by
          rw [Metric.mem_ball, dist_eq_norm]
          have heq : c + fermiPositiveCoordinateInterpolation
              (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 - c =
              fermiPositiveCoordinateInterpolation
                (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 := by abel
          rw [heq]
          exact fermiPositiveCoordinateInterpolation_norm_lt
            (m + a * c.im) a b ha hb hℓ hℓδ hq p.1 p.2), by
          intro h
          have h' : c + fermiPositiveCoordinateInterpolation
              (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 = c + 0 := by simpa using h
          have hz : fermiPositiveCoordinateInterpolation
              (m + a * c.im) a b ha hb ℓ ρ p.1 p.2 = 0 := add_left_cancel h'
          exact fermiPositiveCoordinateInterpolation_ne_zero
            (m + a * c.im) a b ha hb hℓ hρ p.1 p.2 hz⟩⟩,
      continuous_toFun := by
        have ht : Continuous (fun p : I × Circle => (p.1 : ℝ)) :=
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
        exact (continuous_const.add hinterp).subtype_mk _ }
  map_zero_left θ := by
    apply Subtype.ext
    simp [fermiPositiveCoordinateInterpolation, puncturedBaseCircleInclusion,
      convexPuncturedCircleInclusion, puncturedBaseTranslationHomeomorph, add_comm]
  map_one_left θ := by
    apply Subtype.ext
    simp [fermiPositiveCoordinateInterpolation, translatedFermiPositivePolarCoordinateMap]

/-- Openness at the actual puncture supplies a small coordinate circle and
an actual Fermi-polar comparison circle, both in that same side. -/
theorem exists_translatedFermiPositivePolarCoordinateHomotopy
    {B : Set ℂ} {c : ℂ} (hBopen : IsOpen B) (hc : c ∈ B)
    (hB : Convex ℝ B) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ (δ ℓ ρ : ℝ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
      (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
      (hball : Metric.ball c δ ⊆ B)
      (hq : ∀ θ : Circle,
        ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ),
      Nonempty ((puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle).Homotopy
        (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq)) := by
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hBopen c hc
  let δ := ε / 2
  let ℓ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  have hℓδ : ℓ < δ := by dsimp [ℓ, δ]; linarith
  have hball : Metric.ball c δ ⊆ B := by
    intro z hz
    apply hεball
    have hz' : dist z c < δ := by simpa only [Metric.mem_ball] using hz
    exact lt_trans hz' (by dsimp [δ]; linarith)
  have hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B := by
    intro θ
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : c + ℓ • (θ : ℂ) - c = ℓ • (θ : ℂ) := by abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, Circle.norm_coe]
    simpa using hℓδ
  obtain ⟨ερ, hερ, hsmall⟩ := exists_small_fermiPositivePolarCoordinate_norm_lt
    (m + a * c.im) a b ha hb hδ
  let ρ := ερ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ :=
    hsmall ρ hρ.le (by dsimp [ρ]; linarith)
  refine ⟨δ, ℓ, ρ, hℓ, hρ, hcircle, hball, hq, ?_⟩
  exact ⟨translatedFermiPositivePolarCoordinateHomotopy B c hB m a b ha hb
    ℓ ρ δ hℓ hℓδ hρ hcircle hball hq⟩

/-- Map an actual convex side in an embedded chart to the original surface
with both actual center points removed. Injectivity of the chart and the
literal exclusion of the other coordinate center prove both omissions. -/
def translatedFermiSideChartMap {g : ℕ} {X : ClosedHyperbolicSurface g}
    {U : Set ℂ} (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U)
    (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) :
    C(puncturedBaseAt B c,
      OriginalTwoCenterPuncturedCarrier X
        (γ • orientedFermiDiskPoint m a b c)
        (γ • orientedFermiDiskPoint m a b c₂)) := by
  let coord : puncturedBaseAt B c → U := fun z => ⟨z.1, hBU z.2.1⟩
  have hcoord : Continuous coord := continuous_subtype_val.subtype_mk _
  refine ⟨fun z => ⟨f (coord z), ?_⟩, ?_⟩
  · constructor
    · intro hz
      have hcenter := hformula ⟨c, hBU hcB⟩
      have hcenter' : f ⟨c, hBU hcB⟩ =
          (Quotient.mk'' (γ • orientedFermiDiskPoint m a b c) : X.Carrier) := by
        simpa [ClosedHyperbolicSurface.orbitProjection] using hcenter
      have heq : f (coord z) = f ⟨c, hBU hcB⟩ := by
        calc
          f (coord z) = (Quotient.mk'' (γ • orientedFermiDiskPoint m a b c) : X.Carrier) := hz
          _ = f ⟨c, hBU hcB⟩ := hcenter'.symm
      have hcoordEq := hf.injective heq
      exact z.2.2 (congrArg Subtype.val hcoordEq)
    · intro hz
      have hother := hformula ⟨c₂, hc₂⟩
      have hother' : f ⟨c₂, hc₂⟩ =
          (Quotient.mk'' (γ • orientedFermiDiskPoint m a b c₂) : X.Carrier) := by
        simpa [ClosedHyperbolicSurface.orbitProjection] using hother
      have heq : f (coord z) = f ⟨c₂, hc₂⟩ := by
        calc
          f (coord z) = (Quotient.mk'' (γ • orientedFermiDiskPoint m a b c₂) : X.Carrier) := hz
          _ = f ⟨c₂, hc₂⟩ := hother'.symm
      have hcoordEq := hf.injective heq
      exact hBother z.1 z.2.1 (congrArg Subtype.val hcoordEq)
  · exact (f.continuous.comp hcoord).subtype_mk _

/-- The actual translated positive polar circle in the original twice-center
punctured surface, obtained by the literal side chart map. -/
def translatedFermiSideSurfacePolarMap {g : ℕ} {X : ClosedHyperbolicSurface g}
    {U : Set ℂ} (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U)
    (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (ρ δ : ℝ) (hρ : 0 < ρ) (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    C(Circle, OriginalTwoCenterPuncturedCarrier X
      (γ • orientedFermiDiskPoint m a b c)
      (γ • orientedFermiDiskPoint m a b c₂)) :=
  (translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
    (translatedFermiPositivePolarCoordinateMap B c m a b ha hb
      ρ δ hρ hball hq)

/-- Project the actual side comparison homotopy through the literal embedded
chart; this is a homotopy in the original surface with both centers removed. -/
def translatedFermiSideSurfaceHomotopy {g : ℕ} {X : ClosedHyperbolicSurface g}
    {U : Set ℂ} (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U)
    (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hB : Convex ℝ B) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ) (hℓδ : ℓ < δ)
    (hρ : 0 < ρ) (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
        (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).Homotopy
      (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
        hformula ρ δ hρ hball hq) :=
  (ContinuousMap.Homotopy.refl
      (translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula)).comp
    (translatedFermiPositivePolarCoordinateHomotopy B c hB m a b ha hb
      ℓ ρ δ hℓ hℓδ hρ hcircle hball hq)

/-- Pointwise, the translated Fermi endpoint is the actual positive polar
point on the original surface. The chart phase is recorded explicitly. -/
theorem translatedFermiSideSurfacePolarMap_eq_originalPolar
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U) (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hcRe : c.re = 0) (ρ δ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    ((translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
      hformula ρ δ hρ hball hq θ).1 : X.Carrier) =
      (X.dirichletPuncturePolarCircle
        (γ • orientedFermiDiskPoint m a b c) ρ hρ hsys
        (fermiSLPolarAngleMap γ (orientedFermiDiskPoint (m + a * c.im) a b 0)
          θ)).1 := by
  let M := m + a * c.im
  let v := fermiPositivePolarCoordinate M a b ha hb ρ θ
  have hvball : c + v ∈ B := hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : c + v - c = v := by abel
    rw [heq]
    exact hq θ)
  have hchart := hformula ⟨c + v, hBU hvball⟩
  have hcenter : orientedFermiDiskPoint m a b c =
      orientedFermiDiskPoint M a b 0 := by
    simpa [M] using orientedFermiDiskPoint_shift_axis m a b c 0 hcRe
  change f ⟨c + v, hBU hvball⟩ =
      (Quotient.mk'' (gluingPolarPoint
      (γ • orientedFermiDiskPoint m a b c)
      (fermiSLPolarAngleMap γ (orientedFermiDiskPoint (m + a * c.im) a b 0)
        θ) ρ) : X.Carrier)
  rw [hchart, orientedFermiDiskPoint_shift_axis m a b c v hcRe,
    orientedFermiDiskPoint_positivePolarCoordinate, gluingPolarPoint_smul]
  rw [hcenter]
  rfl

/-- The coordinate quarter-turn is undone by multiplication by `I`. -/
theorem fermiPositivePolarAngle_mul_I (φ : Circle) :
    fermiPositivePolarAngle (⟨Complex.I, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [Complex.norm_I]⟩ * φ) = φ := by
  apply Circle.ext
  change -Complex.I * (Complex.I * (φ : ℂ)) = (φ : ℂ)
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    norm_num
  rw [← mul_assoc, hI, one_mul]

/-- Multiplication by `I` also undoes the positive-angle quarter-turn. -/
theorem circleI_mul_fermiPositivePolarAngle (θ : Circle) :
    ⟨Complex.I, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [Complex.norm_I]⟩ * fermiPositivePolarAngle θ = θ := by
  apply Circle.ext
  change Complex.I * (-Complex.I * (θ : ℂ)) = (θ : ℂ)
  have hI : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  rw [← mul_assoc, hI, one_mul]

/-- A continuous parameter change undoing the Fermi and deck phases. -/
def fermiSLPolarAnglePreimageMap (γ : SL(2, ℝ)) (o : ℍ) : C(Circle, Circle) where
  toFun φ := ⟨Complex.I, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.norm_I]⟩ *
    ((gluingPolarSLPhase γ o)⁻¹ * φ)
  continuous_toFun :=
    continuous_const.mul (continuous_const.mul continuous_id)

/-- The preimage map undoes both the Fermi coordinate quarter-turn and the
actual deck-transformation phase. -/
theorem fermiSLPolarAngleMap_preimage (γ : SL(2, ℝ)) (o : ℍ) (φ : Circle) :
    fermiSLPolarAngleMap γ o (fermiSLPolarAnglePreimageMap γ o φ) = φ := by
  change gluingPolarSLPhase γ o *
    fermiPositivePolarAngle
      (⟨Complex.I, by
        apply mem_sphere_zero_iff_norm.mpr
        rw [Complex.norm_I]⟩ * ((gluingPolarSLPhase γ o)⁻¹ * φ)) = φ
  rw [fermiPositivePolarAngle_mul_I]
  simp

/-- The inverse parameter is two-sided, so it is a genuine change of circle
coordinate rather than only a right inverse. -/
theorem fermiSLPolarAnglePreimageMap_phase (γ : SL(2, ℝ)) (o : ℍ) (θ : Circle) :
    fermiSLPolarAnglePreimageMap γ o (fermiSLPolarAngleMap γ o θ) = θ := by
  change ⟨Complex.I, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [Complex.norm_I]⟩ *
    ((gluingPolarSLPhase γ o)⁻¹ *
      (gluingPolarSLPhase γ o * fermiPositivePolarAngle θ)) = θ
  rw [inv_mul_cancel_left, circleI_mul_fermiPositivePolarAngle]

/-- The literal original-surface polar circle, now retained in the actual
twice-center-punctured subtype. Its parameter is the original polar angle. -/
def translatedFermiSideOriginalPolarMap
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U) (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (_hcRe : c.re = 0) (ρ δ : ℝ) (hρ : 0 < ρ) (_hsys : 2 * ρ < X.systole)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    C(Circle, OriginalTwoCenterPuncturedCarrier X
      (γ • orientedFermiDiskPoint m a b c)
      (γ • orientedFermiDiskPoint m a b c₂)) :=
  (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
    ha hb hformula ρ δ hρ hball hq).comp
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * c.im) a b 0))

/-- After forgetting only the second-puncture proof, the subtype-valued
circle is exactly the original Dirichlet polar circle at each angle. -/
theorem translatedFermiSideOriginalPolarMap_coe
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U) (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hcRe : c.re = 0) (ρ δ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (φ : Circle) :
    ((translatedFermiSideOriginalPolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
      ha hb hformula hcRe ρ δ hρ hsys hball hq φ).1 : X.Carrier) =
      (X.dirichletPuncturePolarCircle
        (γ • orientedFermiDiskPoint m a b c) ρ hρ hsys φ).1 := by
  let o := orientedFermiDiskPoint (m + a * c.im) a b 0
  let F := translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf
    γ m a b ha hb hformula ρ δ hρ hball hq
  let ψ := fermiSLPolarAnglePreimageMap γ o φ
  change ((F ψ).1 : X.Carrier) =
    (X.dirichletPuncturePolarCircle
      (γ • orientedFermiDiskPoint m a b c) ρ hρ hsys φ).1
  calc
    ((F ψ).1 : X.Carrier) =
        (X.dirichletPuncturePolarCircle
          (γ • orientedFermiDiskPoint m a b c) ρ hρ hsys
          (fermiSLPolarAngleMap γ o ψ)).1 :=
      translatedFermiSideSurfacePolarMap_eq_originalPolar B c c₂ hBU hcB hc₂
        hBother f hf γ m a b ha hb hformula hcRe ρ δ hρ hsys hball hq ψ
    _ = (X.dirichletPuncturePolarCircle
          (γ • orientedFermiDiskPoint m a b c) ρ hρ hsys φ).1 := by
      rw [fermiSLPolarAngleMap_preimage]

/-- The original phase-parametrized polar circle composed with its explicit
phase is literally the translated side map, including both puncture proofs. -/
theorem translatedFermiSideOriginalPolarMap_comp_phase
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U) (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hcRe : c.re = 0) (ρ δ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ) :
    (translatedFermiSideOriginalPolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
      ha hb hformula hcRe ρ δ hρ hsys hball hq).comp
        (fermiSLPolarAngleMap γ
          (orientedFermiDiskPoint (m + a * c.im) a b 0)) =
      translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
        ha hb hformula ρ δ hρ hball hq := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  change ((translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
      ha hb hformula ρ δ hρ hball hq
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * c.im) a b 0)
        (fermiSLPolarAngleMap γ (orientedFermiDiskPoint (m + a * c.im) a b 0) θ))).1 :
        X.Carrier) =
    ((translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
      ha hb hformula ρ δ hρ hball hq θ).1 : X.Carrier)
  exact congrArg
    (fun ψ => ((translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf
      γ m a b ha hb hformula ρ δ hρ hball hq ψ).1 : X.Carrier))
    (fermiSLPolarAnglePreimageMap_phase γ
      (orientedFermiDiskPoint (m + a * c.im) a b 0) θ)

/-- Mapping a positively reparametrized circle loop through a map and then
casting its basepoint gives the literal loop at the reparametrized point. -/
theorem circleOneTurnLoop_map_comp_cast
    {Y : Type*} [TopologicalSpace Y]
    (P : C(Circle, Y)) (A : C(Circle, Circle)) (F : C(Circle, Y))
    (hcomp : P.comp A = F) (θ : Circle)
    (hturn : (circleOneTurnLoop θ).map A.continuous = circleOneTurnLoop (A θ)) :
    let hbase := congrArg (fun G : C(Circle, Y) => G θ) hcomp
    ((circleOneTurnLoop (A θ)).map P.continuous).cast hbase.symm hbase.symm =
      (circleOneTurnLoop θ).map F.continuous := by
  let hbase := congrArg (fun G : C(Circle, Y) => G θ) hcomp
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
  have hturnAt : A (circleOneTurnLoop θ t) = circleOneTurnLoop (A θ) t :=
    congrArg (fun p : Path (A θ) (A θ) => p t) hturn
  calc
    P (circleOneTurnLoop (A θ) t) = P (A (circleOneTurnLoop θ t)) :=
      congrArg P hturnAt.symm
    _ = F (circleOneTurnLoop θ t) := by
      have h := congrArg (fun G : C(Circle, Y) => G (circleOneTurnLoop θ t)) hcomp
      simpa [ContinuousMap.comp_apply] using h

/-- The mapped coordinate-side positive turn is literally the original
positive polar loop at its phase-adjusted basepoint. -/
theorem translatedFermiSideOriginalPolarMap_oneTurn
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U) (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hcRe : c.re = 0) (ρ δ : ℝ) (hρ : 0 < ρ) (hsys : 2 * ρ < X.systole)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    let P := translatedFermiSideOriginalPolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
      ha hb hformula hcRe ρ δ hρ hsys hball hq
    let A := fermiSLPolarAngleMap γ
      (orientedFermiDiskPoint (m + a * c.im) a b 0)
    let F := translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
      ha hb hformula ρ δ hρ hball hq
    let hbase := congrArg (fun G : C(Circle, OriginalTwoCenterPuncturedCarrier X
      (γ • orientedFermiDiskPoint m a b c)
      (γ • orientedFermiDiskPoint m a b c₂)) => G θ)
      (translatedFermiSideOriginalPolarMap_comp_phase B c c₂ hBU hcB hc₂ hBother
        f hf γ m a b ha hb hformula hcRe ρ δ hρ hsys hball hq)
    ((circleOneTurnLoop (A θ)).map P.continuous).cast hbase.symm hbase.symm =
      (circleOneTurnLoop θ).map F.continuous := by
  let P := translatedFermiSideOriginalPolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
    ha hb hformula hcRe ρ δ hρ hsys hball hq
  let A := fermiSLPolarAngleMap γ (orientedFermiDiskPoint (m + a * c.im) a b 0)
  let F := translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b
    ha hb hformula ρ δ hρ hball hq
  have hmap : P.comp A = F :=
    translatedFermiSideOriginalPolarMap_comp_phase B c c₂ hBU hcB hc₂ hBother
      f hf γ m a b ha hb hformula hcRe ρ δ hρ hsys hball hq
  have hphase : (circleOneTurnLoop θ).map A.continuous = circleOneTurnLoop (A θ) := by
    exact circleOneTurnLoop_map_fermiSLPolarAngleMap γ
      (orientedFermiDiskPoint (m + a * c.im) a b 0) θ
  change let hbase := congrArg (fun G : C(Circle, _) => G θ) hmap
    ((circleOneTurnLoop (A θ)).map P.continuous).cast hbase.symm hbase.symm =
      (circleOneTurnLoop θ).map F.continuous
  exact circleOneTurnLoop_map_comp_cast P A F hmap θ hphase

/-- The projected comparison transports the positive one-turn class along
its actual basepoint track; the phase-adjusted target circle is still a
literal positive turn. -/
theorem translatedFermiSideSurfaceHomotopy_oneTurn
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (B : Set ℂ) (c c₂ : ℂ) (hBU : B ⊆ U) (hcB : c ∈ B) (hc₂ : c₂ ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ c₂)
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hB : Convex ℝ B) (ℓ ρ δ : ℝ) (hℓ : 0 < ℓ) (hℓδ : ℓ < δ)
    (hρ : 0 < ρ) (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((translatedFermiSideSurfaceHomotopy B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
          hformula hB ℓ ρ δ hℓ hℓδ hρ hcircle hball hq).evalAt θ)
      ⟦(circleOneTurnLoop θ).map
        ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
          (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
          hformula ρ δ hρ hball hq).continuous⟧ := by
  let H := translatedFermiSideSurfaceHomotopy B c c₂ hBU hcB hc₂ hBother f hf
    γ m a b ha hb hformula hB ℓ ρ δ hℓ hℓδ hρ hcircle hball hq
  let p := (circleOneTurnLoop θ).map
    ((translatedFermiSideChartMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b hformula).comp
      (puncturedBaseCircleInclusion B c ℓ hB hℓ hcircle)).continuous
  let q := (circleOneTurnLoop θ).map
    (translatedFermiSideSurfacePolarMap B c c₂ hBU hcB hc₂ hBother f hf γ m a b ha hb
      hformula ρ δ hρ hball hq).continuous
  let γpath := H.evalAt θ
  have hhom : (p.trans γpath).Homotopic (γpath.trans q) :=
    Path.Homotopic.map_trans_evalAt H (circleOneTurnLoop θ)
  have heq := Path.Homotopic.Quotient.eq.mpr hhom
  change Path.Homotopic.Quotient.mk (γpath.symm.trans (p.trans γpath)) =
    Path.Homotopic.Quotient.mk q
  rw [Path.Homotopic.Quotient.mk_trans, heq,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

#print axioms translatedFermiSideSurfacePolarMap_eq_originalPolar
#print axioms translatedFermiSideSurfaceHomotopy_oneTurn
#print axioms translatedFermiSideOriginalPolarMap_coe
#print axioms translatedFermiSideOriginalPolarMap_comp_phase
#print axioms translatedFermiSideOriginalPolarMap_oneTurn

end

end SystolicGrowth
