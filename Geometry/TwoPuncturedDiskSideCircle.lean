module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConvexPuncturedDomainCircle
public import Geometry.GluingSeamFundamentalGroup
public import Geometry.TwoPuncturedDiskOpenCover
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# The two actual punctured disk sides retract to circles

Each convex side contains a small literal circle about its retained center.
Translation to the center followed by the convex radial deformation retraction
therefore gives its actual based circle fundamental group.
-/

open Set Metric
open scoped ContinuousMap Topology unitInterval

namespace SystolicGrowth

noncomputable section

/-- Translate a convex base so the retained puncture becomes the origin. -/
def puncturedBaseTranslated (B : Set ℂ) (c : ℂ) : Set ℂ :=
  (fun z : ℂ => z + c) ⁻¹' B

/-- The base with its retained point removed. -/
abbrev puncturedBaseAt (B : Set ℂ) (c : ℂ) := {z : ℂ // z ∈ B ∧ z ≠ c}

/-- Translation identifies a base punctured at `c` with the translated base
punctured at the origin. -/
def puncturedBaseTranslationHomeomorph (B : Set ℂ) (c : ℂ) :
    puncturedBaseAt B c ≃ₜ convexPuncturedDomain (puncturedBaseTranslated B c) where
  toFun z := ⟨z.1 - c, by
    constructor
    · change (z.1 - c) + c ∈ B
      simpa using z.2.1
    · intro hz
      apply z.2.2
      exact sub_eq_zero.mp hz⟩
  invFun z := ⟨z.1 + c, by
    constructor
    · exact z.2.1
    · intro hz
      have hzero : z.1 = 0 := by
        have hz' : z.1 + c = (0 : ℂ) + c := by simpa using hz
        exact add_right_cancel hz'
      exact z.2.2 hzero⟩
  left_inv z := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
  continuous_toFun :=
    (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.add continuous_const).subtype_mk _

/-- Translation preserves convexity of the punctured base. -/
theorem puncturedBaseTranslated_convex {B : Set ℂ} (hB : Convex ℝ B) (c : ℂ) :
    Convex ℝ (puncturedBaseTranslated B c) := by
  exact hB.translate_preimage_left c

/-- Openness at a retained point supplies a genuine small circle lying in the
original base. -/
theorem exists_small_circle_mem_of_isOpen {B : Set ℂ} {c : ℂ}
    (hB : IsOpen B) (hc : c ∈ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hB c hc
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρε : ρ < ε := by dsimp [ρ]; linarith
  refine ⟨ρ, hρ, ?_⟩
  intro θ
  apply hball
  change dist (c + ρ • (θ : ℂ)) c < ε
  rw [dist_eq_norm]
  have hsub : c + ρ • (θ : ℂ) - c = ρ • (θ : ℂ) := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe]
  simpa using hρε

/-- A convex base punctured at an interior point is homotopy equivalent to
the literal normalized unit circle whenever it contains a positive circle
about that point. -/
def puncturedBaseCircleHomotopyEquiv (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B) :
    puncturedBaseAt B c ≃ₕ Circle := by
  exact (puncturedBaseTranslationHomeomorph B c).toHomotopyEquiv.trans
    (convexPuncturedDomainCircleHomotopyEquiv
      (puncturedBaseTranslated B c) ρ
      (puncturedBaseTranslated_convex hB c) hρ (by
        intro θ
        change (ρ • (θ : ℂ)) + c ∈ B
        rw [add_comm]
        exact hcircle θ))

/-- The inverse map of the translated circle equivalence is the literal
radius-`ρ` circle about the retained point. -/
def puncturedBaseCircleInclusion (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (_hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B) :
    C(Circle, puncturedBaseAt B c) :=
  ((puncturedBaseTranslationHomeomorph B c).symm :
    C(convexPuncturedDomain (puncturedBaseTranslated B c), puncturedBaseAt B c)).comp
      (convexPuncturedCircleInclusion (puncturedBaseTranslated B c) ρ hρ (by
        intro θ
        change (ρ • (θ : ℂ)) + c ∈ B
        rw [add_comm]
        exact hcircle θ))

/-- Radial normalization after translation is the actual retraction from the
punctured base to the unit circle. -/
def puncturedBaseCircleRetraction (B : Set ℂ) (c : ℂ) :
    C(puncturedBaseAt B c, Circle) :=
  (convexPuncturedCircleRetraction (puncturedBaseTranslated B c)).comp
    (puncturedBaseTranslationHomeomorph B c :
      C(puncturedBaseAt B c,
        convexPuncturedDomain (puncturedBaseTranslated B c)))

/-- The translated normalization literally uses `z-c`. -/
theorem puncturedBaseCircleRetraction_apply (B : Set ℂ) (c : ℂ)
    (z : puncturedBaseAt B c) :
    puncturedBaseCircleRetraction B c z =
      convexPuncturedUnitDirection (z.1 - c) (by
        intro hz
        apply z.2.2
        exact sub_eq_zero.mp hz) := by
  apply Circle.ext
  rfl

/-- The homotopy equivalence's inverse fixes its included literal circle. -/
@[simp]
theorem puncturedBaseCircleRetraction_inclusion (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B) (θ : Circle) :
    puncturedBaseCircleRetraction B c
      (puncturedBaseCircleInclusion B c ρ hB hρ hcircle θ) = θ := by
  let Ω := puncturedBaseTranslated B c
  have hΩcircle : ∀ φ : Circle, ρ • (φ : ℂ) ∈ Ω := by
    intro φ
    change (ρ • (φ : ℂ)) + c ∈ B
    rw [add_comm]
    exact hcircle φ
  have htranslated : puncturedBaseTranslationHomeomorph B c
      (puncturedBaseCircleInclusion B c ρ hB hρ hcircle θ) =
        convexPuncturedCircleInclusion Ω ρ hρ hΩcircle θ := by
    apply Subtype.ext
    simp [puncturedBaseCircleInclusion, puncturedBaseTranslationHomeomorph,
      convexPuncturedCircleInclusion]
  change convexPuncturedCircleRetraction Ω
    (puncturedBaseTranslationHomeomorph B c
      (puncturedBaseCircleInclusion B c ρ hB hρ hcircle θ)) = θ
  rw [htranslated]
  exact convexPuncturedCircleRetraction_inclusion Ω ρ hρ hΩcircle θ

/-- The punctured base is path connected by its actual circle retraction. -/
theorem puncturedBase_pathConnected (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B) :
    PathConnectedSpace (puncturedBaseAt B c) := by
  let Ω := puncturedBaseTranslated B c
  have hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω := by
    intro θ
    change (ρ • (θ : ℂ)) + c ∈ B
    rw [add_comm]
    exact hcircle θ
  letI := convexPuncturedDomain_pathConnected Ω ρ
    (puncturedBaseTranslated_convex hB c) hρ hΩcircle
  exact Function.Surjective.pathConnectedSpace
    (puncturedBaseTranslationHomeomorph B c).symm.surjective
    (puncturedBaseTranslationHomeomorph B c).symm.continuous

/-- The actual based fundamental group at any punctured-base point is carried
to the circle group at its literal normalized direction. -/
noncomputable def puncturedBaseCircleFundamentalGroupEquiv (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B)
    (z : puncturedBaseAt B c) :
    FundamentalGroup (puncturedBaseAt B c) z ≃*
      FundamentalGroup Circle (puncturedBaseCircleHomotopyEquiv B c ρ hB hρ hcircle z) := by
  let e := puncturedBaseCircleHomotopyEquiv B c ρ hB hρ hcircle
  let h := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact MulEquiv.ofBijective (FundamentalGroup.map e.toFun z)
    (h.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
      (FundamentalGroupoid.mk z))

/-- A positive one-turn loop in the actual included circle maps to the
positive one-turn class in the normalized circle. -/
theorem puncturedBaseCircleRetraction_oneTurn (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B) (θ : Circle) :
    FundamentalGroup.mapOfEq (puncturedBaseCircleRetraction B c)
      (puncturedBaseCircleRetraction_inclusion B c ρ hB hρ hcircle θ)
      ⟦(circleOneTurnLoop θ).map
        (puncturedBaseCircleInclusion B c ρ hB hρ hcircle).continuous⟧ =
      ⟦circleOneTurnLoop θ⟧ := by
  erw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  exact puncturedBaseCircleRetraction_inclusion B c ρ hB hρ hcircle (circleOneTurnLoop θ t)

/-- The actual selected positive loop has the integer generator, not its
inverse, after radial normalization. -/
theorem puncturedBaseCircleRetraction_oneTurn_integer (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B) (θ : Circle) :
    circleFundamentalGroupEquivIntegers θ
      (FundamentalGroup.mapOfEq (puncturedBaseCircleRetraction B c)
        (puncturedBaseCircleRetraction_inclusion B c ρ hB hρ hcircle θ)
        ⟦(circleOneTurnLoop θ).map
          (puncturedBaseCircleInclusion B c ρ hB hρ hcircle).continuous⟧) =
      MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) := by
  rw [puncturedBaseCircleRetraction_oneTurn, circleFundamentalGroupEquivIntegers_oneTurn]

/-- Openness at the retained lower center supplies the actual circle used for
the lower-side deformation retraction. -/
theorem exists_twoPuncturedDiskLowerSideCircleRadius {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : Circle,
      twoPuncturedDiskLeftCenter α + ρ • (θ : ℂ) ∈ twoPuncturedDiskLowerBase α β :=
  exists_small_circle_mem_of_isOpen (twoPuncturedDiskLowerBase_isOpen α β)
    (twoPuncturedDiskLeftCenter_mem_lowerBase hα hα1 hαβ)

/-- Openness at the retained upper center supplies the actual circle used for
the upper-side deformation retraction. -/
theorem exists_twoPuncturedDiskUpperSideCircleRadius {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : Circle,
      twoPuncturedDiskRightCenter β + ρ • (θ : ℂ) ∈ twoPuncturedDiskUpperBase α β :=
  exists_small_circle_mem_of_isOpen (twoPuncturedDiskUpperBase_isOpen α β)
    (twoPuncturedDiskRightCenter_mem_upperBase hβ hβ1 hαβ)

/-- The chosen positive circle radius in the actual lower base. -/
noncomputable def twoPuncturedDiskLowerSideCircleRadius {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) : ℝ :=
  Classical.choose (exists_twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)

theorem twoPuncturedDiskLowerSideCircleRadius_pos {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    0 < twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ :=
  (Classical.choose_spec (exists_twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)).1

theorem twoPuncturedDiskLowerSideCircleRadius_mem {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) (θ : Circle) :
    twoPuncturedDiskLeftCenter α + twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ •
      (θ : ℂ) ∈ twoPuncturedDiskLowerBase α β :=
  (Classical.choose_spec (exists_twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)).2 θ

/-- The chosen positive circle radius in the actual upper base. -/
noncomputable def twoPuncturedDiskUpperSideCircleRadius {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) : ℝ :=
  Classical.choose (exists_twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)

theorem twoPuncturedDiskUpperSideCircleRadius_pos {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    0 < twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ :=
  (Classical.choose_spec (exists_twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)).1

theorem twoPuncturedDiskUpperSideCircleRadius_mem {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) (θ : Circle) :
    twoPuncturedDiskRightCenter β + twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ •
      (θ : ℂ) ∈ twoPuncturedDiskUpperBase α β :=
  (Classical.choose_spec (exists_twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)).2 θ

/-- The homotopy equivalence of the actual lower side, normalized at its
retained center. -/
noncomputable def twoPuncturedDiskLowerSideHomotopyEquiv {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    puncturedBaseAt (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α) ≃ₕ Circle :=
  puncturedBaseCircleHomotopyEquiv (twoPuncturedDiskLowerBase α β)
    (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)

/-- The homotopy equivalence of the actual upper side, normalized at its
retained center. -/
noncomputable def twoPuncturedDiskUpperSideHomotopyEquiv {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    puncturedBaseAt (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β) ≃ₕ Circle :=
  puncturedBaseCircleHomotopyEquiv (twoPuncturedDiskUpperBase α β)
    (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)

/-- The lower equivalence's forward map is normalization of `z-center`. -/
theorem twoPuncturedDiskLowerSideHomotopyEquiv_apply {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β)
    (z : puncturedBaseAt (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)) :
    twoPuncturedDiskLowerSideHomotopyEquiv hα hα1 hαβ z =
      convexPuncturedUnitDirection (z.1 - twoPuncturedDiskLeftCenter α) (by
        intro hz
        apply z.2.2
        exact sub_eq_zero.mp hz) := rfl

/-- The upper equivalence's forward map is normalization of `z-center`. -/
theorem twoPuncturedDiskUpperSideHomotopyEquiv_apply {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (z : puncturedBaseAt (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)) :
    twoPuncturedDiskUpperSideHomotopyEquiv hβ hβ1 hαβ z =
      convexPuncturedUnitDirection (z.1 - twoPuncturedDiskRightCenter β) (by
        intro hz
        apply z.2.2
        exact sub_eq_zero.mp hz) := rfl

/-- The actual lower side is path connected. -/
theorem twoPuncturedDiskLowerSide_pathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    PathConnectedSpace
      (puncturedBaseAt (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)) :=
  puncturedBase_pathConnected (twoPuncturedDiskLowerBase α β)
    (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)

/-- The actual upper side is path connected. -/
theorem twoPuncturedDiskUpperSide_pathConnected {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    PathConnectedSpace
      (puncturedBaseAt (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)) :=
  puncturedBase_pathConnected (twoPuncturedDiskUpperBase α β)
    (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)

/-- Actual lower-side based fundamental group at any original side point. -/
noncomputable def twoPuncturedDiskLowerSideFundamentalGroupEquiv {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β)
    (z : puncturedBaseAt (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)) :
    FundamentalGroup
        (puncturedBaseAt (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)) z ≃*
      FundamentalGroup Circle
        (convexPuncturedUnitDirection (z.1 - twoPuncturedDiskLeftCenter α) (by
          intro hz
          apply z.2.2
          exact sub_eq_zero.mp hz)) :=
  puncturedBaseCircleFundamentalGroupEquiv (twoPuncturedDiskLowerBase α β)
    (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) z

/-- Actual upper-side based fundamental group at any original side point. -/
noncomputable def twoPuncturedDiskUpperSideFundamentalGroupEquiv {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (z : puncturedBaseAt (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)) :
    FundamentalGroup
        (puncturedBaseAt (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)) z ≃*
      FundamentalGroup Circle
        (convexPuncturedUnitDirection (z.1 - twoPuncturedDiskRightCenter β) (by
          intro hz
          apply z.2.2
          exact sub_eq_zero.mp hz)) :=
  puncturedBaseCircleFundamentalGroupEquiv (twoPuncturedDiskUpperBase α β)
    (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) z

/-- The lower actual side's included positive one-turn loop is the positive
integer generator after normalization. -/
theorem twoPuncturedDiskLowerSide_oneTurn_integer {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) (θ : Circle) :
    circleFundamentalGroupEquivIntegers θ
      (FundamentalGroup.mapOfEq (puncturedBaseCircleRetraction
          (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α))
        (puncturedBaseCircleRetraction_inclusion
          (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
          (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
          (twoPuncturedDiskLowerBase_convex α β)
          (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
          (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) θ)
        ⟦(circleOneTurnLoop θ).map
          (puncturedBaseCircleInclusion (twoPuncturedDiskLowerBase α β)
            (twoPuncturedDiskLeftCenter α)
            (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
            (twoPuncturedDiskLowerBase_convex α β)
            (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
            (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)).continuous⟧) =
      MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) := by
  exact puncturedBaseCircleRetraction_oneTurn_integer
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) θ

/-- The upper actual side's included positive one-turn loop is the positive
integer generator after normalization. -/
theorem twoPuncturedDiskUpperSide_oneTurn_integer {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) (θ : Circle) :
    circleFundamentalGroupEquivIntegers θ
      (FundamentalGroup.mapOfEq (puncturedBaseCircleRetraction
          (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β))
        (puncturedBaseCircleRetraction_inclusion
          (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
          (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
          (twoPuncturedDiskUpperBase_convex α β)
          (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
          (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) θ)
        ⟦(circleOneTurnLoop θ).map
          (puncturedBaseCircleInclusion (twoPuncturedDiskUpperBase α β)
            (twoPuncturedDiskRightCenter β)
            (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
            (twoPuncturedDiskUpperBase_convex α β)
            (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
            (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)).continuous⟧) =
      MulOpposite.op (Multiplicative.ofAdd (1 : ℤ)) := by
  exact puncturedBaseCircleRetraction_oneTurn_integer
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) θ

end

end SystolicGrowth
