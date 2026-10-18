module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterBoundarySpine
public import Geometry.GluingSeamOverlap

@[expose] public section

/-!
# Shrinking literal polar loops in a two-center-punctured component

For every positive radius at most the gluing radius, the actual polar circles
avoid both deleted quotient centers. Varying that radius gives a homotopy in
the same original two-center-punctured carrier, with its genuine moving
angle-one basepoint path.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool) : ℍ :=
  if b then (P.centers i).1 else (P.centers i).2

private theorem carrier_dist_polarPoint_center
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (o : ℍ) (θ : Circle) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ < gluingEmbeddedRadius C g) :
    dist (Quotient.mk'' (gluingPolarPoint o θ ρ) : (X i).Carrier)
      (Quotient.mk'' o) = ρ := by
  rw [dist_comm]
  rw [(X i).carrier_dist_mk_center_eq_of_mem_closedBall o
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i)]
  · exact dist_gluingPolarPoint o θ hρ
  · simpa only [mem_closedBall, dist_comm, dist_gluingPolarPoint o θ hρ] using
      hρR.le

theorem Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarPoint_ne_centers
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (b : Bool) (θ : Circle) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ gluingRadius C g) :
    let q : (X i).Carrier := Quotient.mk''
      (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ)
    q ≠ Quotient.mk'' (P.centers i).1 ∧ q ≠ Quotient.mk'' (P.centers i).2 := by
  dsimp only
  have hρR : ρ < gluingEmbeddedRadius C g :=
    lt_of_le_of_lt hρr P.radius_lt_embeddedRadius
  have hown := carrier_dist_polarPoint_center P i (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b)
    θ hρ.le hρR
  have hsep := P.carrier_centers_outer_add_inner_le_dist i
  have hRpos : 0 < gluingEmbeddedRadius C g :=
    lt_trans P.radius_pos P.radius_lt_embeddedRadius
  have hleft : 0 < dist
      (Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ) : (X i).Carrier)
      (Quotient.mk'' (P.centers i).1) := by
    cases b with
    | false =>
      have htri := dist_triangle
        (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ))
        (Quotient.mk'' (P.centers i).2)
      have hqown : dist
          (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).2) = ρ := by
        simpa [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter] using hown
      have htriangle :
          dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
              (Quotient.mk'' (P.centers i).2) ≤
            dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ)) + ρ := by
        rw [hqown] at htri
        exact htri
      rw [dist_comm (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ))] at htriangle
      have hbound : gluingEmbeddedRadius C g ≤
          dist (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ) : (X i).Carrier)
            (Quotient.mk'' (P.centers i).1) := by
        linarith [hsep, htriangle, hρr]
      exact lt_of_lt_of_le hRpos hbound
    | true =>
      have hqown : dist
          (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).1) = ρ := by
        simpa [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter] using hown
      have hpos : 0 < dist
          (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).1) := hqown.symm ▸ hρ
      simpa [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter] using hpos
  have hright : 0 < dist
      (Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ) : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2) := by
    cases b with
    | true =>
      have htri := dist_triangle
        (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ))
        (Quotient.mk'' (P.centers i).2)
      have hqown : dist
          (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).1) = ρ := by
        simpa [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter] using hown
      have hqown' : dist
          (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
          (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ)) = ρ :=
        (dist_comm _ _).trans hqown
      have htriangle :
          dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
              (Quotient.mk'' (P.centers i).2) ≤
            ρ + dist (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ) :
              (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
        rw [hqown'] at htri
        exact htri
      have hbound : gluingEmbeddedRadius C g ≤
          dist (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ) : (X i).Carrier)
            (Quotient.mk'' (P.centers i).2) := by
        linarith [hsep, htriangle, hρr]
      exact lt_of_lt_of_le hRpos hbound
    | false =>
      have hqown : dist
          (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).2) = ρ := by
        simpa [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter] using hown
      have hpos : 0 < dist
          (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).2) := hqown.symm ▸ hρ
      simpa [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter] using hpos
  constructor
  · intro heq
    have hz : dist
        (Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ) :
          (X i).Carrier) (Quotient.mk'' (P.centers i).1) = 0 := by
      rw [heq, dist_self]
    linarith
  · intro heq
    have hz : dist
        (Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ) :
          (X i).Carrier) (Quotient.mk'' (P.centers i).2) = 0 := by
      rw [heq, dist_self]
    linarith

/-- The literal polar point of any positive radius up to the gluing radius
lies in the original quotient with both centers removed. -/
def twoCenterPolarPoint
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (θ : Circle) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    P.CenterPuncturedChainComponent i := by
  let q : (X i).Carrier := Quotient.mk''
    (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ)
  refine ⟨q, ?_⟩
  rw [P.componentCenterPuncturedSet_eq]
  have hne := Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarPoint_ne_centers P i b θ hρ hρr
  by_cases hl : 0 < i.1 <;> by_cases hr : i.1 + 1 < n <;>
    simp [q, hl, hr, hne.1, hne.2]

def Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.centerPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ)
    (ρ : ℝ) (_hρ : 0 < ρ)
    (hmem : ∀ θ, (Quotient.mk'' (gluingPolarPoint o θ ρ) : (X i).Carrier) ∈
      P.componentCenterPuncturedSet i) :
    C(Circle, P.CenterPuncturedChainComponent i) where
  toFun θ := ⟨Quotient.mk'' (gluingPolarPoint o θ ρ), hmem θ⟩
  continuous_toFun := by
    have hparam : Continuous (fun θ : Circle => (θ, ρ)) :=
      continuous_id.prodMk continuous_const
    have hp := (gluingPolarPoint_continuous o).comp hparam
    have hq : Continuous (fun θ : Circle =>
        (Quotient.mk'' (gluingPolarPoint o θ ρ) : (X i).Carrier)) :=
      continuous_quotient_mk'.comp hp
    exact hq.subtype_mk hmem

/-- The actual small-radius polar circle in the native two-center-punctured
component. -/
def twoCenterPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    C(Circle, P.CenterPuncturedChainComponent i) :=
  Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.centerPolarBoundaryMap P i (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) ρ hρ
    (fun θ => (P.twoCenterPolarPoint i b θ ρ hρ hρr).2)

/-- At the original gluing radius, the actual small-circle construction is
definitionally the original incoming polar boundary map. -/
@[simp]
theorem twoCenterPolarBoundaryMap_gluingRadius_left
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.twoCenterPolarBoundaryMap i true (gluingRadius C g) P.radius_pos le_rfl =
      P.componentLeftPolarBoundaryMap i := by
  ext θ
  rfl

/-- At the original gluing radius, the actual small-circle construction is
definitionally the original outgoing polar boundary map. -/
@[simp]
theorem twoCenterPolarBoundaryMap_gluingRadius_right
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.twoCenterPolarBoundaryMap i false (gluingRadius C g) P.radius_pos le_rfl =
      P.componentRightPolarBoundaryMap i := by
  ext θ
  rfl

def Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius (ρ₀ ρ₁ : ℝ) (t : I) : ℝ :=
  (1 - (t : ℝ)) * ρ₀ + (t : ℝ) * ρ₁

theorem Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius_pos (ρ₀ ρ₁ : ℝ)
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (t : I) :
    0 < Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius ρ₀ ρ₁ t := by
  by_cases ht : (t : ℝ) = 0
  · simp [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius, ht, h₀]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hleft : 0 ≤ (1 - (t : ℝ)) * ρ₀ :=
      mul_nonneg (by linarith [t.property.2]) h₀.le
    have hright : 0 < (t : ℝ) * ρ₁ := mul_pos htpos h₁
    exact add_pos_of_nonneg_of_pos hleft hright

theorem Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius_le (ρ₀ ρ₁ R : ℝ)
    (h₀ : ρ₀ ≤ R) (h₁ : ρ₁ ≤ R) (t : I) :
    Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius ρ₀ ρ₁ t ≤ R := by
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have hleft := mul_le_mul_of_nonneg_left h₀ (by linarith)
  have hright := mul_le_mul_of_nonneg_left h₁ ht0
  dsimp [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius]
  nlinarith

theorem Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.continuous_affinePolarGluiPoint (o : ℍ) (ρ₀ ρ₁ : ℝ) :
    Continuous (fun p : I × Circle =>
      gluingPolarPoint o p.2 ((1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ρ₁)) := by
  have hrad : Continuous (fun p : I × Circle =>
      (1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ρ₁) := by
    fun_prop
  have hparam : Continuous (fun p : I × Circle =>
      (p.2, (1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ρ₁)) :=
    continuous_snd.prodMk hrad
  have hmap : Continuous (fun z : Circle × ℝ => gluingPolarPoint o z.1 z.2) :=
    gluingPolarPoint_continuous o
  change Continuous
    ((fun z : Circle × ℝ => gluingPolarPoint o z.1 z.2) ∘
      (fun p : I × Circle =>
        (p.2, (1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ρ₁)))
  exact Continuous.comp hmap hparam

set_option maxHeartbeats 1000000 in
/-- The literal-radius homotopy, with both endpoint radii constrained to the
actual gluing disk. -/
def twoCenterPolarRadiusHomotopy
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ₀ ρ₁ : ℝ) (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀r : ρ₀ ≤ gluingRadius C g) (h₁r : ρ₁ ≤ gluingRadius C g) :
    (P.twoCenterPolarBoundaryMap i b ρ₀ h₀ h₀r).Homotopy
      (P.twoCenterPolarBoundaryMap i b ρ₁ h₁ h₁r) where
  toFun p := P.twoCenterPolarPoint i b p.2 (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius ρ₀ ρ₁ p.1)
    (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius_pos ρ₀ ρ₁ h₀ h₁ p.1)
    (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius_le ρ₀ ρ₁ (gluingRadius C g) h₀r h₁r p.1)
  continuous_toFun := by
    let o : ℍ := Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b
    have hp := Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.continuous_affinePolarGluiPoint o ρ₀ ρ₁
    have hq : Continuous (fun p : I × Circle =>
        (Quotient.mk'' (gluingPolarPoint o p.2
          ((1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ρ₁)) : (X i).Carrier)) :=
      continuous_quotient_mk'.comp hp
    have hmem : ∀ p : I × Circle,
        (Quotient.mk'' (gluingPolarPoint o p.2
          ((1 - (p.1 : ℝ)) * ρ₀ + (p.1 : ℝ) * ρ₁)) : (X i).Carrier) ∈
          P.componentCenterPuncturedSet i := fun p =>
      (P.twoCenterPolarPoint i b p.2 (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius ρ₀ ρ₁ p.1)
        (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius_pos ρ₀ ρ₁ h₀ h₁ p.1)
        (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius_le ρ₀ ρ₁ (gluingRadius C g) h₀r h₁r p.1)).2
    change Continuous (fun p => (⟨_, hmem p⟩ : P.CenterPuncturedChainComponent i))
    exact hq.subtype_mk hmem
  map_zero_left θ := by
    apply Subtype.ext
    change Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ
        (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius ρ₀ ρ₁ 0)) =
      Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ₀)
    simp [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius]
  map_one_left θ := by
    apply Subtype.ext
    change Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ
        (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius ρ₀ ρ₁ 1)) =
      Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ ρ₁)
    simp [Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.affinePolarRadius]

/-- Reversing an actual affine radius track is exactly the track with its
radii exchanged, at every original polar angle and in the unchanged carrier. -/
theorem twoCenterPolarRadiusHomotopy_evalAt_symm
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ₀ ρ₁ : ℝ) (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀r : ρ₀ ≤ gluingRadius C g) (h₁r : ρ₁ ≤ gluingRadius C g) (θ : Circle) :
    ((P.twoCenterPolarRadiusHomotopy i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r).evalAt θ).symm =
      (P.twoCenterPolarRadiusHomotopy i b ρ₁ ρ₀ h₁ h₀ h₁r h₀r).evalAt θ := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ
      ((1 - (1 - (t : ℝ))) * ρ₀ + (1 - (t : ℝ)) * ρ₁)) =
    Quotient.mk'' (gluingPolarPoint (Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarCenter P i b) θ
      ((1 - (t : ℝ)) * ρ₁ + (t : ℝ) * ρ₀))
  congr 2
  ring

#print axioms twoCenterPolarRadiusHomotopy_evalAt_symm

/-- The homotopy explicitly supplies the path followed by the angle-one
basepoint as the radius varies. -/
def twoCenterPolarRadiusBasepointPath
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ₀ ρ₁ : ℝ) (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀r : ρ₀ ≤ gluingRadius C g) (h₁r : ρ₁ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i b ρ₀ h₀ h₀r 1)
      (P.twoCenterPolarBoundaryMap i b ρ₁ h₁ h₁r 1) :=
  (P.twoCenterPolarRadiusHomotopy i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r).evalAt 1

/-- Transporting the literal small-radius positive polar loop along its
actual angle-one basepoint path gives the literal loop at the larger radius. -/
theorem twoCenterPolarRadiusHomotopy_fundamentalGroup
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ₀ ρ₁ : ℝ) (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀r : ρ₀ ≤ gluingRadius C g) (h₁r : ρ₁ ≤ gluingRadius C g) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (P.twoCenterPolarRadiusBasepointPath i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((circleOneTurnLoop 1).map
          (P.twoCenterPolarBoundaryMap i b ρ₀ h₀ h₀r).continuous))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((circleOneTurnLoop 1).map
          (P.twoCenterPolarBoundaryMap i b ρ₁ h₁ h₁r).continuous)) := by
  let F := P.twoCenterPolarRadiusHomotopy i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r
  let p := (circleOneTurnLoop 1).map (P.twoCenterPolarBoundaryMap i b ρ₀ h₀ h₀r).continuous
  let q := (circleOneTurnLoop 1).map (P.twoCenterPolarBoundaryMap i b ρ₁ h₁ h₁r).continuous
  let γ := P.twoCenterPolarRadiusBasepointPath i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r
  have hhom : (p.trans γ).Homotopic (γ.trans q) := by
    change ((circleOneTurnLoop 1).map (map_continuous _)).trans (F.evalAt 1) |>.Homotopic
      ((F.evalAt 1).trans ((circleOneTurnLoop 1).map (map_continuous _)))
    exact Path.Homotopic.map_trans_evalAt F (circleOneTurnLoop 1)
  have hq : (Path.Homotopic.Quotient.mk (p.trans γ) :
      Path.Homotopic.Quotient _ _) =
      Path.Homotopic.Quotient.mk (γ.trans q) :=
    Path.Homotopic.Quotient.eq.mpr hhom
  have htransport :
      Path.Homotopic.Quotient.mk (γ.symm.trans (p.trans γ)) =
        Path.Homotopic.Quotient.mk q := by
    calc
      Path.Homotopic.Quotient.mk (γ.symm.trans (p.trans γ)) =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk γ.symm)
            (Path.Homotopic.Quotient.mk (p.trans γ)) := rfl
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk γ.symm)
            (Path.Homotopic.Quotient.mk (γ.trans q)) := congrArg _ hq
      _ = Path.Homotopic.Quotient.mk q := by
        rw [Path.Homotopic.Quotient.mk_trans]
        rw [← Path.Homotopic.Quotient.trans_assoc]
        simp only [Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  calc
    FundamentalGroup.fundamentalGroupMulEquivOfPath γ
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.symm.trans (p.trans γ))) := rfl
    _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) :=
      congrArg FundamentalGroup.fromPath htransport

#print axioms Internal.SurfaceTwoCenterPolarRadiusHomotopyHelpers.twoCenterPolarPoint_ne_centers
#print axioms twoCenterPolarPoint
#print axioms twoCenterPolarBoundaryMap
#print axioms twoCenterPolarBoundaryMap_gluingRadius_left
#print axioms twoCenterPolarBoundaryMap_gluingRadius_right
#print axioms twoCenterPolarRadiusHomotopy
#print axioms twoCenterPolarRadiusBasepointPath
#print axioms twoCenterPolarRadiusHomotopy_fundamentalGroup

end
end ExerciseGluingPreparation
end SystolicGrowth
