module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedCoordinatePunctureRetraction
public import Geometry.SurfaceTwoCenterDiskChart
public import Geometry.SurfaceTwoCenterPolarRadiusHomotopy

@[expose] public section

/-!
# Small polar circles in an actual two-center chart

An open set containing both quotient centers contains all sufficiently small
literal polar circles about either center.  The chart specialization places
both such circles inside an actual embedded coordinate disk, while the
existing radius homotopy transports their based classes to the original
gluing-radius peripheral loops in the unchanged punctured component.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem carrier_dist_gluingPolarPoint_center
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

/-- Every open neighborhood of both actual quotient centers contains a
uniform positive-radius family of the actual small circles.  The chosen
radius lies within the gluing disk, so every `twoCenterPolarPoint` here is
defined in the original two-center-punctured component. -/
theorem exists_small_twoCenterPolarRadius_mem_of_isOpen
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {D : Set (X i).Carrier} (hD : IsOpen D)
    (hleft : (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈ D)
    (hright : (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈ D) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ (hρr : ρ ≤ gluingRadius C g),
      ∀ (b : Bool) (θ : Circle) (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ),
        (P.twoCenterPolarPoint i b θ s hs (hsρ.trans hρr)).val ∈ D := by
  let qL : (X i).Carrier := Quotient.mk'' (P.centers i).1
  let qR : (X i).Carrier := Quotient.mk'' (P.centers i).2
  obtain ⟨εL, hεL, hballL⟩ := Metric.isOpen_iff.mp hD qL hleft
  obtain ⟨εR, hεR, hballR⟩ := Metric.isOpen_iff.mp hD qR hright
  let m : ℝ := min (gluingRadius C g) (min εL εR)
  let ρ : ℝ := m / 2
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min P.radius_pos (lt_min hεL hεR)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρr : ρ ≤ gluingRadius C g := by
    dsimp [ρ, m]
    have hmin : min (gluingRadius C g) (min εL εR) ≤ gluingRadius C g :=
      min_le_left _ _
    linarith
  have hρL : ρ < εL := by
    dsimp [ρ, m]
    have hmin : min (gluingRadius C g) (min εL εR) ≤ εL :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hρR' : ρ < εR := by
    dsimp [ρ, m]
    have hmin : min (gluingRadius C g) (min εL εR) ≤ εR :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨ρ, hρ, hρr, ?_⟩
  intro b θ s hs hsρ
  have hsr : s ≤ gluingRadius C g := hsρ.trans hρr
  have hsEmbedded : s < gluingEmbeddedRadius C g :=
    lt_of_le_of_lt hsr P.radius_lt_embeddedRadius
  cases b with
  | false =>
      have hdist := carrier_dist_gluingPolarPoint_center P i (P.centers i).2
        θ hs.le hsEmbedded
      have hball : (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ s) :
          (X i).Carrier) ∈ Metric.ball qR εR := by
        change dist (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ s))
          (Quotient.mk'' (P.centers i).2 : (X i).Carrier) < εR
        rw [hdist]
        exact lt_of_le_of_lt hsρ hρR'
      have hmem := hballR hball
      have hp : (P.twoCenterPolarPoint i false θ s hs hsr).val =
          (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ s) : (X i).Carrier) := rfl
      rw [hp]
      exact hmem
  | true =>
      have hdist := carrier_dist_gluingPolarPoint_center P i (P.centers i).1
        θ hs.le hsEmbedded
      have hball : (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ s) :
          (X i).Carrier) ∈ Metric.ball qL εL := by
        change dist (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ s))
          (Quotient.mk'' (P.centers i).1 : (X i).Carrier) < εL
        rw [hdist]
        exact lt_of_le_of_lt hsρ hρL
      have hmem := hballL hball
      have hp : (P.twoCenterPolarPoint i true θ s hs hsr).val =
          (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ s) : (X i).Carrier) := rfl
      rw [hp]
      exact hmem

/-- The same simultaneous polar-circle containment, with the chosen radius
also required to lie below an independently supplied positive threshold.
This synchronizes disk containment with uniform Fermi-side comparison radii. -/
theorem exists_small_twoCenterPolarRadius_mem_of_isOpen_lt
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {D : Set (X i).Carrier} (hD : IsOpen D)
    (hleft : (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈ D)
    (hright : (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, ∃ _hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      ρ < ε ∧
      ∀ (b : Bool) (θ : Circle) (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ),
        (P.twoCenterPolarPoint i b θ s hs (hsρ.trans hρr)).val ∈ D := by
  obtain ⟨ρ₀, hρ₀, hρ₀r, hmem⟩ :=
    P.exists_small_twoCenterPolarRadius_mem_of_isOpen i hD hleft hright
  let ρ := min ρ₀ (ε / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρ₀ (by linarith)
  have hρr : ρ ≤ gluingRadius C g := (min_le_left _ _).trans hρ₀r
  have hρlt : ρ < ε := by
    have hmin := min_le_right ρ₀ (ε / 2)
    dsimp [ρ] at hmin ⊢
    linarith
  refine ⟨ρ, hρ, hρr, hρlt, ?_⟩
  intro b θ s _hs hsρ
  have hsρ₀ : s ≤ ρ₀ := hsρ.trans (min_le_left _ _)
  exact hmem b θ s _hs hsρ₀

/-- The literal coordinate disk of an open embedding is open in the actual
surface carrier. -/
theorem embeddedCoordinatePunctureDisk_isOpen_of_isOpenEmbedding
    {α : Type*} [TopologicalSpace α] {U : Set ℂ} (_hU : IsOpen U)
    (_hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, α)) (hf : Topology.IsOpenEmbedding (f : U → α)) :
    IsOpen (embeddedCoordinatePunctureDisk f) := by
  rw [embeddedCoordinatePunctureDisk]
  exact hf.isOpenMap _
    (isOpen_Iio.preimage (continuous_norm.comp continuous_subtype_val))

/-- For any actual open-embedding chart containing both centers, a genuine
small-radius pair of polar maps lands in its open coordinate disk.  Their
positive one-turn loops transport, along the actual moving basepoint paths,
to the two original gluing-radius loops in the same punctured component. -/
theorem exists_componentTwoCenterSmallChartPolarCircles
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (_hU : IsOpen U)
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (hleft : (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f)
    (hright : (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ b : Bool,
        FundamentalGroup.fundamentalGroupMulEquivOfPath
            (P.twoCenterPolarRadiusBasepointPath i b ρ (gluingRadius C g)
              hρ P.radius_pos hρr le_rfl)
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              ((circleOneTurnLoop 1).map
                (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous))) =
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              ((circleOneTurnLoop 1).map
                (P.twoCenterPolarBoundaryMap i b (gluingRadius C g)
                  P.radius_pos le_rfl).continuous))) := by
  have hD := embeddedCoordinatePunctureDisk_isOpen_of_isOpenEmbedding
    _hU hball f hf
  obtain ⟨ρ, hρ, hρr, hmem⟩ :=
    P.exists_small_twoCenterPolarRadius_mem_of_isOpen i hD hleft hright
  refine ⟨ρ, hρ, hρr, ?_, ?_⟩
  · intro b θ
    have hpoint := hmem b θ ρ hρ le_rfl
    have hval : (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val =
        (P.twoCenterPolarPoint i b θ ρ hρ hρr).val := rfl
    rw [hval]
    exact hpoint
  · intro b
    exact P.twoCenterPolarRadiusHomotopy_fundamentalGroup i b ρ
      (gluingRadius C g) hρ P.radius_pos hρr le_rfl

/-- The chart-contained polar circles can be chosen below any positive
comparison threshold while retaining their original-radius homotopies. -/
theorem exists_componentTwoCenterSmallChartPolarCircles_below
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (_hU : IsOpen U)
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (hleft : (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f)
    (hright : (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      ρ < ε ∧
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ b : Bool,
        FundamentalGroup.fundamentalGroupMulEquivOfPath
            (P.twoCenterPolarRadiusBasepointPath i b ρ (gluingRadius C g)
              hρ P.radius_pos hρr le_rfl)
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              ((circleOneTurnLoop 1).map
                (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous))) =
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              ((circleOneTurnLoop 1).map
                (P.twoCenterPolarBoundaryMap i b (gluingRadius C g)
                  P.radius_pos le_rfl).continuous))) := by
  have hD := embeddedCoordinatePunctureDisk_isOpen_of_isOpenEmbedding
    _hU hball f hf
  obtain ⟨ρ, hρ, hρr, hρlt, hmem⟩ :=
    P.exists_small_twoCenterPolarRadius_mem_of_isOpen_lt i hD hleft hright ε hε
  refine ⟨ρ, hρ, hρr, hρlt, ?_, ?_⟩
  · intro b θ
    have hpoint := hmem b θ ρ hρ le_rfl
    have hval : (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val =
        (P.twoCenterPolarPoint i b θ ρ hρ hρr).val := rfl
    rw [hval]
    exact hpoint
  · intro b
    exact P.twoCenterPolarRadiusHomotopy_fundamentalGroup i b ρ
      (gluingRadius C g) hρ P.radius_pos hρr le_rfl

end
end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_small_twoCenterPolarRadius_mem_of_isOpen
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_small_twoCenterPolarRadius_mem_of_isOpen_lt
#print axioms SystolicGrowth.ExerciseGluingPreparation.embeddedCoordinatePunctureDisk_isOpen_of_isOpenEmbedding
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterSmallChartPolarCircles
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterSmallChartPolarCircles_below
