module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterLocalPolarComparison
public import Geometry.SurfaceTwoCenterDiskPolarPaths

@[expose] public section

/-!
# Actual polar maps in the two-center Fermi chart

The chart's translated positive polar maps are literally the original
two-center polar maps after forgetting subtype proofs. The second center uses
the selected deck translate and its exact unit phase.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)} {U : Set ℂ}

theorem twoCenterPolarRadius_lt_systole
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρr : ρ ≤ gluingRadius C g) :
    2 * ρ < (X i).systole := by
  have hR : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  nlinarith

/-- At the left chart center, the literal translated Fermi side polar map
forgets to the original left polar map on the native two-center carrier. -/
theorem translatedFermiSideOriginalPolarMap_left_twoCenterPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (B : Set ℂ) (p q : U)
    (hBU : B ⊆ U) (hpB : p.1 ∈ B) (hqU : q.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ q.1)
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hpRe : p.1.re = 0)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball p.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δ)
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (θ : Circle) :
    ((translatedFermiSideOriginalPolarMap B p.1 q.1 hBU hpB hqU hBother
      f hf γ m a b ha hb hformula hpRe ρ δ hρ
      (P.twoCenterPolarRadius_lt_systole i ρ hρr)
      hball hqball θ).1 : (X i).Carrier) =
      (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ).val := by
  have hsys := P.twoCenterPolarRadius_lt_systole i ρ hρr
  rw [translatedFermiSideOriginalPolarMap_coe B p.1 q.1 hBU hpB hqU
    hBother f hf γ m a b ha hb hformula hpRe ρ δ hρ hsys hball hqball θ]
  rw [hleft, ClosedHyperbolicSurface.dirichletPuncturePolarCircle_coe]
  change Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ) =
    Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ ρ)
  rfl

/-- At the right chart center, the literal translated Fermi side polar map
with the actual deck phase forgets to the original right polar map. -/
theorem translatedFermiSideOriginalPolarMap_right_twoCenterPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (B : Set ℂ) (p q : U)
    (hBU : B ⊆ U) (hqB : q.1 ∈ B) (hpU : p.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ p.1)
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hqRe : q.1.re = 0)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball q.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δ)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (φ : Circle) :
    ((translatedFermiSideOriginalPolarMap B q.1 p.1 hBU hqB hpU hBother
      f hf γ m a b ha hb hformula hqRe ρ δ hρ
      (P.twoCenterPolarRadius_lt_systole i ρ hρr)
      hball hqball
      (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * φ)).1 :
        (X i).Carrier) =
      (P.twoCenterPolarBoundaryMap i false ρ hρ hρr φ).val := by
  have hsys := P.twoCenterPolarRadius_lt_systole i ρ hρr
  rw [translatedFermiSideOriginalPolarMap_coe B q.1 p.1 hBU hqB hpU
    hBother f hf γ m a b ha hb hformula hqRe ρ δ hρ hsys hball hqball
    (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * φ)]
  rw [hright, ClosedHyperbolicSurface.dirichletPuncturePolarCircle_coe]
  let w := gluingPolarPoint (P.centers i).2 φ ρ
  have hpolar : P.componentCenterClosestDeck i • w =
      gluingPolarPoint (P.componentCenterClosestDeck i • (P.centers i).2)
        (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * φ) ρ :=
    gluingPolarPoint_smul (↑(P.componentCenterClosestDeck i)) (P.centers i).2 φ ρ
  have hproj : (Quotient.mk'' (P.componentCenterClosestDeck i • w) :
      (X i).Carrier) = Quotient.mk'' w := by
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨P.componentCenterClosestDeck i, rfl⟩)
  calc
    _ = Quotient.mk'' (P.componentCenterClosestDeck i • w) :=
      congrArg Quotient.mk'' hpolar.symm
    _ = Quotient.mk'' w := hproj
    _ = (P.twoCenterPolarBoundaryMap i false ρ hρ hρr φ).val := rfl

/-- The original two-puncture carrier embeds into the chart's literal ambient
carrier whenever the two quotient punctures agree. -/
def originalTwoCenterPuncturedToAmbientMap
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (p q : U) (o₁ o₂ : ℍ)
    (h₁ : (Quotient.mk'' o₁ : X.Carrier) = f p)
    (h₂ : (Quotient.mk'' o₂ : X.Carrier) = f q) :
    C(OriginalTwoCenterPuncturedCarrier X o₁ o₂,
      embeddedTwoPunctureAmbientPoint f p q) where
  toFun z := ⟨z.1, by
    change z.1 ≠ f p ∧ z.1 ≠ f q
    exact ⟨fun hz => z.2.1 (hz.trans h₁.symm),
      fun hz => z.2.2 (hz.trans h₂.symm)⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun z => by
    change z.1 ≠ f p ∧ z.1 ≠ f q
    exact ⟨fun hz => z.2.1 (hz.trans h₁.symm),
      fun hz => z.2.2 (hz.trans h₂.symm)⟩)

@[simp]
theorem originalTwoCenterPuncturedToAmbientMap_apply_val
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (p q : U) (o₁ o₂ : ℍ)
    (h₁ : (Quotient.mk'' o₁ : X.Carrier) = f p)
    (h₂ : (Quotient.mk'' o₂ : X.Carrier) = f q)
    (z : OriginalTwoCenterPuncturedCarrier X o₁ o₂) :
    (originalTwoCenterPuncturedToAmbientMap f p q o₁ o₂ h₁ h₂ z).1 = z.1 := rfl

/-- Reorder the two puncture proofs without changing the underlying point. -/
def Internal.SurfaceTwoCenterChartPolarIdentityHelpers.originalTwoCenterPuncturedSwapMap
    {g : ℕ} {X : ClosedHyperbolicSurface g} (o₁ o₂ : ℍ) :
    C(OriginalTwoCenterPuncturedCarrier X o₂ o₁,
      OriginalTwoCenterPuncturedCarrier X o₁ o₂) where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun z =>
    ⟨z.2.2, z.2.1⟩)

@[simp]
private theorem originalTwoCenterPuncturedSwapMap_apply_val
    {g : ℕ} {X : ClosedHyperbolicSurface g} (o₁ o₂ : ℍ)
    (z : OriginalTwoCenterPuncturedCarrier X o₂ o₁) :
    (Internal.SurfaceTwoCenterChartPolarIdentityHelpers.originalTwoCenterPuncturedSwapMap o₁ o₂ z).1 = z.1 := rfl

theorem translatedFermiSidePuncturePoints_eq_chartPoints
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ)
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2) :
    (Quotient.mk'' (γ • orientedFermiDiskPoint m a b p.1) : (X i).Carrier) = f p ∧
      (Quotient.mk'' (γ • orientedFermiDiskPoint m a b q.1) : (X i).Carrier) = f q := by
  constructor
  · rw [hleft]
    exact hp.symm
  · rw [hright]
    calc
      (Quotient.mk'' (P.componentCenterClosestDeck i • (P.centers i).2) :
        (X i).Carrier) = Quotient.mk'' (P.centers i).2 := by
          apply Quotient.sound
          exact MulAction.orbitRel_apply.mpr
            (MulAction.mem_orbit_iff.mpr ⟨P.componentCenterClosestDeck i, rfl⟩)
      _ = f q := hq.symm

/-- The actual left translated Fermi polar circle, now in the chart's actual
two-puncture ambient subtype. -/
noncomputable def translatedFermiSideOriginalPolarMap_left_ambient
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (B : Set ℂ) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hBU : B ⊆ U) (hpB : p.1 ∈ B) (hqU : q.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ q.1)
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hpRe : p.1.re = 0)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball p.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δ)
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2) :
    C(Circle, embeddedTwoPunctureAmbientPoint f p q) := by
  let hc := P.translatedFermiSidePuncturePoints_eq_chartPoints i f p q hp hq
    γ m a b hleft hright
  exact (originalTwoCenterPuncturedToAmbientMap f p q
      (γ • orientedFermiDiskPoint m a b p.1)
      (γ • orientedFermiDiskPoint m a b q.1) hc.1 hc.2).comp
    (translatedFermiSideOriginalPolarMap B p.1 q.1 hBU hpB hqU hBother
      f hf γ m a b ha hb hformula hpRe ρ δ hρ
      (P.twoCenterPolarRadius_lt_systole i ρ hρr) hball hqball)

/-- The actual right translated Fermi polar circle is put in the same
ambient subtype, with its original phase parameter multiplied by the exact
selected-deck phase. -/
noncomputable def translatedFermiSideOriginalPolarMap_right_ambient
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (B : Set ℂ) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hBU : B ⊆ U) (hqB : q.1 ∈ B) (hpU : p.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ p.1)
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hqRe : q.1.re = 0)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball q.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δ)
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2) :
    C(Circle, embeddedTwoPunctureAmbientPoint f p q) := by
  let hc := P.translatedFermiSidePuncturePoints_eq_chartPoints i f p q hp hq
    γ m a b hleft hright
  exact (originalTwoCenterPuncturedToAmbientMap f p q
      (γ • orientedFermiDiskPoint m a b p.1)
      (γ • orientedFermiDiskPoint m a b q.1) hc.1 hc.2).comp
    ((Internal.SurfaceTwoCenterChartPolarIdentityHelpers.originalTwoCenterPuncturedSwapMap
        (γ • orientedFermiDiskPoint m a b p.1)
        (γ • orientedFermiDiskPoint m a b q.1)).comp
      ((translatedFermiSideOriginalPolarMap B q.1 p.1 hBU hqB hpU hBother
        f hf γ m a b ha hb hformula hqRe ρ δ hρ
        (P.twoCenterPolarRadius_lt_systole i ρ hρr) hball hqball).comp
          ⟨fun φ => gluingPolarSLPhase (P.componentCenterClosestDeck i)
              (P.centers i).2 * φ,
            continuous_const.mul continuous_id⟩))

/-! The following two diagrams use the actual ambient-to-native inclusion.
Their proofs reduce to the checked point identities above; all subtype
membership proofs are transported from the exact chart center equations. -/

theorem translatedFermiSideOriginalPolarMap_left_nativeContinuousMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (B : Set ℂ) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hBU : B ⊆ U) (hpB : p.1 ∈ B) (hqU : q.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ q.1)
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hpRe : p.1.re = 0)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball p.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δ)
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2) :
    (P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
      (P.translatedFermiSideOriginalPolarMap_left_ambient i f B p q hp hq
        hBU hpB hqU hBother hf γ m a b ha hb hformula hpRe
        ρ δ hρ hρr hball hqball hleft hright) =
      P.twoCenterPolarBoundaryMap i true ρ hρ hρr := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  change ((translatedFermiSideOriginalPolarMap B p.1 q.1 hBU hpB hqU hBother
    f hf γ m a b ha hb hformula hpRe ρ δ hρ
    (P.twoCenterPolarRadius_lt_systole i ρ hρr) hball hqball θ).1 :
      (X i).Carrier) = (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ).val
  exact P.translatedFermiSideOriginalPolarMap_left_twoCenterPolarBoundaryMap
    i f B p q hBU hpB hqU hBother hf γ m a b ha hb hformula hpRe
    ρ δ hρ hρr hball hqball hleft θ

theorem translatedFermiSideOriginalPolarMap_right_nativeContinuousMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (B : Set ℂ) (p q : U)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hBU : B ⊆ U) (hqB : q.1 ∈ B) (hpU : p.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ p.1)
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hqRe : q.1.re = 0)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball q.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δ)
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2) :
    (P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
      (P.translatedFermiSideOriginalPolarMap_right_ambient i f B p q hp hq
        hBU hqB hpU hBother hf γ m a b ha hb hformula hqRe
        ρ δ hρ hρr hball hqball hleft hright) =
      P.twoCenterPolarBoundaryMap i false ρ hρ hρr := by
  apply ContinuousMap.ext
  intro φ
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, twoCenterAmbientToNativeComponent]
  change ((translatedFermiSideOriginalPolarMap B q.1 p.1 hBU hqB hpU hBother
    f hf γ m a b ha hb hformula hqRe ρ δ hρ
    (P.twoCenterPolarRadius_lt_systole i ρ hρr) hball hqball
    (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * φ)).1 :
      (X i).Carrier) = (P.twoCenterPolarBoundaryMap i false ρ hρ hρr φ).val
  exact P.translatedFermiSideOriginalPolarMap_right_twoCenterPolarBoundaryMap
    i f B p q hBU hqB hpU hBother hf γ m a b ha hb hformula hqRe
    ρ δ hρ hρr hball hqball hright φ

/-- An exact continuous-map triangle also identifies the included based
positive one-turn loop and the induced fundamental-group class. The path
cast records the endpoint equality supplied by the triangle. -/
theorem circleOneTurn_inclusion_map_and_fundamentalGroup
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (T : C(Circle, α)) (N : C(α, β)) (R : C(Circle, β))
    (hmap : N.comp T = R) :
    let hbase := congrArg (fun F : C(Circle, β) => F 1) hmap
    (((circleOneTurnLoop 1).map T.continuous).map N.continuous).cast
        hbase.symm hbase.symm = (circleOneTurnLoop 1).map R.continuous ∧
      FundamentalGroup.mapOfEq N hbase
        (Path.Homotopic.Quotient.mk
          ((circleOneTurnLoop 1).map T.continuous)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((circleOneTurnLoop 1).map R.continuous)) := by
  dsimp only
  let hbase := congrArg (fun F : C(Circle, β) => F 1) hmap
  have hloop :
      (((circleOneTurnLoop 1).map T.continuous).map N.continuous).cast
        hbase.symm hbase.symm = (circleOneTurnLoop 1).map R.continuous := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact congrArg (fun F : C(Circle, β) => F (circleOneTurnLoop 1 t)) hmap
  refine ⟨hloop, ?_⟩
  conv_lhs =>
    rw [FundamentalGroup.mapOfEq_apply,
      ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast]
  exact congrArg Path.Homotopic.Quotient.mk hloop

#print axioms originalTwoCenterPuncturedToAmbientMap
#print axioms translatedFermiSideOriginalPolarMap_left_ambient
#print axioms translatedFermiSideOriginalPolarMap_right_ambient
#print axioms translatedFermiSideOriginalPolarMap_left_nativeContinuousMap
#print axioms translatedFermiSideOriginalPolarMap_right_nativeContinuousMap
#print axioms circleOneTurn_inclusion_map_and_fundamentalGroup

#print axioms translatedFermiSideOriginalPolarMap_left_twoCenterPolarBoundaryMap
#print axioms translatedFermiSideOriginalPolarMap_right_twoCenterPolarBoundaryMap

end
end ExerciseGluingPreparation
end SystolicGrowth
