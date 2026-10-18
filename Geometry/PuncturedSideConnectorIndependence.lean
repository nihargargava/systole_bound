module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterConvexSidePolarComparison

@[expose] public section

/-!
# Connector-independent positive generators in a punctured side

The side fundamental group is cyclic, so changing the path used to conjugate
a loop does not change its based class. This lets the actual Fermi positive
turn be compared along the original cut halves, rather than only along a
radial choice.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

/-- The free group on one generator is commutative, by its actual integer
equivalence. -/
private theorem freeGroupUnit_mul_comm (a b : FreeGroup Unit) : a * b = b * a := by
  apply FreeGroup.mulEquivIntOfUnique.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

/-- The actual punctured convex-side fundamental group is commutative under
its circle and one-generator free markings. -/
theorem puncturedBaseFundamentalGroup_commutative
    (B : Set ℂ) (c : ℂ) (ℓ : ℝ) (hB : Convex ℝ B) (hℓ : 0 < ℓ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (z : puncturedBaseAt B c) (a b : FundamentalGroup (puncturedBaseAt B c) z) :
    a * b = b * a := by
  let θ := puncturedBaseCircleRetraction B c z
  let E := (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z).trans
    (circleFundamentalGroupFreeEquiv θ)
  apply E.injective
  calc
    E (a * b) = E a * E b := map_mul E a b
    _ = E b * E a := freeGroupUnit_mul_comm (E a) (E b)
    _ = E (b * a) := (map_mul E b a).symm

/-- In a commutative based fundamental group, conjugating the same literal
loop along two paths with common endpoints gives the same based class. -/
theorem pathConjugateLoop_eq_of_commutative
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (hcomm : ∀ a b : FundamentalGroup Y x, a * b = b * a)
    (p q : Path x y) (γ : Path y y) :
    Path.Homotopic.Quotient.mk (p.trans (γ.trans p.symm)) =
      Path.Homotopic.Quotient.mk (q.trans (γ.trans q.symm)) := by
  let r : Path x x := p.trans q.symm
  let rclass : FundamentalGroup Y x := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk r)
  let qclass : FundamentalGroup Y x := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (q.trans (γ.trans q.symm)))
  have hconj : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (p.trans (γ.trans p.symm))) =
        rclass⁻¹ * qclass * rclass := by
    rw [FundamentalGroup.inv_def, FundamentalGroup.mul_def,
      FundamentalGroup.mul_def]
    dsimp [rclass, qclass, r]
    change Path.Homotopic.Quotient.mk (p.trans (γ.trans p.symm)) =
      (Path.Homotopic.Quotient.mk (p.trans q.symm)).trans
        ((Path.Homotopic.Quotient.mk (q.trans (γ.trans q.symm))).trans
          (Path.Homotopic.Quotient.mk (p.trans q.symm)).symm)
    rw [← Path.Homotopic.Quotient.mk_symm,
      Path.trans_symm, Path.symm_symm]
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc
        (Path.Homotopic.Quotient.mk q.symm)
        (Path.Homotopic.Quotient.mk q),
      ← Path.Homotopic.Quotient.trans_assoc
        (Path.Homotopic.Quotient.mk q.symm)
        (Path.Homotopic.Quotient.mk q)]
    simp only [Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  calc
    Path.Homotopic.Quotient.mk (p.trans (γ.trans p.symm)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (p.trans (γ.trans p.symm))) := rfl
    _ = rclass⁻¹ * qclass * rclass := hconj
    _ = (qclass * rclass⁻¹) * rclass := by rw [hcomm rclass⁻¹ qclass]
    _ = qclass := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = Path.Homotopic.Quotient.mk (q.trans (γ.trans q.symm)) := rfl

/-- Rebase a positive circle turn along the concrete Circle path, then map it
into any actual continuous target. -/
private theorem mapped_circleOneTurn_conjugate_eq
    {Y : Type*} [TopologicalSpace Y] (F : C(Circle, Y)) (θ φ : Circle) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (((Circle.path θ φ).map F.continuous).trans
          (((circleOneTurnLoop φ).map F.continuous).trans
            ((Circle.path θ φ).map F.continuous).symm))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((circleOneTurnLoop θ).map F.continuous)) := by
  let cpath := Circle.path θ φ
  let spath := cpath.map F.continuous
  let Lθ := (circleOneTurnLoop θ).map F.continuous
  let Lφ := (circleOneTurnLoop φ).map F.continuous
  have hreb : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (cpath.trans ((circleOneTurnLoop φ).trans cpath.symm))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleOneTurnLoop θ)) := by
    apply (FundamentalGroup.fundamentalGroupMulEquivOfPath cpath).injective
    change FundamentalGroup.fundamentalGroupMulEquivOfPath cpath
      ⟦cpath.trans ((circleOneTurnLoop φ).trans cpath.symm)⟧ =
        FundamentalGroup.fundamentalGroupMulEquivOfPath cpath
          ⟦circleOneTurnLoop θ⟧
    rw [fundamentalGroupMulEquivOfPath_conjugate_apply,
      circleOneTurnLoop_rebase_circlePath]
  have hmap : ((cpath.trans ((circleOneTurnLoop φ).trans cpath.symm)).map
      F.continuous).Homotopic ((circleOneTurnLoop θ).map F.continuous) :=
    Path.Homotopic.map (Path.Homotopic.Quotient.eq.mp hreb) F
  have hpath : (cpath.trans ((circleOneTurnLoop φ).trans cpath.symm)).map
      F.continuous = spath.trans (Lφ.trans spath.symm) := by
    simp [spath, Lφ, Path.map_trans, Path.map_symm]
  rw [← hpath]
  exact Path.Homotopic.Quotient.eq.mpr hmap

/-- For an arbitrary Circle angle and any literal path from the chosen side
basepoint to that Fermi point, the conjugated Fermi positive turn is the
positive generator of the actual punctured-side marking. -/
theorem translatedFermiPositivePolarCoordinateBasedFreeGenerator_of_connector
    (B : Set ℂ) (c : ℂ) (hB : Convex ℝ B) (ℓ ρ δ : ℝ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ℓ • (θ : ℂ) ∈ B)
    (hball : Metric.ball c δ ⊆ B)
    (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * c.im) a b ha hb ρ θ‖ < δ)
    (z : puncturedBaseAt B c) (φ : Circle)
    (p : Path z
      (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq φ)) :
    let θ := puncturedBaseCircleRetraction B c z
    let E := (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z).trans
      (circleFundamentalGroupFreeEquiv θ)
    let F := translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq
    E ⟦p.trans (((circleOneTurnLoop φ).map F.continuous).trans p.symm)⟧ =
      FreeGroup.of () := by
  let θ := puncturedBaseCircleRetraction B c z
  let E := (puncturedBaseCircleFundamentalGroupEquiv B c ℓ hB hℓ hcircle z).trans
    (circleFundamentalGroupFreeEquiv θ)
  let F := translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq
  let t := puncturedBaseCircleActualTrack B c ℓ hB hℓ hcircle z
  let H := translatedFermiPositivePolarCoordinateHomotopy_convex B c hB m a b
    ha hb ℓ ρ δ hℓ hρ hcircle hball hq
  let p₀ := t.trans (H.evalAt θ)
  let L₀ := (circleOneTurnLoop θ).map F.continuous
  let Lφ := (circleOneTurnLoop φ).map F.continuous
  let s := (Circle.path θ φ).map F.continuous
  let q := p₀.trans s
  have hbase : E ⟦p₀.trans (L₀.trans p₀.symm)⟧ = FreeGroup.of () := by
    simpa only [E, θ, F, p₀, L₀, t, H] using
      translatedFermiPositivePolarCoordinateBasedFreeGenerator
        B c hB ℓ ρ δ hℓ hρ hcircle hball m a b ha hb hq z
  have hcircleLoop : Path.Homotopic.Quotient.mk (s.trans (Lφ.trans s.symm)) =
      Path.Homotopic.Quotient.mk L₀ := by
    dsimp [s, Lφ, L₀, F]
    exact mapped_circleOneTurn_conjugate_eq
      (translatedFermiPositivePolarCoordinateMap B c m a b ha hb ρ δ hρ hball hq)
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
  have hcomm : ∀ a b : FundamentalGroup (puncturedBaseAt B c) z, a * b = b * a :=
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

#print axioms pathConjugateLoop_eq_of_commutative
#print axioms translatedFermiPositivePolarCoordinateBasedFreeGenerator_of_connector

end

end SystolicGrowth
