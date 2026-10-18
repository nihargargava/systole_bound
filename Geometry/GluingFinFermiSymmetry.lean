module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingFinFermiCoordinates
public import Geometry.GluingCircleTransport

@[expose] public section

/-!
# Reflection symmetry for the finite Fermi fins

Reflection in the imaginary axis preserves the radial Fermi coordinate and
negates the transverse coordinate. It converts lower fins into the upper fins
whose bounded-window geodesic convexity is already established.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- The imaginary-axis reflection leaves the radial Fermi coordinate fixed. -/
theorem gluingFinFermiRadialCoord_mirror (α : ℝ) (z : ℍ) :
    gluingFinFermiRadialCoord α (gluingMirror z) =
      gluingFinFermiRadialCoord α z := by
  unfold gluingFinFermiRadialCoord
  have hnorm : ‖(gluingMirror z : ℂ)‖ = ‖(z : ℂ)‖ := by
    have hsq (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      ring
    have hsqeq : ‖(gluingMirror z : ℂ)‖ ^ 2 = ‖(z : ℂ)‖ ^ 2 := by
      rw [hsq, hsq, gluingMirror_re, gluingMirror_im]
      ring
    nlinarith [norm_nonneg (gluingMirror z : ℂ), norm_nonneg (z : ℂ)]
  rw [hnorm]

/-- The imaginary-axis reflection negates the transverse Fermi coordinate. -/
theorem gluingFinFermiTransverseCoord_mirror (α : ℝ) (z : ℍ) :
    gluingFinFermiTransverseCoord α (gluingMirror z) =
      -gluingFinFermiTransverseCoord α z := by
  rw [gluingFinFermiTransverseCoord, gluingFinFermiTransverseCoord]
  rw [gluingMirror_re, gluingMirror_im]
  rw [show -z.re / z.im = -(z.re / z.im) by ring, Real.arsinh_neg]
  ring

/-- Reflection commutes with the constant-speed geodesic interpolation on its
segment. The identity follows from uniqueness of a point on a geodesic segment
at a prescribed distance from its initial endpoint, so it applies to the
actual upper-half-plane reflection rather than a coordinate-level guess. -/
theorem gluingMirror_geodInterp {a b : ℍ} {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    gluingMirror (Vendored.RiemannDynamics.geodInterp a b s) =
      Vendored.RiemannDynamics.geodInterp (gluingMirror a) (gluingMirror b) s := by
  let ma := gluingMirror a
  let mb := gluingMirror b
  let x := gluingMirror (Vendored.RiemannDynamics.geodInterp a b s)
  let y := Vendored.RiemannDynamics.geodInterp ma mb s
  have hx : x ∈ Vendored.RiemannDynamics.geodSeg ma mb := by
    have hseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b hs
    rw [Vendored.RiemannDynamics.mem_geodSeg] at hseg
    change dist a (Vendored.RiemannDynamics.geodInterp a b s) +
        dist (Vendored.RiemannDynamics.geodInterp a b s) b = dist a b at hseg
    rw [Vendored.RiemannDynamics.mem_geodSeg]
    change dist (gluingMirror a) (gluingMirror
        (Vendored.RiemannDynamics.geodInterp a b s)) +
      dist (gluingMirror (Vendored.RiemannDynamics.geodInterp a b s))
        (gluingMirror b) =
      dist (gluingMirror a) (gluingMirror b)
    calc
      _ = dist a (Vendored.RiemannDynamics.geodInterp a b s) +
          dist (Vendored.RiemannDynamics.geodInterp a b s) b := by
        rw [gluingMirror_isometry.dist_eq, gluingMirror_isometry.dist_eq]
      _ = dist a b := hseg
      _ = dist (gluingMirror a) (gluingMirror b) :=
        (gluingMirror_isometry.dist_eq a b).symm
  have hy : y ∈ Vendored.RiemannDynamics.geodSeg ma mb :=
    Vendored.RiemannDynamics.geodInterp_mem_geodSeg ma mb hs
  have hdist : dist ma x = dist ma y := by
    calc
      dist ma x = dist a (Vendored.RiemannDynamics.geodInterp a b s) :=
        gluingMirror_isometry.dist_eq a (Vendored.RiemannDynamics.geodInterp a b s)
      _ = s * dist a b := Vendored.RiemannDynamics.dist_geodInterp_left a b hs
      _ = s * dist ma mb := by rw [gluingMirror_isometry.dist_eq]
      _ = dist ma y :=
        (Vendored.RiemannDynamics.dist_geodInterp_left ma mb hs).symm
  exact Vendored.RiemannDynamics.eq_of_mem_geodSeg_of_dist_eq hx hy hdist

/-- On a fixed radial window, all sufficiently fine dyadic lower fins are
geodesically convex. Reflection converts the lower endpoint inequalities to
the proved upper-fin inequalities and carries the entire interpolating segment
to its reflected segment. -/
theorem eventually_gluingFinFermi_lowerFin_geodInterp
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ a b : ℍ,
      gluingFinFermiRadialCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a ∈ Set.Icc (-R) R →
      gluingFinFermiRadialCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b ∈ Set.Icc (-R) R →
      gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a ≤
        -((1 / 2 : ℝ) ^ n) * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a) →
      gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b ≤
        -((1 / 2 : ℝ) ^ n) * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b) →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gluingFinFermiTransverseCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
            (Vendored.RiemannDynamics.geodInterp a b s) ≤
          -((1 / 2 : ℝ) ^ n) * gluingCollarWarp r
            (gluingFinFermiRadialCoord
              (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
              (Vendored.RiemannDynamics.geodInterp a b s)) := by
  obtain ⟨N, hN2, hupper⟩ := eventually_gluingFinFermi_upperFin_geodInterp hr hR
  refine ⟨N, hN2, fun n hn a b ha hb hA hB s hs => ?_⟩
  let α : ℝ := Real.sqrt (1 - (1 / 2 : ℝ) ^ n)
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  have hn2 : 2 ≤ n := hN2.trans hn
  have hα : 0 < α := by
    dsimp [α]
    apply Real.sqrt_pos.2
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    norm_num at hpow
    nlinarith
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hma : gluingFinFermiRadialCoord α (gluingMirror a) ∈ Set.Icc (-R) R := by
    simpa [α, gluingFinFermiRadialCoord_mirror] using ha
  have hmb : gluingFinFermiRadialCoord α (gluingMirror b) ∈ Set.Icc (-R) R := by
    simpa [α, gluingFinFermiRadialCoord_mirror] using hb
  have hA' : ε * gluingCollarWarp r
      (gluingFinFermiRadialCoord α (gluingMirror a)) ≤
      gluingFinFermiTransverseCoord α (gluingMirror a) := by
    rw [gluingFinFermiRadialCoord_mirror, gluingFinFermiTransverseCoord_mirror]
    dsimp [ε, α] at hA ⊢
    linarith
  have hB' : ε * gluingCollarWarp r
      (gluingFinFermiRadialCoord α (gluingMirror b)) ≤
      gluingFinFermiTransverseCoord α (gluingMirror b) := by
    rw [gluingFinFermiRadialCoord_mirror, gluingFinFermiTransverseCoord_mirror]
    dsimp [ε, α] at hB ⊢
    linarith
  have hmid := hupper n hn (gluingMirror a) (gluingMirror b) hma hmb hA' hB' s hs
  rw [← gluingMirror_geodInterp hs, gluingFinFermiRadialCoord_mirror,
    gluingFinFermiTransverseCoord_mirror] at hmid
  have hmid' : (1 / 2 : ℝ) ^ n *
      gluingCollarWarp r
        (gluingFinFermiRadialCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
          (Vendored.RiemannDynamics.geodInterp a b s)) ≤
      -gluingFinFermiTransverseCoord
        (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
        (Vendored.RiemannDynamics.geodInterp a b s) := by
    simpa [ε, α] using hmid
  linarith

#print axioms gluingFinFermiRadialCoord_mirror
#print axioms gluingFinFermiTransverseCoord_mirror
#print axioms gluingMirror_geodInterp
#print axioms eventually_gluingFinFermi_lowerFin_geodInterp

end SystolicGrowth
