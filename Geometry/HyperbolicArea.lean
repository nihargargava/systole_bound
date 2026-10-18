module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Core.SystolicCore

@[expose] public section

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth

/-! ## Hyperbolic area

This file collects measure-theoretic facts about the Poincaré upper half-plane
needed by the geometric part of the systolic-growth argument.
-/

/-- Hyperbolic area is invariant under the orientation-preserving isometry
group.  Mathlib proves the stronger statement for `GL(2, ℝ)`; this instance
restricts it to the `SL(2, ℝ)` action used for deck transformations. -/
instance : SMulInvariantMeasure SL(2, ℝ) ℍ volume := by
  constructor
  intro g s hs
  simpa only [MulAction.compHom_smul_def] using
    (SMulInvariantMeasure.measure_preimage_smul (M := GL (Fin 2) ℝ)
      (Matrix.SpecialLinearGroup.mapGL ℝ g) hs)

/-- Hyperbolic balls with the same radius have the same area, independently of
their center. -/
theorem volume_ball_eq_volume_ball_I (z : ℍ) (r : ℝ) :
    volume (Metric.ball z r) = volume (Metric.ball (I : ℍ) r) := by
  let g : SL(2, ℝ) := z.toSL2R
  have hball : g • Metric.ball (I : ℍ) r = Metric.ball z r := by
    rw [Metric.smul_ball, show g • (I : ℍ) = z by
      simp [g]]
  rw [← hball, measure_smul]

/-- Hyperbolic balls of a fixed radius have center-independent area. -/
theorem volume_ball_eq (z w : ℍ) (r : ℝ) :
    volume (Metric.ball z r) = volume (Metric.ball w r) := by
  exact (volume_ball_eq_volume_ball_I z r).trans
    (volume_ball_eq_volume_ball_I w r).symm

/-- A ball of radius less than half the systole embeds in the orbit-space
quotient.  This is the metric input used when packing disks in a closed
hyperbolic surface. -/
theorem quotientMk_injOn_ball {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r : ℝ) (hr : 2 * r < X.systole) :
    Set.InjOn
      (fun z : ℍ ↦ (Quotient.mk'' z : X.Carrier))
      (Metric.ball o r) := by
  intro z hz w hw hquot
  have horbit : z ∈ MulAction.orbit X.deckGroup w :=
    Quotient.exact hquot
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp horbit
  by_cases hγone : γ = 1
  · subst γ
    simpa using hγ.symm
  · have hsys : X.systole ≤ dist w z := by
      simpa [hγ] using X.systole_le_displacement γ hγone w
    have hw' : dist w o < r := Metric.mem_ball.mp hw
    have hz' : dist z o < r := Metric.mem_ball.mp hz
    have hwz : dist w z < 2 * r := calc
      dist w z ≤ dist w o + dist o z := dist_triangle _ _ _
      _ = dist w o + dist z o := by rw [dist_comm o z]
      _ < r + r := add_lt_add hw' hz'
      _ = 2 * r := by ring
    exfalso
    exact (not_lt_of_ge (hr.trans_le hsys).le) hwz

/-- Distinct deck translates of a ball of radius less than half the systole
are disjoint. -/
theorem disjoint_smul_ball {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r : ℝ) (hr : 2 * r < X.systole)
    (γ : X.deckGroup) (hγ : γ ≠ 1) :
    Disjoint (γ • Metric.ball o r) (Metric.ball o r) := by
  rw [Metric.smul_ball, Set.disjoint_left]
  intro z hzγ hz
  have hzo : dist z o < r := Metric.mem_ball.mp hz
  have hzγo : dist z (γ • o) < r := Metric.mem_ball.mp hzγ
  have hdisplacement : dist o (γ • o) < 2 * r := calc
    dist o (γ • o) ≤ dist o z + dist z (γ • o) := dist_triangle _ _ _
    _ < r + r := add_lt_add (by simpa [dist_comm] using hzo) hzγo
    _ = 2 * r := by ring
  have hsys := X.systole_le_displacement γ hγ o
  exact (not_lt_of_ge (hr.trans_le hsys).le) hdisplacement

/-- The same disjointness remains valid at the closed half-systole radius:
open balls have strict pointwise inequalities, so equality in the radius
bound still yields a contradiction. -/
theorem disjoint_smul_ball_of_two_mul_le {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (r : ℝ)
    (hr : 2 * r ≤ X.systole) (γ : X.deckGroup) (hγ : γ ≠ 1) :
    Disjoint (γ • Metric.ball o r) (Metric.ball o r) := by
  rw [Metric.smul_ball, Set.disjoint_left]
  intro z hzγ hz
  have hzo : dist z o < r := Metric.mem_ball.mp hz
  have hzγo : dist z (γ • o) < r := Metric.mem_ball.mp hzγ
  have hdisplacement : dist o (γ • o) < 2 * r := calc
    dist o (γ • o) ≤ dist o z + dist z (γ • o) := dist_triangle _ _ _
    _ < r + r := add_lt_add (by simpa [dist_comm] using hzo) hzγo
    _ = 2 * r := by ring
  have hsys := X.systole_le_displacement γ hγ o
  exact (not_lt_of_ge hsys) (hdisplacement.trans_le hr)

end SystolicGrowth
