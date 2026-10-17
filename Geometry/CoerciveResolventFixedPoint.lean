module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalCurvatureNonlinearity
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

/-!
# The actual nonlinear `L²` fixed point for a coercive resolvent

The scalar extension is the explicit one constructed in
`ConformalCurvatureNonlinearity`. Lipschitz composition gives genuine `Lp`
elements, independent of a.e.-equal representatives, on any finite measure
space. A bounded linear resolvent of norm at most `1 / lam` then gives an
actual unique fixed point and its `Lp` equation.

This functional step does not assert elliptic solvability: its resolvent
input is to be supplied by the separate constructed Hilbert graph inverse.
No PDE or replacement metric is concluded merely from the norm contract.
-/

open MeasureTheory
open scoped ENNReal

namespace SystolicGrowth

noncomputable section

/-- Remove the finite-volume constant before composing on `Lp`. -/
def conformalCurvatureCenteredNonlinearity (B t : ℝ) : ℝ :=
  conformalCurvatureNonlinearity B t - 1

@[simp] theorem conformalCurvatureCenteredNonlinearity_zero (B : ℝ) :
    conformalCurvatureCenteredNonlinearity B 0 = 0 := by
  simp [conformalCurvatureCenteredNonlinearity]

theorem conformalCurvatureCenteredNonlinearity_lipschitz {B : ℝ} (hB : 1 < B) :
    LipschitzWith ⟨4 * B, by linarith⟩ (conformalCurvatureCenteredNonlinearity B) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm, conformalCurvatureCenteredNonlinearity]
  rw [show (conformalCurvatureNonlinearity B s - 1) -
    (conformalCurvatureNonlinearity B t - 1) =
      conformalCurvatureNonlinearity B s - conformalCurvatureNonlinearity B t by ring]
  exact (conformalCurvatureNonlinearity_lipschitz hB).norm_sub_le s t

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

/-- Literal composition by `Ψ` in `L²`, with its nonzero constant retained. -/
def conformalCurvatureNonlinearityLp (B : ℝ) (hB : 1 < B) (v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (conformalCurvatureCenteredNonlinearity_lipschitz hB).compLp
    (conformalCurvatureCenteredNonlinearity_zero B) v + Lp.const 2 μ (1 : ℝ)

theorem conformalCurvatureNonlinearityLp_coeFn (B : ℝ) (hB : 1 < B) (v : Lp ℝ 2 μ) :
    conformalCurvatureNonlinearityLp μ B hB v =ᵐ[μ]
      fun x => conformalCurvatureNonlinearity B (v x) := by
  filter_upwards [Lp.coeFn_add
    ((conformalCurvatureCenteredNonlinearity_lipschitz hB).compLp
      (conformalCurvatureCenteredNonlinearity_zero B) v) (Lp.const 2 μ (1 : ℝ)),
    (conformalCurvatureCenteredNonlinearity_lipschitz hB).coeFn_compLp
      (conformalCurvatureCenteredNonlinearity_zero B) v,
    Lp.coeFn_const (p := 2) (μ := μ) (1 : ℝ)] with x hx hc h1
  simp only [Pi.add_apply, Function.comp_apply, Function.const_apply] at hx hc h1
  unfold conformalCurvatureNonlinearityLp
  rw [hx, hc, h1]
  simp [conformalCurvatureCenteredNonlinearity]

/-- The genuine forcing `lam * v - K - Ψ(v)` in `L²`. The centered damped
composition exposes its sharp difference estimate without a triangle loss. -/
def conformalCurvatureResolventForcing (B lam : ℝ) (hB : 1 < B) (hlam : 4 * B ≤ lam)
    (K v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (conformalCurvatureDampedNonlinearity_lipschitz hB hlam).compLp
    (conformalCurvatureDampedNonlinearity_zero B lam) v - K - Lp.const 2 μ (1 : ℝ)

theorem conformalCurvatureResolventForcing_coeFn (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K v : Lp ℝ 2 μ) :
    conformalCurvatureResolventForcing μ B lam hB hlam K v =ᵐ[μ]
      fun x => lam * v x - K x - conformalCurvatureNonlinearity B (v x) := by
  let D := (conformalCurvatureDampedNonlinearity_lipschitz hB hlam).compLp
    (conformalCurvatureDampedNonlinearity_zero B lam) v
  filter_upwards [Lp.coeFn_sub (D - K) (Lp.const 2 μ (1 : ℝ)),
    Lp.coeFn_sub D K,
    (conformalCurvatureDampedNonlinearity_lipschitz hB hlam).coeFn_compLp
      (conformalCurvatureDampedNonlinearity_zero B lam) v,
    Lp.coeFn_const (p := 2) (μ := μ) (1 : ℝ)] with x hx hs hd h1
  simp only [Pi.sub_apply, Function.comp_apply, Function.const_apply] at hx hs hd h1
  change ((D - K - Lp.const 2 μ (1 : ℝ)) : Lp ℝ 2 μ) x = _
  rw [hx, hs, hd, h1]
  dsimp [conformalCurvatureDampedNonlinearity]
  ring

theorem conformalCurvatureResolventForcing_eq (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K v : Lp ℝ 2 μ) :
    conformalCurvatureResolventForcing μ B lam hB hlam K v =
      lam • v - K - conformalCurvatureNonlinearityLp μ B hB v := by
  apply Lp.ext
  filter_upwards [conformalCurvatureResolventForcing_coeFn μ B lam hB hlam K v,
    Lp.coeFn_sub (lam • v - K) (conformalCurvatureNonlinearityLp μ B hB v),
    Lp.coeFn_sub (lam • v) K, Lp.coeFn_smul lam v,
    conformalCurvatureNonlinearityLp_coeFn μ B hB v] with x hf hs ht hm hp
  simp only [Pi.sub_apply, Pi.smul_apply] at hs ht hm
  rw [hf, hs, ht, hm, hp]
  rfl

theorem conformalCurvatureResolventForcing_norm_sub_le (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K v w : Lp ℝ 2 μ) :
    ‖conformalCurvatureResolventForcing μ B lam hB hlam K v -
      conformalCurvatureResolventForcing μ B lam hB hlam K w‖ ≤ (lam - 1) * ‖v - w‖ := by
  unfold conformalCurvatureResolventForcing
  rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]
  exact (conformalCurvatureDampedNonlinearity_lipschitz hB hlam).norm_compLp_sub_le
    (conformalCurvatureDampedNonlinearity_zero B lam) v w

/-- Apply the actual bounded linear resolvent to the actual nonlinear forcing. -/
def conformalCurvatureResolventMap (B lam : ℝ) (hB : 1 < B) (hlam : 4 * B ≤ lam)
    (K : Lp ℝ 2 μ) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  R (conformalCurvatureResolventForcing μ B lam hB hlam K v)

theorem conformalCurvatureResolventMap_contracting (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K : Lp ℝ 2 μ)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ‖R‖ ≤ lam⁻¹) :
    ContractingWith ⟨(lam - 1) / lam, div_nonneg (by linarith) (by linarith)⟩
      (conformalCurvatureResolventMap μ B lam hB hlam K R) := by
  have hlpos : 0 < lam := by linarith
  constructor
  · change (lam - 1) / lam < 1
    exact (div_lt_one hlpos).2 (by linarith)
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [dist_eq_norm, conformalCurvatureResolventMap]
    rw [← map_sub]
    calc
      ‖R (conformalCurvatureResolventForcing μ B lam hB hlam K v -
          conformalCurvatureResolventForcing μ B lam hB hlam K w)‖ ≤
          ‖R‖ * ‖conformalCurvatureResolventForcing μ B lam hB hlam K v -
            conformalCurvatureResolventForcing μ B lam hB hlam K w‖ := R.le_opNorm _
      _ ≤ lam⁻¹ * ((lam - 1) * ‖v - w‖) :=
        mul_le_mul hR (conformalCurvatureResolventForcing_norm_sub_le μ B lam hB hlam K v w)
          (norm_nonneg _) (inv_nonneg.mpr hlpos.le)
      _ = ((lam - 1) / lam) * ‖v - w‖ := by ring

/-- A constructed `L²` fixed point. This is not a smooth solution yet. -/
def conformalCurvatureResolventFixedPoint (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K : Lp ℝ 2 μ)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ‖R‖ ≤ lam⁻¹) : Lp ℝ 2 μ :=
  (conformalCurvatureResolventMap_contracting μ B lam hB hlam K R hR).fixedPoint _

theorem conformalCurvatureResolventFixedPoint_equation (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K : Lp ℝ 2 μ)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ‖R‖ ≤ lam⁻¹) :
    let u := conformalCurvatureResolventFixedPoint μ B lam hB hlam K R hR
    u = R (lam • u - K - conformalCurvatureNonlinearityLp μ B hB u) := by
  dsimp only
  have h := (conformalCurvatureResolventMap_contracting μ B lam hB hlam K R hR).fixedPoint_isFixedPt
  change R (conformalCurvatureResolventForcing μ B lam hB hlam K _) = _ at h
  rw [conformalCurvatureResolventForcing_eq] at h
  exact h.symm

theorem conformalCurvatureResolventFixedPoint_unique (B lam : ℝ)
    (hB : 1 < B) (hlam : 4 * B ≤ lam) (K : Lp ℝ 2 μ)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ‖R‖ ≤ lam⁻¹) (v : Lp ℝ 2 μ)
    (hv : v = R (lam • v - K - conformalCurvatureNonlinearityLp μ B hB v)) :
    v = conformalCurvatureResolventFixedPoint μ B lam hB hlam K R hR := by
  apply (conformalCurvatureResolventMap_contracting μ B lam hB hlam K R hR).fixedPoint_unique
  change R (conformalCurvatureResolventForcing μ B lam hB hlam K v) = v
  rw [conformalCurvatureResolventForcing_eq]
  exact hv.symm

#print axioms conformalCurvatureNonlinearityLp_coeFn
#print axioms conformalCurvatureResolventForcing_eq
#print axioms conformalCurvatureResolventMap_contracting
#print axioms conformalCurvatureResolventFixedPoint_equation
#print axioms conformalCurvatureResolventFixedPoint_unique

end

end SystolicGrowth
