module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainDistance
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-!
# Pointwise distance convergence of the strip and augmented fin chains

The proved two-sided whole-chain estimates squeeze the actual concatenation
distance to the native collar distance, with the AB04 curvature scale
`lam = sqrt (1 - ε)`. The actual augmented quotient permits fin excursions;
its reverse clipping estimate gives the same native distance limit. Curvature
comparison and passage of curvature to the limit remain separate obligations.
-/

open Set Filter
open scoped ENNReal Topology

namespace SystolicGrowth

/-- On a fixed radial window, the genuine glued-strip distances converge to
the native collar distance for every positive sequence of widths tending to
zero. The maps and target quotients are the actual width-dependent objects. -/
theorem gluingCollarFiniteChainEDist_tendsto
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hscale : Tendsto ε atTop (𝓝 0))
    {x y : ℂ} (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    Tendsto (fun n => gluingCollarFiniteChainEDist r R
      (Real.sqrt (1 - ε n)) (ε n)
      (gluingCollarFiniteBandTargetMap r c (ε n) (hε n) x)
      (gluingCollarFiniteBandTargetMap r c (ε n) (hε n) y))
      atTop (𝓝 (gluingCollarModelEDist hr x y)) := by
  let lam : ℕ → ℝ := fun n => Real.sqrt (1 - ε n)
  let A : ℕ → ℝ := fun n =>
    1 + (Real.cosh (lam n * (ε n * Real.sinh (r + R))) - 1 +
      ε n * Real.cosh (|r| + R))
  let B : ℕ → ℝ := fun n => 1 + ε n * Real.cosh (|r| + R)
  let d : ℝ≥0∞ := gluingCollarModelEDist hr x y
  let dN : ℕ → ℝ≥0∞ := fun n => gluingCollarFiniteChainEDist r R (lam n) (ε n)
    (gluingCollarFiniteBandTargetMap r c (ε n) (hε n) x)
    (gluingCollarFiniteBandTargetMap r c (ε n) (hε n) y)
  have hd : d ≠ ⊤ := (gluingCollarModelEDist_lt_top hr x y).ne
  have hdN (n : ℕ) : dN n ≠ ⊤ :=
    (gluingCollarFiniteChainEDist_lt_top hr hR (Real.sqrt_nonneg _) (hε n)
      (gluingCollarFiniteBandTargetMap_admissible hr (hε n) hx)
      (gluingCollarFiniteBandTargetMap_admissible hr (hε n) hy)).ne
  have hApos (n : ℕ) : 0 < A n := by
    dsimp [A]
    have hcosh := Real.cosh_pos (lam n * (ε n * Real.sinh (r + R)))
    have herr : 0 ≤ ε n * Real.cosh (|r| + R) :=
      mul_nonneg (hε n).le (Real.cosh_pos _).le
    linarith
  have hBpos (n : ℕ) : 0 < B n := by
    dsimp [B]
    have heps := hε n
    positivity
  have hupper (n : ℕ) : (dN n).toReal ≤ A n * d.toReal := by
    have h := gluingCollarFiniteChainEDist_forward_le_native
      (c := c) (lam := lam n) hr hR (Real.sqrt_nonneg (1 - ε n)) (hε n) hx hy
    change dN n ≤ ENNReal.ofReal (A n) * d at h
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hApos n).le] using hreal
  have hlower (n : ℕ) : d.toReal / B n ≤ (dN n).toReal := by
    have h : d ≤ ENNReal.ofReal (B n) * dN n := by
      simpa only [gluingCollarFiniteBandTargetInverse_map] using
        gluingCollarModelEDist_inverse_le_chain hr hR (hε n).le c
          (gluingCollarFiniteBandTargetMap r c (ε n) (hε n) x)
          (gluingCollarFiniteBandTargetMap r c (ε n) (hε n) y)
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdN n)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hBpos n).le] at hreal
    exact (div_le_iff₀ (hBpos n)).2 (by simpa only [mul_comm] using hreal)
  have hlam : Tendsto lam atTop (𝓝 1) := by
    have hsub : Tendsto (fun n => (1 : ℝ) - ε n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hscale
    simpa only [lam, Function.comp_def, sub_zero, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto (1 - 0)).comp hsub
  have harg : Tendsto (fun n => lam n * (ε n * Real.sinh (r + R)))
      atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using hlam.mul (hscale.mul_const _)
  have hcosh : Tendsto (fun n => Real.cosh (lam n * (ε n * Real.sinh (r + R))))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cosh_zero] using
      (Real.continuous_cosh.tendsto 0).comp harg
  have herr : Tendsto (fun n => ε n * Real.cosh (|r| + R)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hscale.mul_const (Real.cosh (|r| + R))
  have hA : Tendsto A atTop (𝓝 1) := by
    have hform : A = fun n => Real.cosh (lam n * (ε n * Real.sinh (r + R))) +
        ε n * Real.cosh (|r| + R) := by
      funext n
      dsimp [A]
      ring
    rw [hform]
    simpa only [add_zero] using hcosh.add herr
  have hB : Tendsto B atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add herr
  have hlowerLimit : Tendsto (fun n => d.toReal / B n) atTop (𝓝 d.toReal) := by
    convert
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => d.toReal) atTop (𝓝 d.toReal)).div
        hB (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> simp [Pi.div_def]
  have hupperLimit : Tendsto (fun n => A n * d.toReal) atTop (𝓝 d.toReal) := by
    simpa only [one_mul] using hA.mul_const d.toReal
  have hreal : Tendsto (fun n => (dN n).toReal) atTop (𝓝 d.toReal) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerLimit hupperLimit hlower hupper
  have henn := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_toReal hd, ENNReal.ofReal_toReal (hdN _)] using henn

/-- AB04's dyadic widths are a concrete verified instance of pointwise
distance convergence on each bounded radial window. -/
theorem gluingCollarFiniteChainEDist_dyadic_tendsto
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    Tendsto (fun n : ℕ => gluingCollarFiniteChainEDist r R
      (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)
      (gluingCollarFiniteBandTargetMap r c ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n) x)
      (gluingCollarFiniteBandTargetMap r c ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n) y))
      atTop (𝓝 (gluingCollarModelEDist hr x y)) :=
  gluingCollarFiniteChainEDist_tendsto hr hR (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => pow_pos (by norm_num) n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hx hy

/-- The actual augmented fin-chain distances converge to native collar
distance on every fixed radial window. The reverse estimate controls all
ambient fin excursions, not only paths constrained to the strips. -/
theorem gluingCollarFiniteFinChainEDist_tendsto
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hscale : Tendsto ε atTop (𝓝 0))
    {x y : ℂ} (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    Tendsto (fun n => gluingCollarFiniteFinChainEDist r R
      (Real.sqrt (1 - ε n)) (ε n)
      (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) x)
      (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) y))
      atTop (𝓝 (gluingCollarModelEDist hr x y)) := by
  let lam : ℕ → ℝ := fun n => Real.sqrt (1 - ε n)
  let A : ℕ → ℝ := fun n =>
    1 + (Real.cosh (lam n * (ε n * Real.sinh (r + R))) - 1 +
      ε n * Real.cosh (|r| + R))
  let B : ℕ → ℝ := fun n => (1 + ε n * Real.cosh (|r| + R)) ^ 2
  let d : ℝ≥0∞ := gluingCollarModelEDist hr x y
  let dN : ℕ → ℝ≥0∞ := fun n => gluingCollarFiniteFinChainEDist r R (lam n) (ε n)
    (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) x)
    (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) y)
  have hd : d ≠ ⊤ := (gluingCollarModelEDist_lt_top hr x y).ne
  have hdN (n : ℕ) : dN n ≠ ⊤ :=
    (gluingCollarFiniteFinChainEDist_map_lt_top hr hR (Real.sqrt_nonneg _) (hε n)
      hx hy).ne
  have hApos (n : ℕ) : 0 < A n := by
    dsimp [A]
    have hcosh := Real.cosh_pos (lam n * (ε n * Real.sinh (r + R)))
    have herr : 0 ≤ ε n * Real.cosh (|r| + R) :=
      mul_nonneg (hε n).le (Real.cosh_pos _).le
    linarith
  have hBpos (n : ℕ) : 0 < B n := by
    dsimp [B]
    have heps := hε n
    positivity
  have hupper (n : ℕ) : (dN n).toReal ≤ A n * d.toReal := by
    have h := gluingCollarFiniteFinChainEDist_forward_le_native
      (c := c) (lam := lam n) hr hR (Real.sqrt_nonneg (1 - ε n)) (hε n) hx hy
    change dN n ≤ ENNReal.ofReal (A n) * d at h
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hApos n).le] using hreal
  have hlower (n : ℕ) : d.toReal / B n ≤ (dN n).toReal := by
    have h : d ≤ ENNReal.ofReal (B n) * dN n := by
      simpa only [gluingCollarFiniteFinTargetInverse_map] using
        gluingCollarModelEDist_inverse_le_finChain hr hR (hε n).le c
          (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) x)
          (gluingCollarFiniteFinTargetMap r c (ε n) (hε n) y)
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdN n)) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hBpos n).le] at hreal
    exact (div_le_iff₀ (hBpos n)).2 (by simpa only [mul_comm] using hreal)
  have hlam : Tendsto lam atTop (𝓝 1) := by
    have hsub : Tendsto (fun n => (1 : ℝ) - ε n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hscale
    simpa only [lam, Function.comp_def, sub_zero, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto (1 - 0)).comp hsub
  have harg : Tendsto (fun n => lam n * (ε n * Real.sinh (r + R)))
      atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using hlam.mul (hscale.mul_const _)
  have hcosh : Tendsto (fun n => Real.cosh (lam n * (ε n * Real.sinh (r + R))))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cosh_zero] using
      (Real.continuous_cosh.tendsto 0).comp harg
  have herr : Tendsto (fun n => ε n * Real.cosh (|r| + R)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hscale.mul_const (Real.cosh (|r| + R))
  have hA : Tendsto A atTop (𝓝 1) := by
    have hform : A = fun n => Real.cosh (lam n * (ε n * Real.sinh (r + R))) +
        ε n * Real.cosh (|r| + R) := by
      funext n
      dsimp [A]
      ring
    rw [hform]
    simpa only [add_zero] using hcosh.add herr
  have hB : Tendsto B atTop (𝓝 1) := by
    have hsum : Tendsto (fun n => 1 + ε n * Real.cosh (|r| + R)) atTop (𝓝 1) := by
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add herr
    simpa only [one_pow] using hsum.pow 2
  have hlowerLimit : Tendsto (fun n => d.toReal / B n) atTop (𝓝 d.toReal) := by
    convert
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => d.toReal) atTop (𝓝 d.toReal)).div
        hB (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> simp [Pi.div_def]
  have hupperLimit : Tendsto (fun n => A n * d.toReal) atTop (𝓝 d.toReal) := by
    simpa only [one_mul] using hA.mul_const d.toReal
  have hreal : Tendsto (fun n => (dN n).toReal) atTop (𝓝 d.toReal) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlowerLimit hupperLimit hlower hupper
  have henn := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_toReal hd, ENNReal.ofReal_toReal (hdN _)] using henn

/-- AB04's exact dyadic widths and curvature scale satisfy the augmented
fin-chain distance-limit conclusion. -/
theorem gluingCollarFiniteFinChainEDist_dyadic_tendsto
    {r R c : ℝ} (hr : 0 < r) (hR : 0 ≤ R) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    Tendsto (fun n : ℕ => gluingCollarFiniteFinChainEDist r R
      (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)
      (gluingCollarFiniteFinTargetMap r c ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n) x)
      (gluingCollarFiniteFinTargetMap r c ((1 / 2 : ℝ) ^ n)
        (pow_pos (by norm_num) n) y))
      atTop (𝓝 (gluingCollarModelEDist hr x y)) :=
  gluingCollarFiniteFinChainEDist_tendsto hr hR (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => pow_pos (by norm_num) n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hx hy

#print axioms gluingCollarFiniteChainEDist_tendsto
#print axioms gluingCollarFiniteChainEDist_dyadic_tendsto
#print axioms gluingCollarFiniteFinChainEDist_tendsto
#print axioms gluingCollarFiniteFinChainEDist_dyadic_tendsto

end SystolicGrowth
