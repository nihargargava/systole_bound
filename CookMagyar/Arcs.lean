module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The elementary major/minor-arc decomposition in this file is adapted from
Gershon Bialer's `ternary-goldbach-lean`, in particular
`MathExtras.NumberTheory.Vinogradov.CircleMethod` and
`Math.Problems.TernaryGoldbach.CircleMethodDecomposition.Core`
(Apache-2.0).  The cubic scaling and arbitrary-power integrand are specific
to the Cook--Magyar specialization developed here.
-/
public import CookMagyar.CircleMethod
public import Mathlib.Analysis.Normed.Group.AddCircle

@[expose] public section

open MeasureTheory

namespace SystolicGrowth
namespace CookMagyarArcs

open CookMagyarCircle

/-! # Major and minor arcs for the cubic Cook--Magyar sum

For a cutoff `Q`, the major-arc centers are the reduced fractions `a / q`
with `0 <= a < q <= Q`.  At cubic scale `N`, each arc has radius
`Q / N^3`, as in the one-equation specialization of Cook--Magyar.  All arcs
are clipped to the fixed fundamental interval `[0, 1]`; the minor arcs are
the relative complement there.

This file only establishes the exact decomposition and its elementary
analytic prerequisites.  Estimates on the two pieces belong in subsequent
modules.
-/

/-- Reduced rational centers `a / q` with denominator at most `Q`.

The pair convention is `(numerator, denominator)`. -/
def majorArcCenters (Q : ℕ) : Set (ℕ × ℕ) :=
  {aq | aq.2 ≤ Q ∧ aq.2 ≠ 0 ∧ aq.1 < aq.2 ∧ Nat.Coprime aq.1 aq.2}

/-- The rational number represented by a major-arc center. -/
noncomputable def rationalCenter (a q : ℕ) : ℝ :=
  (a : ℝ) / (q : ℝ)

/-- The cubic major-arc radius.  Analytic applications take `Q` to be a
power of `log N`. -/
noncomputable def cubicArcRadius (N Q : ℕ) : ℝ :=
  (Q : ℝ) / (N : ℝ) ^ 3

/-- Distance modulo the period `1`.  Using the circle distance, rather than
ordinary distance in `ℝ`, is essential at the identified endpoints `0` and
`1` of the chosen fundamental interval. -/
noncomputable def periodicDistance (α β : ℝ) : ℝ :=
  dist (α : UnitAddCircle) (β : UnitAddCircle)

/-- The major arcs in the chosen fundamental interval `[0, 1]`. -/
noncomputable def majorArcs (N Q : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ a q : ℕ, (a, q) ∈ majorArcCenters Q ∧
      periodicDistance α (rationalCenter a q) < cubicArcRadius N Q}

/-- The minor arcs are the relative complement of the major arcs in
`[0, 1]`. -/
noncomputable def minorArcs (N Q : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ majorArcs N Q

theorem mem_majorArcCenters_iff {Q a q : ℕ} :
    (a, q) ∈ majorArcCenters Q ↔
      q ≤ Q ∧ q ≠ 0 ∧ a < q ∧ Nat.Coprime a q :=
  Iff.rfl

theorem mem_majorArcs_iff {N Q : ℕ} {α : ℝ} :
    α ∈ majorArcs N Q ↔
      α ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ a q : ℕ, (a, q) ∈ majorArcCenters Q ∧
          periodicDistance α (rationalCenter a q) < cubicArcRadius N Q :=
  Iff.rfl

theorem mem_minorArcs_iff {N Q : ℕ} {α : ℝ} :
    α ∈ minorArcs N Q ↔
      α ∈ Set.Icc (0 : ℝ) 1 ∧ α ∉ majorArcs N Q := by
  rfl

/-- There are only finitely many reduced centers with bounded denominator. -/
theorem majorArcCenters_finite (Q : ℕ) :
    (majorArcCenters Q).Finite := by
  refine Set.Finite.subset
    ((Set.finite_Iic (Q + 1)).prod (Set.finite_Iic (Q + 1))) ?_
  rintro ⟨a, q⟩ ⟨hq, _hq0, ha, _hcop⟩
  exact ⟨(lt_of_lt_of_le ha hq).le.trans (Nat.le_succ _),
    hq.trans (Nat.le_succ _)⟩

theorem majorArcs_subset_Icc (N Q : ℕ) :
    majorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  exact hα.1

theorem minorArcs_subset_Icc (N Q : ℕ) :
    minorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  exact hα.1

/-- The finite union of open, clipped rational neighborhoods is measurable. -/
theorem majorArcs_measurableSet (N Q : ℕ) :
    MeasurableSet (majorArcs N Q) := by
  have heq : majorArcs N Q =
      Set.Icc (0 : ℝ) 1 ∩
        ⋃ aq ∈ majorArcCenters Q,
          {α : ℝ |
            periodicDistance α (rationalCenter aq.1 aq.2) <
              cubicArcRadius N Q} := by
    ext α
    constructor
    · rintro ⟨hIcc, a, q, haq, hdist⟩
      refine ⟨hIcc, ?_⟩
      simp only [Set.mem_iUnion]
      exact ⟨(a, q), haq, hdist⟩
    · rintro ⟨hIcc, h⟩
      simp only [Set.mem_iUnion] at h
      obtain ⟨⟨a, q⟩, haq, hdist⟩ := h
      exact ⟨hIcc, a, q, haq, hdist⟩
  rw [heq]
  refine measurableSet_Icc.inter ?_
  refine (majorArcCenters_finite Q).measurableSet_biUnion ?_
  rintro ⟨a, q⟩ _haq
  exact (isOpen_lt (by
    unfold periodicDistance
    fun_prop) (by fun_prop)).measurableSet

theorem minorArcs_measurableSet (N Q : ℕ) :
    MeasurableSet (minorArcs N Q) := by
  exact measurableSet_Icc.diff (majorArcs_measurableSet N Q)

/-- Major and minor arcs are disjoint by construction. -/
theorem majorArcs_disjoint_minorArcs (N Q : ℕ) :
    Disjoint (majorArcs N Q) (minorArcs N Q) := by
  unfold minorArcs
  exact disjoint_sdiff_self_right

/-- Every point of `[0, 1]` belongs to exactly one side of the arc split. -/
theorem majorArcs_union_minorArcs (N Q : ℕ) :
    majorArcs N Q ∪ minorArcs N Q = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro α hα
    rcases hα with hmajor | hminor
    · exact majorArcs_subset_Icc N Q hmajor
    · exact minorArcs_subset_Icc N Q hminor
  · intro α hα
    by_cases hmajor : α ∈ majorArcs N Q
    · exact Or.inl hmajor
    · exact Or.inr ⟨hα, hmajor⟩

/-! ## The cubic Fourier integrand -/

/-- The Fourier integrand whose full-period integral extracts the target
coefficient for `n` copies of `x^3 - x`. -/
noncomputable def cubicIntegrand (n N T : ℕ) (α : ℝ) : ℂ :=
  (cubicVonMangoldtExpSum α N) ^ n * negAddChar α T

/-- The cubic integrand is continuous because it is a finite sum of complex
exponentials, followed by products and a natural power. -/
theorem cubicIntegrand_continuous (n N T : ℕ) :
    Continuous (cubicIntegrand n N T) := by
  unfold cubicIntegrand cubicVonMangoldtExpSum addChar negAddChar
  fun_prop

theorem cubicIntegrand_integrableOn_Icc (n N T : ℕ) :
    IntegrableOn (cubicIntegrand n N T) (Set.Icc (0 : ℝ) 1) :=
  (cubicIntegrand_continuous n N T).integrableOn_Icc

theorem cubicIntegrand_integrableOn_majorArcs (n N T Q : ℕ) :
    IntegrableOn (cubicIntegrand n N T) (majorArcs N Q) :=
  (cubicIntegrand_integrableOn_Icc n N T).mono_set (majorArcs_subset_Icc N Q)

theorem cubicIntegrand_integrableOn_minorArcs (n N T Q : ℕ) :
    IntegrableOn (cubicIntegrand n N T) (minorArcs N Q) :=
  (cubicIntegrand_integrableOn_Icc n N T).mono_set (minorArcs_subset_Icc N Q)

/-- The major-arc contribution to the cubic Fourier coefficient. -/
noncomputable def cubicMajorArcIntegral (n N T Q : ℕ) : ℂ :=
  ∫ α in majorArcs N Q, cubicIntegrand n N T α

/-- The minor-arc contribution to the cubic Fourier coefficient. -/
noncomputable def cubicMinorArcIntegral (n N T Q : ℕ) : ℂ :=
  ∫ α in minorArcs N Q, cubicIntegrand n N T α

/-- Exact major/minor-arc decomposition of the full cubic Fourier
integral. -/
theorem integral_cubicIntegrand_eq_major_add_minor (n N T Q : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1, cubicIntegrand n N T α) =
      cubicMajorArcIntegral n N T Q + cubicMinorArcIntegral n N T Q := by
  rw [← majorArcs_union_minorArcs N Q]
  rw [setIntegral_union (majorArcs_disjoint_minorArcs N Q)
    (minorArcs_measurableSet N Q)
    (cubicIntegrand_integrableOn_majorArcs n N T Q)
    (cubicIntegrand_integrableOn_minorArcs n N T Q)]
  rfl

/-- Combining Fourier orthogonality with the arc partition gives an exact
major-plus-minor formula for the weighted representation count. -/
theorem cubicVonMangoldtRepresentation_eq_major_add_minor (n N T Q : ℕ) :
    (cubicVonMangoldtRepresentation n N T : ℂ) =
      cubicMajorArcIntegral n N T Q + cubicMinorArcIntegral n N T Q := by
  rw [← integral_cubicVonMangoldtExpSum_pow n N T]
  exact integral_cubicIntegrand_eq_major_add_minor n N T Q

end CookMagyarArcs
end SystolicGrowth
