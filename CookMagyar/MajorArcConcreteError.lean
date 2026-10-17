module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MajorArcSumError
public import CookMagyar.CubicMajorArcMeasurableModel
public import CookMagyar.CubicMajorArcHomogeneousModel

@[expose] public section

open MeasureTheory

namespace SystolicGrowth.CookMagyarArcs

open CookMagyarCircle CookMagyarFiniteFourier CookMagyarMajorArc CookMagyarReal

abbrev Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator (Q : ℕ) :=
  {q : ℕ // q ∈ Finset.Icc 1 Q}

abbrev Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator (q : ℕ) :=
  {a : ℕ // a < q ∧ Nat.Coprime a q}

/-- The finite set of valid numerator/denominator pairs is exactly the
dependent family of reduced numerators over denominators `1 ≤ q ≤ Q`. -/
noncomputable def Internal.MajorArcConcreteErrorHelpers.majorArcCenterEquivDenominatorNumerator (Q : ℕ) :
  {aq : ℕ × ℕ // aq ∈ (majorArcCenters_finite Q).toFinset} ≃
      Σ q : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator Q, Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1 where
  toFun c := by
    have hc : c.1 ∈ majorArcCenters Q := by
      simpa only [Set.Finite.mem_toFinset] using c.2
    have hcenter := mem_majorArcCenters_iff.mp hc
    exact ⟨⟨c.1.2, Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hcenter.2.1, hcenter.1⟩⟩,
      ⟨c.1.1, ⟨hcenter.2.2.1, hcenter.2.2.2⟩⟩⟩
  invFun s := by
    refine ⟨(s.2.1, s.1.1), ?_⟩
    have hs : (s.2.1, s.1.1) ∈ majorArcCenters Q := by
      apply mem_majorArcCenters_iff.mpr
      exact ⟨(Finset.mem_Icc.mp s.1.2).2,
        Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp s.1.2).1,
        s.2.2.1, s.2.2.2⟩
    simpa only [Set.Finite.mem_toFinset] using hs
  left_inv := by
    intro c
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    cases s with
    | mk q a =>
      cases q with
      | mk q hq =>
        cases a with
        | mk a ha =>
          apply Sigma.ext
          · apply Subtype.ext
            rfl
          · rfl

/-! # Concrete integration of the wrapped powered model

This packages the pointwise AP discrepancy on each rational arc into the
existing disjoint-arc integration bound. Only the quantitative AP estimates
and the subsequent evaluation of the model integrals remain external.
-/

/-- Extend the wrapped model to all numerator/denominator pairs by zero on
the invalid zero-denominator case, so it is an ordinary function on the
finite center set used by the arc decomposition. -/
noncomputable def wrappedMajorArcModelForCenter
    (N n T : ℕ) (aq : ℕ × ℕ) (alpha : ℝ) : ℂ := by
  classical
  by_cases hq : aq.2 = 0
  · exact 0
  · letI : NeZero aq.2 := ⟨hq⟩
    exact wrappedMajorArcModel aq.2 aq.1 N n T alpha

/-- Uniform AP errors on the finitely many rational arcs give an integrated
major-arc approximation by the canonical wrapped models. -/
theorem norm_cubicMajorArcIntegral_sub_sum_wrappedModels_le
    (n N T Q : ℕ) (hscale : 2 * Q ^ 3 ≤ N ^ 3)
    (Delta : ℕ → ℝ) (hN : 0 < N)
    (hDelta : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      0 ≤ Delta aq.2)
    (hAP : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∀ (hqn : aq.2 ≠ 0), letI : NeZero aq.2 := ⟨hqn⟩
      ∀ r : ZMod aq.2, ∀ m ≤ N,
        ‖cubicResiduePartialSum aq.2 r m -
          (m + 1 : ℕ) *
            (if IsUnit r then (Nat.totient aq.2 : ℂ)⁻¹ else 0)‖ ≤
          Delta aq.2) :
    ‖cubicMajorArcIntegral n N T Q -
        ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
          ∫ alpha in majorArcAt N Q aq.1 aq.2,
            wrappedMajorArcModelForCenter N n T aq alpha‖ ≤
      ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
        ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((aq.2 : ℝ) * Delta aq.2 + 1) *
            (1 + 8 * Real.pi * (Q : ℝ)))) *
          volume.real (majorArcAt N Q aq.1 aq.2) := by
  let F := (majorArcCenters_finite Q).toFinset
  let model : ℕ × ℕ → ℝ → ℂ := fun aq alpha =>
    wrappedMajorArcModelForCenter N n T aq alpha
  let E : ℕ × ℕ → ℝ := fun aq =>
    (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
      (((aq.2 : ℝ) * Delta aq.2 + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)))
  have hmodel : ∀ aq ∈ F,
      IntegrableOn (model aq) (majorArcAt N Q aq.1 aq.2) := by
    intro aq haq
    change aq ∈ (majorArcCenters_finite Q).toFinset at haq
    have hcenter : aq ∈ majorArcCenters Q := by
      simpa only [Set.Finite.mem_toFinset] using haq
    rcases hcenter with ⟨_, hqn, _, _⟩
    letI : NeZero aq.2 := ⟨hqn⟩
    have hmodel_eq : model aq = wrappedMajorArcModel aq.2 aq.1 N n T := by
      funext alpha
      simp [model, wrappedMajorArcModelForCenter, hqn]
    rw [hmodel_eq]
    exact wrappedMajorArcModel_integrableOn aq.2 aq.1 N Q n T
  have hpoint : ∀ aq ∈ F, ∀ alpha ∈ majorArcAt N Q aq.1 aq.2,
      ‖cubicIntegrand n N T alpha - model aq alpha‖ ≤ E aq := by
    intro aq haq alpha halpha
    change aq ∈ (majorArcCenters_finite Q).toFinset at haq
    have hcenter : aq ∈ majorArcCenters Q := by
      simpa only [Set.Finite.mem_toFinset] using haq
    have hqn : aq.2 ≠ 0 := hcenter.2.1
    letI : NeZero aq.2 := ⟨hqn⟩
    have hmodel_eq : model aq = wrappedMajorArcModel aq.2 aq.1 N n T := by
      funext x
      simp [model, wrappedMajorArcModelForCenter, hqn]
    rw [hmodel_eq]
    exact norm_cubicIntegrand_sub_wrappedMajorArcModel_le
      aq.2 aq.1 N Q n T hN (hDelta aq haq) halpha (hAP aq haq hqn)
  simpa only [F, model, E] using
    norm_cubicMajorArcIntegral_sub_sum_models_le n N T Q hscale
      model E hmodel hpoint

/-- A common discrepancy bound and the elementary center/volume estimates
collapse the finite local major-arc error sum to one explicit global bound.
The AP estimate remains a genuine hypothesis; this theorem only performs the
uniform analytic bookkeeping. -/
theorem norm_cubicMajorArcIntegral_sub_sum_wrappedHomogeneousModels_le_global
    (n N T Q : ℕ) (hscale : 2 * Q ^ 3 ≤ N ^ 3)
    (Delta : ℕ → ℝ) (D : ℝ) (hN : 0 < N)
    (hD : 0 ≤ D)
    (hDelta : ∀ q ≤ Q, 0 ≤ Delta q ∧ Delta q ≤ D)
    (hAP : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∀ (hqn : aq.2 ≠ 0), letI : NeZero aq.2 := ⟨hqn⟩
      ∀ r : ZMod aq.2, ∀ m ≤ N,
        ‖cubicResiduePartialSum aq.2 r m -
          (m + 1 : ℕ) *
            (if IsUnit r then (Nat.totient aq.2 : ℂ)⁻¹ else 0)‖ ≤
          Delta aq.2) :
    ‖cubicMajorArcIntegral n N T Q -
        ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
          ∫ alpha in majorArcAt N Q aq.1 aq.2,
            wrappedHomogeneousMajorArcModelForCenter N n T aq alpha‖ ≤
      ((Q + 1 : ℕ) ^ 2 : ℝ) *
        ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
            2 * Real.pi * Q / (N : ℝ)) *
          (2 * (Q : ℝ) / (N : ℝ) ^ 3)) := by
  let F := (majorArcCenters_finite Q).toFinset
  let pointBound : ℝ :=
    (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
      (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
        2 * Real.pi * Q / (N : ℝ))
  have hpointBound : 0 ≤ pointBound := by
    dsimp [pointBound]
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hcenters : F.card ≤ (Q + 1) ^ 2 :=
    majorArcCenters_card_le_square Q
  have hlocal (aq : ℕ × ℕ) (haq : aq ∈ F) :
      ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((aq.2 : ℝ) * Delta aq.2 + 1) *
          (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * Q / (N : ℝ))) *
        volume.real (majorArcAt N Q aq.1 aq.2) ≤
      pointBound * (2 * (Q : ℝ) / (N : ℝ) ^ 3) := by
    have hcenter : aq ∈ majorArcCenters Q := by
      simpa only [F, Set.Finite.mem_toFinset] using haq
    have hqle : (aq.2 : ℝ) ≤ Q := by
      exact_mod_cast hcenter.1
    have hqDelta : (aq.2 : ℝ) * Delta aq.2 ≤ (Q : ℝ) * D := by
      have hprod := mul_nonneg (sub_nonneg.mpr hqle) (hDelta aq.2 hcenter.1 |>.1)
      have hupper := hDelta aq.2 hcenter.1 |>.2
      nlinarith
    have hterm :
        (((aq.2 : ℝ) * Delta aq.2 + 1) *
          (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * Q / (N : ℝ)) ≤
        (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * Q / (N : ℝ)) := by
      have hfac : 0 ≤ 1 + 8 * Real.pi * (Q : ℝ) := by positivity
      have hbase : (aq.2 : ℝ) * Delta aq.2 + 1 ≤
          (Q : ℝ) * D + 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hbase hfac
      linarith
    have hcoeff : 0 ≤
        (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) := by
      positivity
    have hvol := volume_real_majorArcAt_le_two_radius N Q aq.1 aq.2
    have hrad : 2 * cubicArcRadius N Q =
        2 * (Q : ℝ) / (N : ℝ) ^ 3 := by
      rw [cubicArcRadius]
      ring
    rw [hrad] at hvol
    dsimp [pointBound]
    calc
      _ ≤ ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
            2 * Real.pi * Q / (N : ℝ))) *
          volume.real (majorArcAt N Q aq.1 aq.2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hterm hcoeff)
          (measureReal_nonneg)
      _ ≤ ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
            2 * Real.pi * Q / (N : ℝ))) *
          (2 * (Q : ℝ) / (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hvol hpointBound
  have hsum := norm_cubicMajorArcIntegral_sub_sum_wrappedHomogeneousModels_le
    n N T Q hscale Delta hN
    (fun aq haq => (hDelta aq.2 (by
      have hc : aq ∈ majorArcCenters Q := by
        simpa only [F, Set.Finite.mem_toFinset] using haq
      exact hc.1)).1)
    hAP
  calc
    _ ≤ ∑ aq ∈ F,
        ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((aq.2 : ℝ) * Delta aq.2 + 1) *
            (1 + 8 * Real.pi * (Q : ℝ)) +
            2 * Real.pi * Q / (N : ℝ))) *
          volume.real (majorArcAt N Q aq.1 aq.2) := hsum
    _ ≤ ∑ _aq ∈ F, pointBound * (2 * (Q : ℝ) / (N : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro aq haq
      exact hlocal aq haq
    _ = (F.card : ℕ) * (pointBound *
          (2 * (Q : ℝ) / (N : ℝ) ^ 3)) := by simp
    _ ≤ ((Q + 1 : ℕ) ^ 2 : ℝ) * (pointBound *
          (2 * (Q : ℝ) / (N : ℝ) ^ 3)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcenters)
        (by positivity)
    _ = _ := by rfl

/-- Reindexing the nondependent center set recovers the denominator-indexed
sum used by the exact truncated singular-series model identity. -/
theorem sum_wrappedHomogeneousModels_over_centers_eq_denominators
    (N n T Q : ℕ) :
    (∑ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∫ alpha in majorArcAt N Q aq.1 aq.2,
        wrappedHomogeneousMajorArcModelForCenter N n T aq alpha) =
      ∑ q : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator Q,
        (letI : NeZero q.1 := ⟨by
           have hq := (Finset.mem_Icc.mp q.2).1
           omega⟩
         letI : Fintype (Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1) :=
           Fintype.ofEquiv (ZMod q.1)ˣ
             (reducedResiduesEquivUnits q.1).symm
         ∑ a : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1,
           ∫ alpha in majorArcAt N Q a.1 q.1,
             wrappedHomogeneousMajorArcModel q.1 a.1 N n T alpha) := by
  classical
  let F := (majorArcCenters_finite Q).toFinset
  let C := {aq : ℕ × ℕ // aq ∈ F}
  let Sigma : Type := Σ q : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator Q,
    Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1
  let e := Internal.MajorArcConcreteErrorHelpers.majorArcCenterEquivDenominatorNumerator Q
  let g : ℕ × ℕ → ℂ := fun aq =>
    ∫ alpha in majorArcAt N Q aq.1 aq.2,
      wrappedHomogeneousMajorArcModelForCenter N n T aq alpha
  let f : Sigma → ℂ := fun s =>
    letI : NeZero s.1.1 := ⟨by
      have hq := (Finset.mem_Icc.mp s.1.2).1
      omega⟩
    ∫ alpha in majorArcAt N Q s.2.1 s.1.1,
      wrappedHomogeneousMajorArcModel s.1.1 s.2.1 N n T alpha
  letI : ∀ q : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator Q,
      Fintype (Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1) := by
    intro q
    letI : NeZero q.1 := ⟨by
      have hq := (Finset.mem_Icc.mp q.2).1
      omega⟩
    exact Fintype.ofEquiv (ZMod q.1)ˣ
      (reducedResiduesEquivUnits q.1).symm
  have hattach :
      (∑ c : C, g c.1) = ∑ aq ∈ F, g aq := by
    rw [Finset.univ_eq_attach, Finset.sum_attach]
  have hreindex :
      (∑ c : C, g c.1) = ∑ s : Sigma, f s := by
    calc
      _ = ∑ c : C, f (e c) := by
        apply Fintype.sum_congr
        intro c
        have hc : c.1 ∈ majorArcCenters Q := by
          simpa only [F, Set.Finite.mem_toFinset] using c.2
        have hq0 : c.1.2 ≠ 0 := (mem_majorArcCenters_iff.mp hc).2.1
        simp [f, g, e, Internal.MajorArcConcreteErrorHelpers.majorArcCenterEquivDenominatorNumerator,
          wrappedHomogeneousMajorArcModelForCenter, hq0]
      _ = ∑ s : Sigma, f s := e.sum_comp f
  calc
    _ = ∑ c : C, g c.1 := hattach.symm
    _ = ∑ s : Sigma, f s := hreindex
    _ = ∑ q : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator Q,
          (letI : NeZero q.1 := ⟨by
             have hq := (Finset.mem_Icc.mp q.2).1
             omega⟩
           letI : Fintype (Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1) :=
             Fintype.ofEquiv (ZMod q.1)ˣ
               (reducedResiduesEquivUnits q.1).symm
           ∑ a : Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator q.1,
             ∫ alpha in majorArcAt N Q a.1 q.1,
               wrappedHomogeneousMajorArcModel q.1 a.1 N n T alpha) := by
      rw [Fintype.sum_sigma]
    _ = _ := by
      apply Fintype.sum_congr
      intro q
      letI : NeZero q.1 := ⟨by
        have hq := (Finset.mem_Icc.mp q.2).1
        omega⟩
      simp [f, Internal.MajorArcConcreteErrorHelpers.MajorArcCenterDenominator, Internal.MajorArcConcreteErrorHelpers.MajorArcCenterNumerator]

/-- The exact homogeneous model sum over the nondependent rational-center set
is the truncated singular-series/integral main term. -/
theorem sum_wrappedHomogeneousModels_over_centers_eq_truncatedMainTerm
    (N n T Q : ℕ) (hN : 0 < N)
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    (∑ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∫ alpha in majorArcAt N Q aq.1 aq.2,
        wrappedHomogeneousMajorArcModelForCenter N n T aq alpha) =
      (((N : ℝ) ^ n : ℂ) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)) *
        truncatedSingularSeries n T Q := by
  rw [sum_wrappedHomogeneousModels_over_centers_eq_denominators]
  exact sum_wrappedHomogeneousMajorArcModel_integrals_by_denominator_eq_truncatedSingularSeries
    N n T Q hN hscale

/-- Conditional major-arc approximation directly to the truncated analytic
main term, after reindexing the exact homogeneous model sum. -/
theorem norm_cubicMajorArcIntegral_sub_truncatedMainTerm_le_global
    (n N T Q : ℕ) (hscale : 2 * Q ^ 3 ≤ N ^ 3)
    (Delta : ℕ → ℝ) (D : ℝ) (hN : 0 < N)
    (hD : 0 ≤ D)
    (hDelta : ∀ q ≤ Q, 0 ≤ Delta q ∧ Delta q ≤ D)
    (hAP : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∀ (hqn : aq.2 ≠ 0), letI : NeZero aq.2 := ⟨hqn⟩
      ∀ r : ZMod aq.2, ∀ m ≤ N,
        ‖cubicResiduePartialSum aq.2 r m -
          (m + 1 : ℕ) *
            (if IsUnit r then (Nat.totient aq.2 : ℂ)⁻¹ else 0)‖ ≤
          Delta aq.2) :
    ‖cubicMajorArcIntegral n N T Q -
        ((((N : ℝ) ^ n : ℂ) *
          (((N : ℝ) ^ 3)⁻¹ •
            truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)) *
          truncatedSingularSeries n T Q)‖ ≤
      ((Q + 1 : ℕ) ^ 2 : ℝ) *
        ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((Q : ℝ) * D + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
            2 * Real.pi * Q / (N : ℝ)) *
          (2 * (Q : ℝ) / (N : ℝ) ^ 3)) := by
  have h := norm_cubicMajorArcIntegral_sub_sum_wrappedHomogeneousModels_le_global
    n N T Q hscale Delta D hN hD hDelta hAP
  rw [sum_wrappedHomogeneousModels_over_centers_eq_truncatedMainTerm
    N n T Q hN hscale] at h
  exact h

end SystolicGrowth.CookMagyarArcs

#print axioms SystolicGrowth.CookMagyarArcs.norm_cubicMajorArcIntegral_sub_sum_wrappedHomogeneousModels_le_global
#print axioms SystolicGrowth.CookMagyarArcs.sum_wrappedHomogeneousModels_over_centers_eq_truncatedMainTerm
#print axioms SystolicGrowth.CookMagyarArcs.norm_cubicMajorArcIntegral_sub_truncatedMainTerm_le_global
