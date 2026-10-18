module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteMetricBlocks
public import Geometry.GluingCollarFiniteFinPathEMetric
public import Geometry.GluingCollarFiniteMetricBlockChainMap
public import Geometry.MetricGluingLipschitzLift

@[expose] public section

/-!
# Distance bridge for the actual finite Fermi blocks

Every block point belongs to an original labelled slab. Compatible
nonexpanding maps into the separated original path space then identify the
block limit's distance with the original scaled whole-chain distance.
The raw quotient's outside-window points are not declared finite.
-/

open Set

namespace SystolicGrowth

/-- The original labelled slabs cover the entire actual finite block. -/
theorem gluingCollarFiniteMetricBlockCopy_surjective
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ)
    (x : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n) :
    ∃ i : ℤ, ∃ hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ),
      ∃ z : gluingFinFermiRadialWindow lam R,
        gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hi z = x := by
  letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
  induction n with
  | zero => exact ⟨0, by omega, x, rfl⟩
  | succ n ih =>
      let B := gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n
      change (B.extend (r := r) (ε := ε)).Space at x
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      cases a with
      | inr z =>
          refine ⟨((n + 1 : ℕ) : ℤ), by omega, z, ?_⟩
          rw [gluingCollarFiniteMetricBlockCopy_right]
          rfl
      | inl a =>
          obtain ⟨b, rfl⟩ := Quotient.exists_rep a
          cases b with
          | inr z =>
              refine ⟨-((n + 1 : ℕ) : ℤ), by omega, z, ?_⟩
              rw [gluingCollarFiniteMetricBlockCopy_left]
              rfl
          | inl b =>
              obtain ⟨i, hi, z, hz⟩ := ih b
              refine ⟨i, by omega, z, ?_⟩
              rw [gluingCollarFiniteMetricBlockCopy_inclusion hR hlam n i hi]
              change B.intoExtend
                (gluingCollarFiniteMetricBlockCopy hR hlam n i hi z) =
                  B.intoExtend b
              exact congrArg B.intoExtend hz

theorem Internal.GluingCollarFiniteMetricBlockDistanceBridgeHelpers.exists_metricBlockPathMap
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    ∃ F : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n →
        gluingCollarFiniteFinPathEMetric r R lam ε,
      LipschitzWith 1 F ∧
      ∀ (i : ℤ) (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ))
        (z : gluingFinFermiRadialWindow lam R),
        F (gluingCollarFiniteMetricBlockCopy hR hlam n i hi z) =
          gluingCollarFiniteFinPathSlabMap r R lam ε i z := by
  letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
  induction n with
  | zero =>
      refine ⟨gluingCollarFiniteFinPathSlabMap r R lam ε 0,
        gluingCollarFiniteFinPathSlabMap_lipschitz hlam 0, ?_⟩
      intro i hi z
      have hi0 : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      obtain ⟨F, hF, hFc⟩ := ih
      let B := gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n
      let A := B.attachLeft (r := r) (ε := ε)
      let neg := -((n + 1 : ℕ) : ℤ)
      let pos := ((n + 1 : ℕ) : ℤ)
      let fneg := gluingCollarFiniteFinPathSlabMap r R lam ε neg
      let fpos := gluingCollarFiniteFinPathSlabMap r R lam ε pos
      have hfneg : LipschitzWith 1 fneg := gluingCollarFiniteFinPathSlabMap_lipschitz hlam neg
      have hfpos : LipschitzWith 1 fpos := gluingCollarFiniteFinPathSlabMap_lipschitz hlam pos
      have hFleft (z : gluingFinFermiRadialWindow lam R) :
          F (B.left z) = gluingCollarFiniteFinPathSlabMap r R lam ε (-(n : ℤ)) z := by
        have h := hFc (-(n : ℤ)) (by omega) z
        rw [gluingCollarFiniteMetricBlockCopy_left] at h
        exact h
      have hFright (z : gluingFinFermiRadialWindow lam R) :
          F (B.right z) = gluingCollarFiniteFinPathSlabMap r R lam ε (n : ℤ) z := by
        have h := hFc (n : ℤ) (by omega) z
        rw [gluingCollarFiniteMetricBlockCopy_right] at h
        exact h
      let hΦ := B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
      let hΨ := gluingCollarFiniteMetricGlueLeft_isometry r R lam ε
      have hcomm : F ∘ (B.left ∘ gluingCollarFiniteMetricGlueRight r R lam ε) =
          fneg ∘ gluingCollarFiniteMetricGlueLeft r R lam ε := by
        funext q
        change F (B.left (gluingCollarFiniteMetricGlueRight r R lam ε q)) =
          fneg (gluingCollarFiniteMetricGlueLeft r R lam ε q)
        rw [hFleft]
        have h := gluingCollarFiniteFinPathSlabMap_seam r R lam ε neg q
        have hnext : neg + 1 = -(n : ℤ) := by dsimp [neg]; omega
        rw [hnext] at h
        exact h.symm
      let H : A.Space → gluingCollarFiniteFinPathEMetric r R lam ε :=
        metricGlueLipschitzLift hΦ hΨ F fneg
      have hH : LipschitzWith 1 H :=
        metricGlueLipschitzLift_lipschitz hΦ hΨ F fneg hF hfneg hcomm
      have hHold (x : B.Space) : H (B.intoAttachLeft (r := r) (ε := ε) x) = F x :=
        metricGlueLipschitzLift_left hΦ hΨ F fneg hF hfneg hcomm x
      have hHnew (z : gluingFinFermiRadialWindow lam R) : H (A.left z) = fneg z :=
        metricGlueLipschitzLift_right hΦ hΨ F fneg hF hfneg hcomm z
      let hΦ' := A.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      let hΨ' := gluingCollarFiniteMetricGlueRight_isometry r R lam ε
      have hcomm' : H ∘ (A.right ∘ gluingCollarFiniteMetricGlueLeft r R lam ε) =
          fpos ∘ gluingCollarFiniteMetricGlueRight r R lam ε := by
        funext q
        change H (B.intoAttachLeft (r := r) (ε := ε)
          (B.right (gluingCollarFiniteMetricGlueLeft r R lam ε q))) =
            fpos (gluingCollarFiniteMetricGlueRight r R lam ε q)
        rw [hHold, hFright]
        exact gluingCollarFiniteFinPathSlabMap_seam r R lam ε (n : ℤ) q
      let J : (B.extend (r := r) (ε := ε)).Space →
          gluingCollarFiniteFinPathEMetric r R lam ε :=
        metricGlueLipschitzLift hΦ' hΨ' H fpos
      have hJ : LipschitzWith 1 J :=
        metricGlueLipschitzLift_lipschitz hΦ' hΨ' H fpos hH hfpos hcomm'
      have hJold (x : A.Space) : J (A.intoAttachRight (r := r) (ε := ε) x) = H x :=
        metricGlueLipschitzLift_left hΦ' hΨ' H fpos hH hfpos hcomm' x
      have hJnew (z : gluingFinFermiRadialWindow lam R) :
          J ((B.extend (r := r) (ε := ε)).right z) = fpos z :=
        metricGlueLipschitzLift_right hΦ' hΨ' H fpos hH hfpos hcomm' z
      have hJleft (z : gluingFinFermiRadialWindow lam R) :
          J ((B.extend (r := r) (ε := ε)).left z) = fneg z := by
        change J (A.intoAttachRight (r := r) (ε := ε) (A.left z)) = fneg z
        rw [hJold, hHnew]
      refine ⟨J, hJ, ?_⟩
      intro i hi z
      by_cases hleft : i = neg
      · subst i
        rw [gluingCollarFiniteMetricBlockCopy_left]
        exact hJleft z
      · by_cases hright : i = pos
        · subst i
          rw [gluingCollarFiniteMetricBlockCopy_right]
          exact hJnew z
        · have hiold : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ) := by dsimp [neg, pos] at hleft hright; omega
          rw [gluingCollarFiniteMetricBlockCopy_inclusion hR hlam n i hiold]
          change J (A.intoAttachRight (r := r) (ε := ε)
            (B.intoAttachLeft (r := r) (ε := ε)
              (gluingCollarFiniteMetricBlockCopy hR hlam n i hiold z))) =
                gluingCollarFiniteFinPathSlabMap r R lam ε i z
          rw [hJold, hHold, hFc]

/-- The recursively constructed nonexpanding map from an actual finite
block to the separated original finite-walk path space. -/
noncomputable def gluingCollarFiniteMetricBlockPathMap
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n →
      gluingCollarFiniteFinPathEMetric r R lam ε :=
  (Internal.GluingCollarFiniteMetricBlockDistanceBridgeHelpers.exists_metricBlockPathMap hR hlam n).choose

theorem gluingCollarFiniteMetricBlockPathMap_lipschitz
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    LipschitzWith 1 (gluingCollarFiniteMetricBlockPathMap (r := r) (ε := ε) hR hlam n) :=
  (Internal.GluingCollarFiniteMetricBlockDistanceBridgeHelpers.exists_metricBlockPathMap hR hlam n).choose_spec.1

/-- The block map keeps the integer label and exact native slab point. -/
theorem gluingCollarFiniteMetricBlockPathMap_copy
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ)
    (i : ℤ) (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ))
    (z : gluingFinFermiRadialWindow lam R) :
    gluingCollarFiniteMetricBlockPathMap (r := r) (ε := ε) hR hlam n
        (gluingCollarFiniteMetricBlockCopy hR hlam n i hi z) =
      gluingCollarFiniteFinPathSlabMap r R lam ε i z :=
  (Internal.GluingCollarFiniteMetricBlockDistanceBridgeHelpers.exists_metricBlockPathMap hR hlam n).choose_spec.2 i hi z

/-- Independently chosen stage maps are coherent because every block point
belongs to one original labelled copy, whose value is fixed exactly. -/
theorem gluingCollarFiniteMetricBlockPathMap_inclusion
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ)
    (x : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n) :
    gluingCollarFiniteMetricBlockPathMap (r := r) (ε := ε) hR hlam (n + 1)
        (gluingCollarFiniteMetricBlockInclusion hR hlam n x) =
      gluingCollarFiniteMetricBlockPathMap hR hlam n x := by
  obtain ⟨i, hi, z, rfl⟩ := gluingCollarFiniteMetricBlockCopy_surjective hR hlam n x
  have hinc := congrFun (gluingCollarFiniteMetricBlockCopy_inclusion
    (r := r) (ε := ε) hR hlam n i hi (by omega)) z
  dsimp only [Function.comp_apply] at hinc
  rw [← hinc]
  rw [gluingCollarFiniteMetricBlockPathMap_copy, gluingCollarFiniteMetricBlockPathMap_copy]

/-- The compatible block maps descend through the actual metric inductive
limit into the separated native finite-walk distance space. -/
noncomputable def gluingCollarFiniteMetricBlockLimitPathMap
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) :
    gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam →
      gluingCollarFiniteFinPathEMetric r R lam ε :=
  metricInductiveLimitLipschitzLift
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam)
    (gluingCollarFiniteMetricBlockPathMap hR hlam)

theorem gluingCollarFiniteMetricBlockLimitPathMap_lipschitz
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) :
    LipschitzWith 1 (gluingCollarFiniteMetricBlockLimitPathMap
      (r := r) (ε := ε) hR hlam) :=
  metricInductiveLimitLipschitzLift_lipschitz
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam)
    (gluingCollarFiniteMetricBlockPathMap hR hlam)
    (gluingCollarFiniteMetricBlockPathMap_lipschitz hR hlam)
    (gluingCollarFiniteMetricBlockPathMap_inclusion hR hlam)

/-- Exact evaluation on every original block stage. -/
theorem gluingCollarFiniteMetricBlockLimitPathMap_stage
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ)
    (x : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n) :
    gluingCollarFiniteMetricBlockLimitPathMap hR hlam
        (Metric.toInductiveLimit
          (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) n x) =
      gluingCollarFiniteMetricBlockPathMap hR hlam n x :=
  metricInductiveLimitLipschitzLift_eval
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam)
    (gluingCollarFiniteMetricBlockPathMap hR hlam)
    (gluingCollarFiniteMetricBlockPathMap_lipschitz hR hlam)
    (gluingCollarFiniteMetricBlockPathMap_inclusion hR hlam) n x

/-- Every canonical labelled slab in the actual block limit maps to the
same labelled slab class in the separated native path space. -/
theorem gluingCollarFiniteMetricBlockLimitPathMap_copy
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ)
    (z : gluingFinFermiRadialWindow lam R) :
    gluingCollarFiniteMetricBlockLimitPathMap (r := r) (ε := ε) hR hlam
        (gluingCollarFiniteMetricBlockLimitCopy hR hlam i z) =
      gluingCollarFiniteFinPathSlabMap r R lam ε i z := by
  dsimp only [gluingCollarFiniteMetricBlockLimitCopy, Function.comp_apply]
  rw [gluingCollarFiniteMetricBlockLimitPathMap_stage,
    gluingCollarFiniteMetricBlockPathMap_copy]

#print axioms gluingCollarFiniteMetricBlockCopy_surjective
#print axioms gluingCollarFiniteMetricBlockPathMap_lipschitz
#print axioms gluingCollarFiniteMetricBlockPathMap_copy
#print axioms gluingCollarFiniteMetricBlockPathMap_inclusion
#print axioms gluingCollarFiniteMetricBlockLimitPathMap_lipschitz
#print axioms gluingCollarFiniteMetricBlockLimitPathMap_copy

end SystolicGrowth
