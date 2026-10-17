module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainDistance
public import Geometry.MetricGluingAttainment

@[expose] public section

/-!
# Actual finite blocks of the augmented Fermi chain

Starting with copy zero, each stage attaches one closed slab at each end,
along the actual reflected fin. All carriers use mathlib's metric gluing,
and every old block and endpoint slab embeds isometrically. Properness is
preserved. No curvature comparison for a finite block is assumed here.
-/

open Set

namespace SystolicGrowth

instance gluingCollarFiniteMetricBlockSlab_properSpace (lam R : ℝ) :
    ProperSpace (gluingFinFermiRadialWindow lam R) :=
  ProperSpace.of_isClosed (gluingFinFermiRadialWindow_isClosed lam R)

/-- A genuine proper metric block with its two endpoint slab embeddings. -/
structure GluingCollarFiniteMetricBlockData (lam R : ℝ) where
  Space : Type
  [metricSpace : MetricSpace Space]
  [properSpace : ProperSpace Space]
  left : gluingFinFermiRadialWindow lam R → Space
  right : gluingFinFermiRadialWindow lam R → Space
  left_isometry : Isometry left
  right_isometry : Isometry right

attribute [instance] GluingCollarFiniteMetricBlockData.metricSpace
  GluingCollarFiniteMetricBlockData.properSpace

namespace GluingCollarFiniteMetricBlockData

/-- A single actual closed hyperbolic radial slab. -/
noncomputable def single (lam R : ℝ) : GluingCollarFiniteMetricBlockData lam R where
  Space := gluingFinFermiRadialWindow lam R
  metricSpace := inferInstance
  properSpace := inferInstance
  left := id
  right := id
  left_isometry := isometry_id
  right_isometry := isometry_id

variable {r R lam ε : ℝ}
  [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]

/-- Attach a new slab on the left: its upper fin meets the old lower fin. -/
noncomputable def attachLeft (B : GluingCollarFiniteMetricBlockData lam R) :
    GluingCollarFiniteMetricBlockData lam R where
  Space := Metric.GlueSpace
    (B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
  metricSpace := inferInstance
  properSpace := metricGlue_properSpace
    (B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
  left := Metric.toGlueR
    (B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
  right := Metric.toGlueL
    (B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε) ∘ B.right
  left_isometry := Metric.toGlueR_isometry _ _
  right_isometry := (Metric.toGlueL_isometry _ _).comp B.right_isometry

/-- The actual isometric inclusion when a slab is attached on the left. -/
noncomputable def intoAttachLeft (B : GluingCollarFiniteMetricBlockData lam R) :
    B.Space → (B.attachLeft (r := r) (ε := ε)).Space :=
  Metric.toGlueL
    (B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)

theorem intoAttachLeft_isometry (B : GluingCollarFiniteMetricBlockData lam R) :
    Isometry (B.intoAttachLeft (r := r) (ε := ε)) :=
  Metric.toGlueL_isometry _ _

theorem intoAttachLeft_seam (B : GluingCollarFiniteMetricBlockData lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    B.intoAttachLeft (r := r) (ε := ε)
        (B.left (gluingCollarFiniteMetricGlueRight r R lam ε q)) =
      (B.attachLeft (r := r) (ε := ε)).left
        (gluingCollarFiniteMetricGlueLeft r R lam ε q) :=
  congrFun (Metric.toGlue_commute _ _) q

/-- Attach a new slab on the right: its lower fin meets the old upper fin. -/
noncomputable def attachRight (B : GluingCollarFiniteMetricBlockData lam R) :
    GluingCollarFiniteMetricBlockData lam R where
  Space := Metric.GlueSpace
    (B.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  metricSpace := inferInstance
  properSpace := metricGlue_properSpace
    (B.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  left := Metric.toGlueL
    (B.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) ∘ B.left
  right := Metric.toGlueR
    (B.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  left_isometry := (Metric.toGlueL_isometry _ _).comp B.left_isometry
  right_isometry := Metric.toGlueR_isometry _ _

/-- The actual isometric inclusion when a slab is attached on the right. -/
noncomputable def intoAttachRight (B : GluingCollarFiniteMetricBlockData lam R) :
    B.Space → (B.attachRight (r := r) (ε := ε)).Space :=
  Metric.toGlueL
    (B.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)

theorem intoAttachRight_isometry (B : GluingCollarFiniteMetricBlockData lam R) :
    Isometry (B.intoAttachRight (r := r) (ε := ε)) :=
  Metric.toGlueL_isometry _ _

theorem intoAttachRight_seam (B : GluingCollarFiniteMetricBlockData lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    B.intoAttachRight (r := r) (ε := ε)
        (B.right (gluingCollarFiniteMetricGlueLeft r R lam ε q)) =
      (B.attachRight (r := r) (ε := ε)).right
        (gluingCollarFiniteMetricGlueRight r R lam ε q) :=
  congrFun (Metric.toGlue_commute _ _) q

/-- Each symmetric extension adds one genuine slab at either end. -/
noncomputable def extend (B : GluingCollarFiniteMetricBlockData lam R) :
    GluingCollarFiniteMetricBlockData lam R :=
  (B.attachLeft (r := r) (ε := ε)).attachRight (r := r) (ε := ε)

noncomputable def intoExtend (B : GluingCollarFiniteMetricBlockData lam R) :
    B.Space → (B.extend (r := r) (ε := ε)).Space :=
  (B.attachLeft (r := r) (ε := ε)).intoAttachRight (r := r) (ε := ε) ∘
    B.intoAttachLeft (r := r) (ε := ε)

theorem intoExtend_isometry (B : GluingCollarFiniteMetricBlockData lam R) :
    Isometry (B.intoExtend (r := r) (ε := ε)) :=
  (B.attachLeft (r := r) (ε := ε)).intoAttachRight_isometry.comp
    B.intoAttachLeft_isometry

theorem extend_left_seam (B : GluingCollarFiniteMetricBlockData lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    (B.extend (r := r) (ε := ε)).left
        (gluingCollarFiniteMetricGlueLeft r R lam ε q) =
      B.intoExtend (r := r) (ε := ε)
        (B.left (gluingCollarFiniteMetricGlueRight r R lam ε q)) := by
  exact congrArg ((B.attachLeft (r := r) (ε := ε)).intoAttachRight
    (r := r) (ε := ε)) (B.intoAttachLeft_seam q).symm

theorem extend_right_seam (B : GluingCollarFiniteMetricBlockData lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    B.intoExtend (r := r) (ε := ε)
        (B.right (gluingCollarFiniteMetricGlueLeft r R lam ε q)) =
      (B.extend (r := r) (ε := ε)).right
        (gluingCollarFiniteMetricGlueRight r R lam ε q) :=
  (B.attachLeft (r := r) (ε := ε)).intoAttachRight_seam q

end GluingCollarFiniteMetricBlockData

/-- The actual block with copies `[-n,n]`, obtained by two genuine metric
gluings at every successor stage. Nonemptiness comes from a native fin point. -/
noncomputable def gluingCollarFiniteMetricBlockData
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    GluingCollarFiniteMetricBlockData lam R := by
  letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
  exact Nat.rec (GluingCollarFiniteMetricBlockData.single lam R)
    (fun _ B => B.extend (r := r) (ε := ε)) n

abbrev gluingCollarFiniteMetricBlockSpace
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :=
  (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n).Space

/-- The nested block inclusion used by the actual metric inductive limit. -/
noncomputable def gluingCollarFiniteMetricBlockInclusion
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n →
      gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam (n + 1) := by
  letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
  exact (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n).intoExtend

theorem gluingCollarFiniteMetricBlockInclusion_isometry
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    Isometry (gluingCollarFiniteMetricBlockInclusion (r := r) (ε := ε) hR hlam n) := by
  letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
  exact (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n).intoExtend_isometry

/-- The actual embedding of each integer-labelled copy in its symmetric
finite block. The bounds are precisely the labels `[-n,n]`. -/
noncomputable def gluingCollarFiniteMetricBlockCopy
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) :
    (n : ℕ) → (i : ℤ) → (-(n : ℤ) ≤ i ∧ i ≤ (n : ℤ)) →
      gluingFinFermiRadialWindow lam R →
        gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n
  | 0, _, _ => id
  | n + 1, i, hi => by
      by_cases hleft : i = -((n + 1 : ℕ) : ℤ)
      · exact (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam (n + 1)).left
      · by_cases hright : i = ((n + 1 : ℕ) : ℤ)
        · exact (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam (n + 1)).right
        · exact gluingCollarFiniteMetricBlockInclusion (r := r) (ε := ε) hR hlam n ∘
            gluingCollarFiniteMetricBlockCopy hR hlam n i (by omega)

theorem gluingCollarFiniteMetricBlockCopy_isometry
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (n : ℕ) (i : ℤ) (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ)) :
    Isometry (gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hi) := by
  induction n with
  | zero => exact isometry_id
  | succ n ih =>
      by_cases hleft : i = -((n + 1 : ℕ) : ℤ)
      · simpa only [gluingCollarFiniteMetricBlockCopy, dif_pos hleft] using
          (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam (n + 1)).left_isometry
      · by_cases hright : i = ((n + 1 : ℕ) : ℤ)
        · simpa only [gluingCollarFiniteMetricBlockCopy, dif_neg hleft, dif_pos hright] using
            (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam (n + 1)).right_isometry
        · simpa only [gluingCollarFiniteMetricBlockCopy, dif_neg hleft, dif_neg hright] using
            (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam n).comp
              (ih (by omega))

/-- An old labelled copy commutes with the genuine nested block inclusion. -/
theorem gluingCollarFiniteMetricBlockCopy_inclusion
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (n : ℕ) (i : ℤ) (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ))
    (hi' : -((n + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((n + 1 : ℕ) : ℤ)) :
    gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam (n + 1) i hi' =
      gluingCollarFiniteMetricBlockInclusion (r := r) (ε := ε) hR hlam n ∘
        gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hi := by
  have hleft : i ≠ -((n + 1 : ℕ) : ℤ) := by omega
  have hright : i ≠ ((n + 1 : ℕ) : ℤ) := by omega
  simp only [gluingCollarFiniteMetricBlockCopy, dif_neg hleft, dif_neg hright]

theorem gluingCollarFiniteMetricBlockCopy_left
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n (-(n : ℤ))
        (by omega) =
      (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n).left := by
  cases n with
  | zero => rfl
  | succ n => simp [gluingCollarFiniteMetricBlockCopy]

theorem gluingCollarFiniteMetricBlockCopy_right
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) :
    gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n (n : ℤ)
        (by omega) =
      (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n).right := by
  cases n with
  | zero => rfl
  | succ n =>
      have hleft : ((n + 1 : ℕ) : ℤ) ≠ -((n + 1 : ℕ) : ℤ) := by omega
      simp only [gluingCollarFiniteMetricBlockCopy, dif_neg hleft, dite_true]

private theorem metricBlockCopy_label_congr
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (n : ℕ) {i j : ℤ}
    (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ))
    (hj : -(n : ℤ) ≤ j ∧ j ≤ (n : ℤ)) (hij : i = j) :
    gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hi =
      gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n j hj := by
  subst j
  rfl

/-- Adjacent labelled copies identify their actual whole reflected fins,
not just the strip-boundary graphs. -/
theorem gluingCollarFiniteMetricBlockCopy_seam
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (n : ℕ) (i : ℤ) (hi : -(n : ℤ) ≤ i ∧ i + 1 ≤ (n : ℤ))
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i (by omega)
        (gluingCollarFiniteMetricGlueLeft r R lam ε q) =
      gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n (i + 1) (by omega)
        (gluingCollarFiniteMetricGlueRight r R lam ε q) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
      let B := gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n
      by_cases hleft : i = -((n + 1 : ℕ) : ℤ)
      · have hnext : i + 1 = -(n : ℤ) := by omega
        have hnextold : -(n : ℤ) ≤ i + 1 ∧ i + 1 ≤ (n : ℤ) := by omega
        have hleftCopy :
            gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam (n + 1) i
                (by omega) = (B.extend (r := r) (ε := ε)).left := by
          exact (metricBlockCopy_label_congr hR hlam (n + 1) (by omega) (by omega)
            hleft).trans (gluingCollarFiniteMetricBlockCopy_left
              (r := r) (ε := ε) hR hlam (n + 1))
        have hnextCopy :
            gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n (i + 1)
                hnextold = B.left := by
          exact (metricBlockCopy_label_congr hR hlam n hnextold (by omega) hnext).trans
            (gluingCollarFiniteMetricBlockCopy_left (r := r) (ε := ε) hR hlam n)
        rw [gluingCollarFiniteMetricBlockCopy_inclusion hR hlam n (i + 1) hnextold]
        simp only [Function.comp_apply]
        rw [hleftCopy, hnextCopy]
        exact B.extend_left_seam q
      · by_cases hright : i = (n : ℤ)
        · have hold : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ) := by omega
          have hnext : i + 1 = ((n + 1 : ℕ) : ℤ) := by omega
          have hrightCopy :
              gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam (n + 1)
                  (i + 1) (by omega) = (B.extend (r := r) (ε := ε)).right := by
            exact (metricBlockCopy_label_congr hR hlam (n + 1) (by omega) (by omega)
              hnext).trans (gluingCollarFiniteMetricBlockCopy_right
                (r := r) (ε := ε) hR hlam (n + 1))
          have holdCopy :
              gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hold =
                B.right := by
            exact (metricBlockCopy_label_congr hR hlam n hold (by omega) hright).trans
              (gluingCollarFiniteMetricBlockCopy_right (r := r) (ε := ε) hR hlam n)
          rw [gluingCollarFiniteMetricBlockCopy_inclusion hR hlam n i hold]
          simp only [Function.comp_apply]
          rw [holdCopy, hrightCopy]
          exact B.extend_right_seam q
        · have hold : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ) := by omega
          have hnextold : -(n : ℤ) ≤ i + 1 ∧ i + 1 ≤ (n : ℤ) := by omega
          rw [gluingCollarFiniteMetricBlockCopy_inclusion hR hlam n i hold,
            gluingCollarFiniteMetricBlockCopy_inclusion hR hlam n (i + 1) hnextold]
          simp only [Function.comp_apply]
          exact congrArg (gluingCollarFiniteMetricBlockInclusion hR hlam n)
            (ih i (by omega))

#print axioms gluingCollarFiniteMetricBlockInclusion_isometry
#print axioms gluingCollarFiniteMetricBlockCopy_isometry
#print axioms gluingCollarFiniteMetricBlockCopy_seam

end SystolicGrowth
