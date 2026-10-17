module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteMetricBlocks

@[expose] public section

/-!
# The native whole-fin chain maps to the actual finite-block limit

Each labelled slab embeds isometrically in the metric inductive limit,
independently of the chosen sufficiently large block. Adjacent copies agree
on their entire actual reflected fins. The resulting map on the whole-fin
quotient contracts its scaled Fermi-chain distance. No curvature premise or
reverse distance inequality is assumed here.
-/

open Set
open scoped ENNReal

namespace SystolicGrowth

/-- The actual metric inductive limit of the original symmetric blocks. -/
abbrev gluingCollarFiniteMetricBlockLimit
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) :=
  Metric.InductiveLimit
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam)

theorem Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlock_label_natAbs_bounds (i : ℤ) :
    -(i.natAbs : ℤ) ≤ i ∧ i ≤ (i.natAbs : ℤ) := by
  cases i with
  | ofNat n => simp
  | negSucc n => simp; omega

private theorem metricBlock_label_natAbs_le {i : ℤ} {n : ℕ}
    (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ)) : i.natAbs ≤ n := by
  cases i with
  | ofNat k => simpa using hi.2
  | negSucc k => simp_all; omega

private theorem metricBlock_stageCopy_stable
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (i : ℤ) {n m : ℕ} (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ)) (hnm : n ≤ m)
    (z : gluingFinFermiRadialWindow lam R) :
    Metric.toInductiveLimit
        (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) m
        (gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam m i (by omega) z) =
      Metric.toInductiveLimit
        (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) n
        (gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hi z) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      rw [gluingCollarFiniteMetricBlockCopy_inclusion hR hlam m i (by omega)]
      exact (congrFun (Metric.toInductiveLimit_commute
        (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) m)
        (gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam m i (by omega) z)).trans ih

/-- Every integer-labelled slab has one canonical isometric embedding in
the actual metric limit, initially using its smallest symmetric block. -/
noncomputable def gluingCollarFiniteMetricBlockLimitCopy
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ) :
    gluingFinFermiRadialWindow lam R →
      gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam :=
  Metric.toInductiveLimit
      (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) i.natAbs ∘
    gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam i.natAbs i
      (Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlock_label_natAbs_bounds i)

theorem gluingCollarFiniteMetricBlockLimitCopy_isometry
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ) :
    Isometry (gluingCollarFiniteMetricBlockLimitCopy (r := r) (ε := ε) hR hlam i) :=
  (Metric.toInductiveLimit_isometry
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) i.natAbs).comp
      (gluingCollarFiniteMetricBlockCopy_isometry hR hlam i.natAbs i
        (Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlock_label_natAbs_bounds i))

/-- The canonical copy equals its realization in any sufficiently large
actual block, not merely one specially chosen stage. -/
theorem gluingCollarFiniteMetricBlockLimitCopy_eq_stage
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ) (n : ℕ)
    (hi : -(n : ℤ) ≤ i ∧ i ≤ (n : ℤ)) (z : gluingFinFermiRadialWindow lam R) :
    gluingCollarFiniteMetricBlockLimitCopy (r := r) (ε := ε) hR hlam i z =
      Metric.toInductiveLimit
        (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) n
        (gluingCollarFiniteMetricBlockCopy (r := r) (ε := ε) hR hlam n i hi z) := by
  exact (metricBlock_stageCopy_stable hR hlam i (Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlock_label_natAbs_bounds i)
    (metricBlock_label_natAbs_le hi) z).symm

/-- Adjacent canonical copies agree on the whole native reflected fin. -/
theorem gluingCollarFiniteMetricBlockLimitCopy_seam
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ)
    (q : gluingCollarFiniteUpperFin r R lam ε) :
    gluingCollarFiniteMetricBlockLimitCopy (r := r) (ε := ε) hR hlam i
        (gluingCollarFiniteMetricGlueLeft r R lam ε q) =
      gluingCollarFiniteMetricBlockLimitCopy (r := r) (ε := ε) hR hlam (i + 1)
        (gluingCollarFiniteMetricGlueRight r R lam ε q) := by
  let n := max i.natAbs (i + 1).natAbs
  have hi : -(n : ℤ) ≤ i ∧ i + 1 ≤ (n : ℤ) := by
    have h₁ := Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlock_label_natAbs_bounds i
    have h₂ := Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlock_label_natAbs_bounds (i + 1)
    have hn₁ := Nat.le_max_left i.natAbs (i + 1).natAbs
    have hn₂ := Nat.le_max_right i.natAbs (i + 1).natAbs
    dsimp only [n]
    omega
  rw [gluingCollarFiniteMetricBlockLimitCopy_eq_stage hR hlam i n (by omega),
    gluingCollarFiniteMetricBlockLimitCopy_eq_stage hR hlam (i + 1) n (by omega)]
  exact congrArg (Metric.toInductiveLimit
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam) n)
      (gluingCollarFiniteMetricBlockCopy_seam hR hlam n i hi q)

/-- The original Fermi point in its actual closed hyperbolic radial slab. -/
noncomputable def gluingCollarFiniteMetricBlockChainSlab
    {R lam : ℝ} (hlam : 0 < lam) (z : ℂ) (hz : z.re ∈ Icc (-R) R) :
    gluingFinFermiRadialWindow lam R :=
  ⟨gluingFinFermiPoint lam z.re z.im, by
    change gluingFinFermiRadialCoord lam _ ∈ Icc (-R) R
    rwa [gluingFinFermiRadialCoord_point hlam]⟩

noncomputable def Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (p : ℤ × ℂ) :
    gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam := by
  classical
  exact if hz : p.2.re ∈ Icc (-R) R then
    gluingCollarFiniteMetricBlockLimitCopy hR hlam p.1
      (gluingCollarFiniteMetricBlockChainSlab hlam p.2 hz)
  else gluingCollarFiniteMetricBlockLimitCopy hR hlam 0
    (gluingCollarFiniteMetricBlockChainSlab hlam 0 ⟨by simpa using neg_nonpos.mpr hR, hR⟩)

theorem Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw_relation
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) {p q : ℤ × ℂ}
    (hpq : gluingCollarFiniteFinRelation r ε p q) :
    Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw (r := r) (ε := ε) hR hlam p =
      Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw (r := r) (ε := ε) hR hlam q := by
  classical
  have hmirror := gluingCollarFiniteFinRelation_fermi_eq_mirror hpq lam
  obtain ⟨hindex, hre, _, hupper⟩ := hpq
  by_cases hp : p.2.re ∈ Icc (-R) R
  · have hq : q.2.re ∈ Icc (-R) R := hre ▸ hp
    let a : gluingCollarFiniteUpperFin r R lam ε :=
      ⟨gluingFinFermiPoint lam p.2.re p.2.im, by
        change gluingFinFermiRadialCoord lam _ ∈ Icc (-R) R ∧ _
        rw [gluingFinFermiRadialCoord_point hlam, gluingFinFermiTransverseCoord_point hlam]
        exact ⟨hp, hupper⟩⟩
    have hleft : gluingCollarFiniteMetricBlockChainSlab hlam p.2 hp =
        gluingCollarFiniteMetricGlueLeft r R lam ε a := rfl
    have hright : gluingCollarFiniteMetricBlockChainSlab hlam q.2 hq =
        gluingCollarFiniteMetricGlueRight r R lam ε a := by
      apply Subtype.ext
      exact hmirror.symm
    simp only [Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw, dif_pos hp, dif_pos hq]
    rw [hleft, hright, ← hindex]
    exact gluingCollarFiniteMetricBlockLimitCopy_seam hR hlam p.1 a
  · have hq : q.2.re ∉ Icc (-R) R := by simpa only [← hre] using hp
    simp only [Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw, dif_neg hp, dif_neg hq]

/-- The actual whole-fin quotient maps to the genuine finite-block metric
limit. All out-of-window representatives map to one fixed copy-zero point;
the actual seam relation preserves radial membership. -/
noncomputable def gluingCollarFiniteMetricBlockChainMap
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) :
    gluingCollarFiniteFinTarget r ε →
      gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε) hR hlam := by
  refine Quotient.lift (Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw hR hlam) ?_
  intro p q h
  induction h with
  | rel p q h => exact Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw_relation hR hlam h
  | refl p => rfl
  | symm p q _ h => exact h.symm
  | trans p q s _ _ hpq hqs => exact hpq.trans hqs

theorem gluingCollarFiniteMetricBlockChainMap_mk
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ) (z : ℂ)
    (hz : z.re ∈ Icc (-R) R) :
    gluingCollarFiniteMetricBlockChainMap (r := r) (ε := ε) hR hlam
        (Quotient.mk _ (i, z)) =
      gluingCollarFiniteMetricBlockLimitCopy hR hlam i
        (gluingCollarFiniteMetricBlockChainSlab hlam z hz) := by
  classical
  simp only [gluingCollarFiniteMetricBlockChainMap, Quotient.lift_mk,
    Internal.GluingCollarFiniteMetricBlockChainMapHelpers.metricBlockChainRaw, dif_pos hz]

/-- Each genuine Fermi step preserves its exact distance in the limit,
including the required curvature-scale factor. -/
theorem gluingCollarFiniteMetricBlockChainMap_fermi_edist
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ) (z w : ℂ)
    (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    edist (gluingCollarFiniteMetricBlockChainMap (r := r) (ε := ε) hR hlam
        (Quotient.mk _ (i, z)))
      (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (i, w))) =
        ENNReal.ofReal lam * gluingCollarFiniteFermiEDist R lam z w := by
  rw [gluingCollarFiniteMetricBlockChainMap_mk hR hlam i z hz,
    gluingCollarFiniteMetricBlockChainMap_mk hR hlam i w hw,
    (gluingCollarFiniteMetricBlockLimitCopy_isometry hR hlam i).edist_eq,
    edist_dist, gluingCollarFiniteFermiEDist_scaled_eq hlam hz hw]
  rfl

/-- Every original finite whole-fin walk bounds the distance between its
mapped endpoints by its cost times the exact curvature scale. -/
theorem gluingCollarFiniteMetricBlockChainMap_edist_le_cost
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    {p q : gluingCollarFiniteFinTarget r ε} {A : ℝ≥0∞}
    (h : GluingCollarFiniteFinChainPath r R lam ε p q A) :
    edist (gluingCollarFiniteMetricBlockChainMap hR hlam p)
      (gluingCollarFiniteMetricBlockChainMap hR hlam q) ≤ ENNReal.ofReal lam * A := by
  induction h with
  | refl p => simp
  | fermi n z w hz hw =>
      exact (gluingCollarFiniteMetricBlockChainMap_fermi_edist hR hlam n z w hz hw).le
  | symm h ih => simpa only [edist_comm] using ih
  | @trans p q s A B hpq hqs ihpq ihqs =>
      calc
        _ ≤ edist (gluingCollarFiniteMetricBlockChainMap hR hlam p)
              (gluingCollarFiniteMetricBlockChainMap hR hlam q) +
            edist (gluingCollarFiniteMetricBlockChainMap hR hlam q)
              (gluingCollarFiniteMetricBlockChainMap hR hlam s) := edist_triangle _ _ _
        _ ≤ ENNReal.ofReal lam * A + ENNReal.ofReal lam * B := add_le_add ihpq ihqs
        _ = ENNReal.ofReal lam * (A + B) := (mul_add _ _ _).symm

/-- Forward contraction from the original scaled whole-chain distance to
the actual finite-block metric limit. The reverse inequality is separate. -/
theorem gluingCollarFiniteMetricBlockChainMap_edist_le
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (p q : gluingCollarFiniteFinTarget r ε) :
    edist (gluingCollarFiniteMetricBlockChainMap hR hlam p)
      (gluingCollarFiniteMetricBlockChainMap hR hlam q) ≤
        ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε p q := by
  have hpos : ENNReal.ofReal lam ≠ 0 := by positivity
  simp only [gluingCollarFiniteFinChainEDist,
    ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
  exact le_iInf fun A => le_iInf fun h =>
    gluingCollarFiniteMetricBlockChainMap_edist_le_cost hR hlam h

#print axioms gluingCollarFiniteMetricBlockLimitCopy_isometry
#print axioms gluingCollarFiniteMetricBlockLimitCopy_eq_stage
#print axioms gluingCollarFiniteMetricBlockLimitCopy_seam
#print axioms gluingCollarFiniteMetricBlockChainMap
#print axioms gluingCollarFiniteMetricBlockChainMap_fermi_edist
#print axioms gluingCollarFiniteMetricBlockChainMap_edist_le

end SystolicGrowth
