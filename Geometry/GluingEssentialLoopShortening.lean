module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingEssentialLoopArclength
public import Geometry.MetricPathVariation
public import Geometry.MetricPathLipschitz

@[expose] public section

/-!
# Local shortening of an actual essential-loop minimum

Inside a genuine contractible comparison ball, replace a short arc by its
native metric chord. Concatenation preserves the homotopy class, and
arclength normalization returns the competitor to the original speed bound.
Minimality therefore forces equality between local arc length and distance.
-/

open Set Metric
open scoped Topology unitInterval NNReal ENNReal

namespace SystolicGrowth

private theorem essential_of_homotopic_closedLoop
    {M : Type*} [TopologicalSpace M] (f a : closedLoopMapSet M)
    (hbase : f.1 0 = a.1 0)
    (hf : ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0)))
    (hhom : (closedLoopPath f).Homotopic ((closedLoopPath a).cast hbase hbase)) :
    ¬(closedLoopPath a).Homotopic (Path.refl (a.1 0)) := by
  intro ha
  have hcast := ha.pathCast hbase hbase
  have hrefl : (Path.refl (a.1 0)).cast hbase hbase = Path.refl (f.1 0) := by
    apply Path.ext
    funext t
    exact hbase.symm
  rw [hrefl] at hcast
  exact hf (hhom.trans hcast)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An arclength-normalized minimum in the actual common-speed essential
family has the positive local metric speed law on the interval interior.
The hypotheses are exactly the fields of the constructed native minimum. -/
theorem arclength_minimizing_essential_loop_locally_metric
    (P : ExerciseGluingPreparation C g n genera X) (K : ℝ≥0) (l : ℝ)
    (hl : 0 < l) (hlK : l ≤ K) (f : closedLoopMapSet P.GluedCarrier)
    (hLip : letI := P.gluedCarrierIntrinsicMetricSpace; LipschitzWith ⟨l, hl.le⟩ f.1)
    (hessential : ¬(closedLoopPath f).Homotopic (Path.refl (f.1 0)))
    (hvariation : letI := P.gluedCarrierIntrinsicMetricSpace;
      ∀ s t : unitInterval, s ≤ t →
        eVariationOn f.1 (Icc s t) = ENNReal.ofReal (l * ((t : ℝ) - s)))
    (hmin : letI := P.gluedCarrierIntrinsicMetricSpace;
      ∀ h : closedLoopMapSet P.GluedCarrier, LipschitzWith K h.1 →
        ¬(closedLoopPath h).Homotopic (Path.refl (h.1 0)) →
        ENNReal.ofReal l ≤ eVariationOn h.1 univ) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      ∃ δ > 0, ∀ u v : unitInterval,
        |(u : ℝ) - t| < δ → |(v : ℝ) - t| < δ →
        dist (f.1 u) (f.1 v) = l * |(u : ℝ) - v| := by
  classical
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  intro t _ht0 _ht1
  obtain ⟨ε₁, hε₁, hcomparison⟩ :=
    P.gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test (f.1 t)
  obtain ⟨ε₂, hε₂, hcontract⟩ :=
    P.gluedIntrinsicMetric_locally_contractible_closedBall (f.1 t)
  let R := min ε₁ ε₂ / 2
  have hR : 0 < R := div_pos (lt_min hε₁ hε₂) (by norm_num)
  have hR₁ : R < ε₁ := by dsimp only [R]; linarith [min_le_left ε₁ ε₂]
  have hR₂ : R < ε₂ := by dsimp only [R]; linarith [min_le_right ε₁ ε₂]
  letI : IsClosed (closedBall (f.1 t) R) := isClosed_closedBall
  letI : ContractibleSpace (closedBall (f.1 t) R) := hcontract R hR.le hR₂
  let δ := R / l
  have hδ : 0 < δ := div_pos hR hl
  have hball (w : unitInterval) (hw : |(w : ℝ) - t| < δ) :
      f.1 w ∈ closedBall (f.1 t) R := by
    apply mem_closedBall.mpr
    have hd := hLip.dist_le_mul w t
    change dist (f.1 w) (f.1 t) ≤ l * |(w : ℝ) - t| at hd
    have hsmall := mul_lt_mul_of_pos_left hw hl
    have hcancel : l * δ = R := mul_div_cancel₀ _ hl.ne'
    rw [hcancel] at hsmall
    exact (hd.trans_lt hsmall).le
  refine ⟨δ, hδ, ?_⟩
  intro u v hu hv
  wlog huv : u ≤ v generalizing u v
  · rw [dist_comm, abs_sub_comm]
    exact this v u hv hu (le_of_not_ge huv)
  have huvreal : (u : ℝ) ≤ v := huv
  have hupper : dist (f.1 u) (f.1 v) ≤ l * ((v : ℝ) - u) := by
    have hd := hLip.dist_le_mul u v
    change dist (f.1 u) (f.1 v) ≤ l * |(u : ℝ) - v| at hd
    simpa only [abs_of_nonpos (sub_nonpos.mpr huvreal), neg_sub] using hd
  rw [abs_of_nonpos (sub_nonpos.mpr huvreal), neg_sub]
  apply le_antisymm hupper
  by_contra hnot
  have hshort : dist (f.1 u) (f.1 v) < l * ((v : ℝ) - u) := lt_of_not_ge hnot
  let p := closedLoopPath f
  have harcball (s : unitInterval) : p.subpath u v s ∈ closedBall (f.1 t) R := by
    have hs : Set.Icc.convexComb u v s ∈ Icc u v := by
      have hrange : Set.Icc.convexComb u v s ∈ range (Set.Icc.convexComb u v) :=
        mem_range_self s
      rw [Path.range_subpathAux, uIcc_of_le huv] at hrange
      exact hrange
    have hsreal : (u : ℝ) ≤ Set.Icc.convexComb u v s ∧
        (Set.Icc.convexComb u v s : ℝ) ≤ v := hs
    apply hball
    apply abs_lt.mpr
    have hu' := abs_lt.mp hu
    have hv' := abs_lt.mp hv
    constructor <;> linarith
  let y : closedBall (f.1 t) R := ⟨f.1 u, hball u hu⟩
  let z : closedBall (f.1 t) R := ⟨f.1 v, hball v hv⟩
  let m : closedBall (f.1 t) R → closedBall (f.1 t) R → closedBall (f.1 t) R :=
    fun a b => (hcomparison R hR.le hR₁ a b).choose
  have hm : ∀ a b : closedBall (f.1 t) R,
      dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
    fun a b => ⟨(hcomparison R hR.le hR₁ a b).choose_spec.1,
      (hcomparison R hR.le hR₁ a b).choose_spec.2.1⟩
  obtain ⟨Γ, hΓ⟩ := exists_midpoint_metric_path m hm y z
  let arc : Path y z :=
    { toFun := fun s => ⟨p.subpath u v s, harcball s⟩
      continuous_toFun := (p.subpath u v).continuous.subtype_mk harcball
      source' := Subtype.ext (p.subpath u v).source
      target' := Subtype.ext (p.subpath u v).target }
  let q : Path (f.1 u) (f.1 v) := Γ.map continuous_subtype_val
  have hsub : (p.subpath u v).Homotopic q := by
    have h := (SimplyConnectedSpace.paths_homotopic arc Γ).map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(closedBall (f.1 t) R, P.GluedCarrier))
    exact h
  have hqmetric : ∀ s w : unitInterval,
      dist (q s) (q w) = dist (f.1 u) (f.1 v) * |(s : ℝ) - w| := hΓ
  let left := p.subpath 0 u
  let right := p.subpath v 1
  let r := (left.trans q).trans right
  let Q : Path (f.1 0) (f.1 0) := r.cast p.source.symm p.target.symm
  let h : closedLoopMapSet P.GluedCarrier :=
    ⟨Q.toContinuousMap, by change Q 0 = Q 1; rw [Q.source, Q.target]⟩
  have hbase : f.1 0 = h.1 0 := Q.source.symm
  have hQhom : p.Homotopic Q := by
    have hchange := ((Path.Homotopic.refl left).hcomp hsub).hcomp
      (Path.Homotopic.refl right)
    have hsplit₁ : (left.trans (p.subpath u v)).Homotopic (p.subpath 0 v) :=
      ⟨Path.Homotopy.subpathTransSubpath p 0 u v⟩
    have hsplit₂ : ((left.trans (p.subpath u v)).trans right).Homotopic
        ((p.subpath 0 v).trans right) :=
      Path.Homotopic.hcomp hsplit₁ (Path.Homotopic.refl right)
    have hsplit := hsplit₂.trans ⟨Path.Homotopy.subpathTransSubpath p 0 v 1⟩
    have hcast := (hchange.symm.trans hsplit).pathCast p.source.symm p.target.symm
    have hwhole : (p.subpath 0 1).cast p.source.symm p.target.symm = p := by
      apply Path.ext
      funext s
      simp only [Path.cast_coe, Path.subpath_zero_one]
    rw [hwhole] at hcast
    exact hcast.symm
  have hhessential : ¬(closedLoopPath h).Homotopic (Path.refl (h.1 0)) := by
    apply essential_of_homotopic_closedLoop f h hbase hessential
    have heq : (closedLoopPath h).cast hbase hbase = Q := by
      apply Path.ext
      funext s
      rfl
    rw [heq]
    exact hQhom
  have hqLip : LipschitzWith (nndist (f.1 u) (f.1 v)) q := by
    apply LipschitzWith.of_dist_le_mul
    intro s w
    rw [hqmetric s w]
    exact le_rfl
  have hpLip : LipschitzWith ⟨l, hl.le⟩ p := hLip
  have hleftLip := lipschitzWith_path_subpath p hpLip 0 u
  have hrightLip := lipschitzWith_path_subpath p hpLip v 1
  have hrLip := lipschitzWith_path_trans (left.trans q) right
    (lipschitzWith_path_trans left q hleftLip hqLip) hrightLip
  have hhLip : LipschitzWith
      (2 * (2 * (⟨l, hl.le⟩ + nndist (f.1 u) (f.1 v)) + ⟨l, hl.le⟩)) h.1 := by
    apply LipschitzWith.of_dist_le_mul
    intro s w
    exact hrLip.dist_le_mul s w
  have hhcost : eVariationOn h.1 univ < ENNReal.ofReal l := by
    have hleftvar : eVariationOn left univ = ENNReal.ofReal (l * (u : ℝ)) := by
      calc
        _ = eVariationOn f.1 (Icc 0 u) :=
          eVariationOn_path_subpath p (show (0 : unitInterval) ≤ u from u.2.1)
        _ = _ := by
          simpa only [Set.Icc.coe_zero, sub_zero] using
            hvariation 0 u (show (0 : unitInterval) ≤ u from u.2.1)
    have hrightvar : eVariationOn right univ = ENNReal.ofReal (l * (1 - (v : ℝ))) := by
      calc
        _ = eVariationOn f.1 (Icc v 1) :=
          eVariationOn_path_subpath p (show v ≤ (1 : unitInterval) from v.2.2)
        _ = _ := by
          simpa only [Set.Icc.coe_one] using
            hvariation v 1 (show v ≤ (1 : unitInterval) from v.2.2)
    have hqvar : eVariationOn (fun s => q s) univ =
        ENNReal.ofReal (dist (f.1 u) (f.1 v)) :=
      eVariationOn_path_eq_of_metric_segment q hqmetric
    have hcosteq : eVariationOn h.1 univ =
        ENNReal.ofReal (l * (u : ℝ)) + ENNReal.ofReal (dist (f.1 u) (f.1 v)) +
          ENNReal.ofReal (l * (1 - (v : ℝ))) := by
      calc
        _ = eVariationOn (left.trans q) univ + eVariationOn right univ :=
          eVariationOn_path_trans (left.trans q) right
        _ = (eVariationOn left univ + eVariationOn (fun s => q s) univ) +
            eVariationOn right univ :=
          congrArg (fun a => a + eVariationOn right univ) (eVariationOn_path_trans left q)
        _ = _ := congrArg₂ (fun a b => a + b)
          (congrArg₂ (fun a b => a + b) hleftvar hqvar) hrightvar
    rw [hcosteq]
    rw [← ENNReal.ofReal_add (mul_nonneg hl.le u.2.1) dist_nonneg,
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hl.le u.2.1) dist_nonneg)
        (mul_nonneg hl.le (sub_nonneg.mpr v.2.2)), ENNReal.ofReal_lt_ofReal_iff hl]
    nlinarith
  have hhFinite : eVariationOn h.1 univ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hhcost.le
  obtain ⟨r₀, hr₀, hnull⟩ := P.exists_nullhomotopy_radius
  have hhPos : 0 < eVariationOn h.1 univ := by
    have hrle : ENNReal.ofReal r₀ ≤ eVariationOn h.1 univ := by
      apply le_of_not_gt
      exact fun hsmall => hhessential (hnull (h.1 0) (closedLoopPath h) hsmall)
    exact (ENNReal.ofReal_pos.mpr hr₀).trans_le hrle
  have hhRealPos : 0 < (eVariationOn h.1 univ).toReal :=
    ENNReal.toReal_pos hhPos.ne' hhFinite
  obtain ⟨a, haBase, haLip, haVariation, haHom⟩ :=
    exists_lipschitz_arclength_closedLoop h hhLip hhRealPos
  have haEssential := essential_of_homotopic_closedLoop h a haBase hhessential haHom
  have haK : (eVariationOn h.1 univ).toReal ≤ (K : ℝ) := by
    have hreal := ENNReal.toReal_mono (by simp) hhcost.le
    rw [ENNReal.toReal_ofReal hl.le] at hreal
    exact hreal.trans hlK
  have haLipK : LipschitzWith K a.1 := haLip.weaken haK
  have hminA := hmin a haLipK haEssential
  rw [haVariation] at hminA
  exact (not_lt_of_ge hminA) hhcost

end ExerciseGluingPreparation

end SystolicGrowth
