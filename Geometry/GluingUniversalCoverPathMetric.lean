module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCover
public import Geometry.MetricPathVariation
public import Geometry.GluingUniversalCoverPathDistance
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
# Native local geometry for the universal-cover path metric

The local inverse of the original covering lifts actual native metric
segments. Their projected variation is exactly the downstairs distance.
This supplies the local metric construction without changing the cover's
carrier or quotient topology.
-/

open Set Metric Topology
open scoped unitInterval ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The selected local inverse of the original endpoint covering at an
actual native cover point. -/
noncomputable def gluedUniversalCoverLocalInverse
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    OpenPartialHomeomorph P.GluedCarrier (P.basedTopologicalUniversalCover x) :=
  (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt e

/-- Every native neighborhood contains a local lifted metric ball. Actual
downstairs metric segments lift in the selected sheet and have exact projected
variation; the sheet and radius are constructed from the covering and W. -/
theorem exists_gluedUniversalCover_local_metric_lift
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x)
    (W : Set (P.basedTopologicalUniversalCover x)) (hW : W ∈ 𝓝 e) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    let φ := P.gluedUniversalCoverLocalInverse x e
    ∃ r > 0,
      ball (P.gluedUniversalCoverProjection x e) r ⊆ φ.source ∧
      φ '' ball (P.gluedUniversalCoverProjection x e) r ⊆ W ∧
      ∀ y ∈ ball (P.gluedUniversalCoverProjection x e) r,
        ∃ Γ : Path e (φ y),
          eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ =
            edist (P.gluedUniversalCoverProjection x e) y := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let hp := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph
  let φ := P.gluedUniversalCoverLocalInverse x e
  obtain ⟨V, hVW, hVopen, heV⟩ := mem_nhds_iff.mp hW
  have hsource : IsOpen (φ.source ∩ φ ⁻¹' V) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hVopen
  have he : P.gluedUniversalCoverProjection x e ∈ φ.source ∩ φ ⁻¹' V := by
    refine ⟨hp.apply_self_mem_localInverseAt_source, ?_⟩
    change hp.localInverseAt e (P.gluedUniversalCoverProjection x e) ∈ V
    simpa only [hp.localInverseAt_apply_self] using heV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hsource _ he
  refine ⟨r, hr, (fun y hy => (hball hy).1), ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact hVW (hball hy).2
  · intro y hy
    obtain ⟨β, hβ⟩ := P.gluedIntrinsicMetric_exists_metric_path
      (P.gluedUniversalCoverProjection x e) y
    have hβball : ∀ t : unitInterval,
        β t ∈ ball (P.gluedUniversalCoverProjection x e) r := by
      intro t
      apply Metric.mem_ball.mpr
      have hdist := hβ t 0
      rw [β.source] at hdist
      rw [hdist]
      simp only [Set.Icc.coe_zero, sub_zero, abs_of_nonneg t.2.1]
      have hy' : dist (P.gluedUniversalCoverProjection x e) y < r := by
        simpa only [Metric.mem_ball, dist_comm] using hy
      exact (mul_le_of_le_one_right dist_nonneg t.2.2).trans_lt hy'
    have hβsource : ∀ t : unitInterval, β t ∈ φ.source :=
      fun t => (hball (hβball t)).1
    let Γ : Path e (φ y) :=
      { toFun := fun t => φ (β t)
        continuous_toFun := φ.continuousOn_toFun.comp_continuous β.continuous hβsource
        source' := by
          rw [β.source]
          exact hp.localInverseAt_apply_self
        target' := by rw [β.target] }
    have hproj : P.gluedUniversalCoverProjection x ∘ Γ = β := by
      funext t
      exact hp.apply_localInverseAt_of_mem (hβsource t)
    refine ⟨Γ, ?_⟩
    rw [hproj, eVariationOn_path_eq_of_metric_segment β hβ, edist_dist]

/-- Every positive path-distance ball is a neighborhood in the original
cover topology, using the actual lifted metric segments in one local sheet. -/
theorem gluedUniversalCover_pathDistance_ball_mem_nhds
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) {c : ℝ≥0∞} (hc : 0 < c) :
    {f | P.gluedUniversalCoverPathDistance x e f < c} ∈ 𝓝 e := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let hp := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph
  let φ := P.gluedUniversalCoverLocalInverse x e
  obtain ⟨r, hr, hsource, _, hpath⟩ :=
    P.exists_gluedUniversalCover_local_metric_lift x e univ Filter.univ_mem
  obtain ⟨s, hs0, hsc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have hs : 0 < (s : ℝ) := by exact_mod_cast hs0
  let δ : ℝ := min r (s : ℝ)
  have hδ : 0 < δ := lt_min hr hs
  have hδr : δ ≤ r := min_le_left _ _
  have hδs : ENNReal.ofReal δ ≤ (s : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (min_le_right r (s : ℝ))
  have hδsource : ball (P.gluedUniversalCoverProjection x e) δ ⊆ φ.source :=
    (Metric.ball_subset_ball hδr).trans hsource
  have hopen : IsOpen (φ '' ball (P.gluedUniversalCoverProjection x e) δ) :=
    φ.isOpen_image_of_subset_source isOpen_ball hδsource
  have he : e ∈ φ '' ball (P.gluedUniversalCoverProjection x e) δ :=
    ⟨P.gluedUniversalCoverProjection x e, Metric.mem_ball_self hδ,
      hp.localInverseAt_apply_self⟩
  apply Filter.mem_of_superset (hopen.mem_nhds he)
  rintro f ⟨y, hy, rfl⟩
  obtain ⟨Γ, hΓ⟩ := hpath y ((Metric.ball_subset_ball hδr) hy)
  have hd : P.gluedUniversalCoverPathDistance x e (φ y) ≤
      edist (P.gluedUniversalCoverProjection x e) y := by
    exact (P.gluedUniversalCoverPathDistance_le_projectedPathVariation x Γ).trans_eq hΓ
  have hy' : dist (P.gluedUniversalCoverProjection x e) y < δ := by
    simpa only [Metric.mem_ball, dist_comm] using hy
  have hed : edist (P.gluedUniversalCoverProjection x e) y < ENNReal.ofReal δ :=
    edist_lt_ofReal.mpr hy'
  exact hd.trans_lt (hed.trans_le hδs |>.trans hsc)

/-- Every original cover neighborhood contains a positive path-distance
ball. The target-systole gap rules out landing in a different sheet over the
same nearby base point; no compatible cover metric is assumed. -/
theorem exists_gluedUniversalCover_pathDistance_ball_subset
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x)
    (W : Set (P.basedTopologicalUniversalCover x)) (hW : W ∈ 𝓝 e) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      {f | P.gluedUniversalCoverPathDistance x e f < c} ⊆ W := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let hp := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph
  let φ := P.gluedUniversalCoverLocalInverse x e
  obtain ⟨r, hr, hsource, himage, hpath⟩ :=
    P.exists_gluedUniversalCover_local_metric_lift x e W hW
  let δ : ℝ := min r (targetSystole C g / 3)
  have hδ : 0 < δ := lt_min hr (div_pos P.target_pos (by norm_num))
  have hδr : δ ≤ r := min_le_left _ _
  have hsum : ENNReal.ofReal δ + ENNReal.ofReal δ ≤
      ENNReal.ofReal (targetSystole C g) := by
    rw [← ENNReal.ofReal_add hδ.le hδ.le]
    apply ENNReal.ofReal_le_ofReal
    have hδL : δ ≤ targetSystole C g / 3 := min_le_right _ _
    linarith [P.target_pos]
  refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.mpr hδ, ?_⟩
  intro f hf
  have hproj : edist (P.gluedUniversalCoverProjection x e)
      (P.gluedUniversalCoverProjection x f) < ENNReal.ofReal δ :=
    (P.gluedUniversalCover_edist_le_pathDistance x e f).trans_lt hf
  have hfbase : P.gluedUniversalCoverProjection x f ∈
      ball (P.gluedUniversalCoverProjection x e) r := by
    apply Metric.mem_ball.mpr
    simpa only [dist_comm] using (edist_lt_ofReal.mp hproj).trans_le hδr
  let f₀ := φ (P.gluedUniversalCoverProjection x f)
  have hf₀W : f₀ ∈ W := himage ⟨_, hfbase, rfl⟩
  have hf₀proj : P.gluedUniversalCoverProjection x f₀ =
      P.gluedUniversalCoverProjection x f :=
    hp.apply_localInverseAt_of_mem (hsource hfbase)
  obtain ⟨Γ, hΓ⟩ := hpath _ hfbase
  have hsmall : P.gluedUniversalCoverPathDistance x e f₀ < ENNReal.ofReal δ :=
    ((P.gluedUniversalCoverPathDistance_le_projectedPathVariation x Γ).trans_eq hΓ).trans_lt hproj
  have heq : f = f₀ := by
    by_contra hne
    have hgap := P.target_le_gluedUniversalCoverPathDistance_of_same_fiber_ne
      x hf₀proj.symm hne
    have htriangle := P.gluedUniversalCoverPathDistance_triangle x f₀ e f
    rw [P.gluedUniversalCoverPathDistance_comm x f₀ e] at htriangle
    have hlt := htriangle.trans_lt (ENNReal.add_lt_add hsmall hf)
    exact (not_lt_of_ge hgap) (hlt.trans_le hsum)
  exact heq.symm ▸ hf₀W

/-- The canonical path-distance balls form a basis for the unchanged native
cover topology. -/
theorem gluedUniversalCover_pathDistance_nhds_basis
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    (𝓝 e).HasBasis (fun c : ℝ≥0∞ => 0 < c)
      (fun c => {f | P.gluedUniversalCoverPathDistance x e f < c}) := by
  apply Filter.hasBasis_iff.mpr
  intro W
  constructor
  · exact P.exists_gluedUniversalCover_pathDistance_ball_subset x e W
  · rintro ⟨c, hc, hsub⟩
    exact Filter.mem_of_superset (P.gluedUniversalCover_pathDistance_ball_mem_nhds x e hc) hsub

/-- The actual cover's canonical path distance defines an extended metric
with its original topology, not a replacement topology. -/
@[instance_reducible] noncomputable def gluedUniversalCoverPathEMetricSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    EMetricSpace (P.basedTopologicalUniversalCover x) where
  toPseudoEMetricSpace := PseudoEMetricSpace.ofEDistOfTopology
    (P.gluedUniversalCoverPathDistance x)
    (P.gluedUniversalCoverPathDistance_self x)
    (P.gluedUniversalCoverPathDistance_comm x)
    (P.gluedUniversalCoverPathDistance_triangle x)
    (P.gluedUniversalCover_pathDistance_nhds_basis x)
  eq_of_edist_eq_zero := fun {a b} h =>
    (P.gluedUniversalCoverPathDistance_eq_zero_iff x a b).mp h

/-- The native cover is connected, so its open-and-closed finite-distance
component is the whole cover. Its canonical path distance is therefore finite
between every pair; finite variation is not an extra input. -/
theorem gluedUniversalCoverPathDistance_ne_top
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverPathDistance x e f ≠ ∞ := by
  letI := P.gluedUniversalCoverPathEMetricSpace x
  have hclopen : IsClopen (Metric.eball e ∞) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hall : Metric.eball e ∞ = Set.univ :=
    hclopen.eq_univ ⟨e, Metric.mem_eball_self ENNReal.zero_lt_top⟩
  have hf : f ∈ Metric.eball e ∞ := by rw [hall]; exact Set.mem_univ f
  change edist e f ≠ ∞
  exact ne_top_of_lt (by simpa only [Metric.mem_eball, edist_comm] using hf)

/-- The canonical finite path metric on the actual native cover. Both the
underlying carrier and topology are retained by the Mathlib construction. -/
@[instance_reducible] noncomputable def gluedUniversalCoverPathMetricSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    MetricSpace (P.basedTopologicalUniversalCover x) := by
  letI := P.gluedUniversalCoverPathEMetricSpace x
  exact EMetricSpace.toMetricSpace (P.gluedUniversalCoverPathDistance_ne_top x)

/-- The actual projection is nonexpanding for the two native metrics. -/
theorem gluedUniversalCoverProjection_pathMetric_lipschitz
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := P.gluedUniversalCoverPathMetricSpace x
    LipschitzWith 1 (P.gluedUniversalCoverProjection x) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI := P.gluedUniversalCoverPathMetricSpace x
  apply LipschitzWith.of_edist_le
  intro e f
  change edist (P.gluedUniversalCoverProjection x e)
    (P.gluedUniversalCoverProjection x f) ≤ P.gluedUniversalCoverPathDistance x e f
  exact P.gluedUniversalCover_edist_le_pathDistance x e f

/-- Every genuine native deck map is an isometry of the constructed path
metric, because it preserves every projected path cost. -/
theorem gluedUniversalCoverDeck_pathMetric_isometry
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    Isometry τ.val := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  intro e f
  exact P.gluedUniversalCoverPathDistance_deck_invariant x τ e f

/-- The length of every actual native cover path is exactly the intrinsic
variation of its projection, including paths of infinite variation. -/
theorem gluedUniversalCoverPathMetric_variation_eq_projected
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e f : P.basedTopologicalUniversalCover x} (Γ : Path e f) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := P.gluedUniversalCoverPathMetricSpace x
    eVariationOn Γ univ =
      eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI := P.gluedUniversalCoverPathMetricSpace x
  let β := Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous
  apply le_antisymm
  · apply iSup_le
    rintro ⟨m, u, hu, _⟩
    calc
      (∑ i ∈ Finset.range m, edist (Γ (u (i + 1))) (Γ (u i))) ≤
          ∑ i ∈ Finset.range m, eVariationOn β (Icc (u i) (u (i + 1))) := by
        apply Finset.sum_le_sum
        intro i _
        rw [edist_comm]
        have h := P.gluedUniversalCoverPathDistance_le_projectedPathVariation x
          (Γ.subpath (u i) (u (i + 1)))
        change edist (Γ (u i)) (Γ (u (i + 1))) ≤
          eVariationOn (β.subpath (u i) (u (i + 1))) univ at h
        rw [eVariationOn_path_subpath β (hu (Nat.le_succ i))] at h
        exact h
      _ = eVariationOn β (Icc (u 0) (u m)) := eVariationOn.sum' β hu
      _ ≤ eVariationOn β univ := eVariationOn.mono β (subset_univ _)
  · simpa only [one_mul, ENNReal.coe_one] using
      ((P.gluedUniversalCoverProjection_pathMetric_lipschitz x).lipschitzOnWith).comp_eVariationOn_le
        (g := Γ) (s := univ) (mapsTo_univ _ _)

/-- The constructed native cover metric is the intrinsic length metric of
its actual continuous paths, not only an infimum of downstairs path costs. -/
theorem gluedUniversalCoverPathMetric_edist_eq_iInf_variation
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := P.gluedUniversalCoverPathMetricSpace x
    edist e f = ⨅ Γ : Path e f, eVariationOn Γ univ := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI := P.gluedUniversalCoverPathMetricSpace x
  change (⨅ Γ : Path e f, P.gluedUniversalCoverProjectedPathVariation x Γ) = _
  congr 1
  funext Γ
  exact (P.gluedUniversalCoverPathMetric_variation_eq_projected x Γ).symm

/-- The original downstairs distance is attained by an actual deck translate
in the constructed cover metric. Lift a genuine downstairs metric segment,
then identify its endpoint with the prescribed fiber by deck transitivity. -/
theorem exists_gluedUniversalCoverDeck_dist_eq_projection_dist
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := P.gluedUniversalCoverPathMetricSpace x
    ∃ τ : P.gluedUniversalCoverDeckGroup x,
      dist e (τ.val f) = dist (P.gluedUniversalCoverProjection x e)
        (P.gluedUniversalCoverProjection x f) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI := P.gluedUniversalCoverPathMetricSpace x
  obtain ⟨β, hβ⟩ := P.gluedIntrinsicMetric_exists_metric_path
    (P.gluedUniversalCoverProjection x e) (P.gluedUniversalCoverProjection x f)
  let F := P.gluedUniversalCoverPathLift x e β
  let Γ : Path e (F 1) :=
    { toContinuousMap := F
      source' := P.gluedUniversalCoverPathLift_zero x e β
      target' := rfl }
  have hproj : P.gluedUniversalCoverProjection x ∘ Γ = β := by
    funext t
    exact P.gluedUniversalCoverProjection_pathLift x e β t
  have hfiber : P.gluedUniversalCoverProjection x f =
      P.gluedUniversalCoverProjection x (F 1) := by
    rw [P.gluedUniversalCoverProjection_pathLift x e β 1, β.target]
  obtain ⟨τ, hτ⟩ := P.exists_gluedUniversalCoverDeck_of_projection_eq x f (F 1) hfiber
  refine ⟨τ, ?_⟩
  have hupper : edist e (F 1) ≤
      edist (P.gluedUniversalCoverProjection x e)
        (P.gluedUniversalCoverProjection x f) := by
    change P.gluedUniversalCoverPathDistance x e (F 1) ≤ _
    have hcost := P.gluedUniversalCoverPathDistance_le_projectedPathVariation x Γ
    change P.gluedUniversalCoverPathDistance x e (F 1) ≤
      eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ at hcost
    rw [hproj, eVariationOn_path_eq_of_metric_segment β hβ] at hcost
    simpa only [edist_dist] using hcost
  have hlower := P.gluedUniversalCover_edist_le_pathDistance x e (F 1)
  change edist (P.gluedUniversalCoverProjection x e)
    (P.gluedUniversalCoverProjection x (F 1)) ≤ edist e (F 1) at hlower
  rw [P.gluedUniversalCoverProjection_pathLift x e β 1, β.target] at hlower
  rw [hτ]
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
    congrArg ENNReal.toReal (le_antisymm hupper hlower)

/-- Every nonidentity deck displacement pays the target at every native
cover point, in the constructed actual finite path metric. -/
theorem targetSystole_le_gluedUniversalCoverDeck_displacement
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (hτ : τ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    targetSystole C g ≤ dist e (τ.val e) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  have h := P.target_le_gluedUniversalCoverPathDistance_of_deck_ne_one x τ hτ e
  change ENNReal.ofReal (targetSystole C g) ≤ edist e (τ.val e) at h
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

/-- The coherent fundamental-group action has the same every-point real
displacement bound, without an assumed representation or metric upstairs. -/
theorem targetSystole_le_gluedUniversalCoverFundamentalGroup_displacement
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) (hγ : γ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    letI := P.gluedUniversalCoverFundamentalGroupMulAction x
    targetSystole C g ≤ dist e (γ • e) := by
  exact P.targetSystole_le_gluedUniversalCoverDeck_displacement x
    (P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ)
    (P.gluedUniversalCoverFundamentalGroupDeckEquiv_ne_one x γ hγ) e

#print axioms exists_gluedUniversalCover_local_metric_lift
#print axioms gluedUniversalCover_pathDistance_ball_mem_nhds
#print axioms exists_gluedUniversalCover_pathDistance_ball_subset
#print axioms gluedUniversalCover_pathDistance_nhds_basis
#print axioms gluedUniversalCoverPathEMetricSpace
#print axioms gluedUniversalCoverPathDistance_ne_top
#print axioms gluedUniversalCoverPathMetricSpace
#print axioms gluedUniversalCoverProjection_pathMetric_lipschitz
#print axioms gluedUniversalCoverDeck_pathMetric_isometry
#print axioms gluedUniversalCoverPathMetric_variation_eq_projected
#print axioms gluedUniversalCoverPathMetric_edist_eq_iInf_variation
#print axioms exists_gluedUniversalCoverDeck_dist_eq_projection_dist
#print axioms targetSystole_le_gluedUniversalCoverDeck_displacement
#print axioms targetSystole_le_gluedUniversalCoverFundamentalGroup_displacement

end SystolicGrowth.ExerciseGluingPreparation
