module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainDistance

@[expose] public section

/-!
# Actual two-leg geodesics through an attained common-fin minimizer

The two legs are the original hyperbolic slab segments. Exact attainment of
the cross-copy distance makes their concatenation isometric, including when
one or both legs have zero length. The same minimizing point and its exact
arc-length time are retained for local comparison at the junction.
-/

open Set UpperHalfPlane

namespace SystolicGrowth

/-- Concatenating two isometric intervals whose endpoints realize the sum
of their lengths gives an isometric interval through their common endpoint.
Both zero-length cases are included. -/
theorem exists_isometric_two_leg_interval
    {M : Type*} [MetricSpace M] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (α : Icc (0 : ℝ) a → M) (β : Icc (0 : ℝ) b → M)
    (hα : Isometry α) (hβ : Isometry β)
    (hjoin : α ⟨a, ⟨ha, le_rfl⟩⟩ = β ⟨0, ⟨le_rfl, hb⟩⟩)
    (hdist : dist (α ⟨0, ⟨le_rfl, ha⟩⟩) (β ⟨b, ⟨hb, le_rfl⟩⟩) = a + b) :
    ∃ σ : Icc (0 : ℝ) (a + b) → M,
      Isometry σ ∧
      (∀ s : Icc (0 : ℝ) a,
        σ ⟨s.1, ⟨s.2.1, s.2.2.trans (le_add_of_nonneg_right hb)⟩⟩ = α s) ∧
      (∀ t : Icc (0 : ℝ) b,
        σ ⟨a + t.1, ⟨add_nonneg ha t.2.1, add_le_add le_rfl t.2.2⟩⟩ = β t) := by
  classical
  let σ : Icc (0 : ℝ) (a + b) → M := fun t =>
    if h : t.1 ≤ a then α ⟨t.1, ⟨t.2.1, h⟩⟩
    else β ⟨t.1 - a, ⟨by have := le_of_not_ge h; linarith,
      by have := t.2.2; linarith⟩⟩
  have hleft (s : Icc (0 : ℝ) a) :
      σ ⟨s.1, ⟨s.2.1, s.2.2.trans (le_add_of_nonneg_right hb)⟩⟩ = α s := by
    dsimp only [σ]
    rw [dif_pos s.2.2]
  have hright (t : Icc (0 : ℝ) b) :
      σ ⟨a + t.1, ⟨add_nonneg ha t.2.1, add_le_add le_rfl t.2.2⟩⟩ = β t := by
    dsimp only [σ]
    by_cases ht : a + t.1 ≤ a
    · rw [dif_pos ht]
      have ht0 : t.1 = 0 := by have := t.2.1; linarith
      have hta : (⟨a + t.1, by exact ⟨add_nonneg ha t.2.1, ht⟩⟩ : Icc (0 : ℝ) a) =
          ⟨a, ⟨ha, le_rfl⟩⟩ := by apply Subtype.ext; dsimp; linarith
      have ht' : t = ⟨0, ⟨le_rfl, hb⟩⟩ := Subtype.ext ht0
      rw [hta, hjoin, ht']
    · rw [dif_neg ht]
      congr 1
      apply Subtype.ext
      dsimp
      ring
  have hupper : ∀ s t : Icc (0 : ℝ) (a + b), s.1 ≤ t.1 →
      dist (σ s) (σ t) ≤ t.1 - s.1 := by
    intro s t hst
    by_cases hs : s.1 ≤ a
    · by_cases ht : t.1 ≤ a
      · dsimp only [σ]
        rw [dif_pos hs, dif_pos ht, hα.dist_eq, Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hst)]
        linarith
      · have hta : 0 ≤ t.1 - a := by linarith [lt_of_not_ge ht]
        have htb : t.1 - a ≤ b := by have := t.2.2; linarith
        dsimp only [σ]
        rw [dif_pos hs, dif_neg ht]
        calc
          dist (α ⟨s.1, ⟨s.2.1, hs⟩⟩) (β ⟨t.1 - a, ⟨hta, htb⟩⟩) ≤
              dist (α ⟨s.1, ⟨s.2.1, hs⟩⟩) (α ⟨a, ⟨ha, le_rfl⟩⟩) +
                dist (α ⟨a, ⟨ha, le_rfl⟩⟩) (β ⟨t.1 - a, ⟨hta, htb⟩⟩) :=
            dist_triangle _ _ _
          _ = (a - s.1) + (t.1 - a) := by
            rw [hα.dist_eq, hjoin, hβ.dist_eq]
            simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
              abs_of_nonneg hta, abs_of_nonpos (sub_nonpos.mpr hs)]
            ring
          _ = t.1 - s.1 := by ring
    · have ht : ¬t.1 ≤ a := by linarith [lt_of_not_ge hs]
      dsimp only [σ]
      rw [dif_neg hs, dif_neg ht, hβ.dist_eq, Subtype.dist_eq, Real.dist_eq]
      have hneg : s.1 - a - (t.1 - a) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
  let start : Icc (0 : ℝ) (a + b) := ⟨0, ⟨le_rfl, add_nonneg ha hb⟩⟩
  let finish : Icc (0 : ℝ) (a + b) := ⟨a + b, ⟨add_nonneg ha hb, le_rfl⟩⟩
  have hstart : σ start = α ⟨0, ⟨le_rfl, ha⟩⟩ := hleft ⟨0, ⟨le_rfl, ha⟩⟩
  have hfinish : σ finish = β ⟨b, ⟨hb, le_rfl⟩⟩ := hright ⟨b, ⟨hb, le_rfl⟩⟩
  have hends : dist (σ start) (σ finish) = a + b := by rw [hstart, hfinish, hdist]
  have hdist_ordered (s t : Icc (0 : ℝ) (a + b)) (hst : s.1 ≤ t.1) :
      dist (σ s) (σ t) = t.1 - s.1 := by
    apply le_antisymm (hupper s t hst)
    have h0 := hupper start s s.2.1
    have h1 := hupper t finish t.2.2
    have htri := dist_triangle4 (σ start) (σ s) (σ t) (σ finish)
    rw [hends] at htri
    dsimp only [start, finish] at h0 h1
    linarith
  refine ⟨σ, Isometry.of_dist_eq ?_, hleft, hright⟩
  intro s t
  rw [Subtype.dist_eq, Real.dist_eq]
  rcases le_total s.1 t.1 with hst | hts
  · rw [hdist_ordered s t hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [dist_comm, hdist_ordered t s hts, abs_of_nonneg (sub_nonneg.mpr hts)]

theorem Internal.GluingCollarFinChainGeodesicHelpers.div_mem_unitInterval_of_mem_distance_interval {d t : ℝ}
    (hd : 0 ≤ d) (ht : t ∈ Icc (0 : ℝ) d) : t / d ∈ Icc (0 : ℝ) 1 := by
  by_cases hd0 : d = 0
  · have ht0 : t = 0 := by rw [hd0] at ht; linarith [ht.1, ht.2]
    simp [hd0, ht0]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    exact ⟨div_nonneg ht.1 hd, (div_le_one hdpos).mpr ht.2⟩

/-- The explicit hyperbolic interpolation in a native radial window,
parametrized by arc length rather than by unit time. -/
noncomputable def gluingFinFermiRadialWindowArc
    {lam R : ℝ} (hlam : 0 < lam)
    (x y : gluingFinFermiRadialWindow lam R)
    (t : Icc (0 : ℝ) (dist x y)) : gluingFinFermiRadialWindow lam R :=
  ⟨Vendored.RiemannDynamics.geodInterp x.1 y.1 (t.1 / dist x y),
    gluingFinFermiRadialWindow_geodSeg_subset hlam x.2 y.2
      (Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _
        (Internal.GluingCollarFinChainGeodesicHelpers.div_mem_unitInterval_of_mem_distance_interval dist_nonneg t.2))⟩

/-- Arc-length interpolation in the actual hyperbolic slab is isometric,
even when its endpoint distance is zero. -/
theorem gluingFinFermiRadialWindowArc_isometry
    {lam R : ℝ} (hlam : 0 < lam) (x y : gluingFinFermiRadialWindow lam R) :
    Isometry (gluingFinFermiRadialWindowArc hlam x y) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq]
  change dist
    (Vendored.RiemannDynamics.geodInterp x.1 y.1 (s.1 / dist x y))
    (Vendored.RiemannDynamics.geodInterp x.1 y.1 (t.1 / dist x y)) = |s.1 - t.1|
  rw [Vendored.RiemannDynamics.dist_geodInterp_pair]
  change |s.1 / dist x y - t.1 / dist x y| * dist x y = |s.1 - t.1|
  by_cases hd : dist x y = 0
  · have hs : s.1 = 0 := by linarith [s.2.1, s.2.2]
    have ht : t.1 = 0 := by linarith [t.2.1, t.2.2]
    simp [hd, hs, ht]
  · rw [← sub_div, abs_div, abs_of_nonneg dist_nonneg, div_mul_cancel₀ _ hd]

@[simp] theorem gluingFinFermiRadialWindowArc_start
    {lam R : ℝ} (hlam : 0 < lam) (x y : gluingFinFermiRadialWindow lam R) :
    gluingFinFermiRadialWindowArc hlam x y ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x := by
  apply Subtype.ext
  simp [gluingFinFermiRadialWindowArc, Vendored.RiemannDynamics.geodInterp_zero]

@[simp] theorem gluingFinFermiRadialWindowArc_finish
    {lam R : ℝ} (hlam : 0 < lam) (x y : gluingFinFermiRadialWindow lam R) :
    gluingFinFermiRadialWindowArc hlam x y
      ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  apply Subtype.ext
  dsimp only [gluingFinFermiRadialWindowArc]
  by_cases hd : dist x y = 0
  · have hxy : x = y := dist_eq_zero.mp hd
    simp [hxy, Vendored.RiemannDynamics.geodInterp_self]
  · rw [div_self hd, Vendored.RiemannDynamics.geodInterp_one]

/-- The two actual slab segments through a specified attained seam point
form an isometric path. Their junction time is the left leg length, and the
closed parameter intervals on either side remain in their original copies. -/
theorem gluingCollarFiniteMetricGlue_twoLeg_segment_of_seam
    {r R lam ε : ℝ} (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R)
    (q : gluingCollarFiniteUpperFin r R lam ε)
    (hq : dist
        (Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) x)
        (Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) y) =
      dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist (gluingCollarFiniteMetricGlueRight r R lam ε q) y) :
    let L := Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let d := dist (L x) (Rg y)
    ∃ τ : Icc (0 : ℝ) d, ∃ σ : Icc (0 : ℝ) d →
        gluingCollarFiniteMetricGlueSpace r R lam ε,
      Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = L x ∧
      σ ⟨d, ⟨dist_nonneg, le_rfl⟩⟩ = Rg y ∧
      τ.1 = dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) ∧
      σ τ = L (gluingCollarFiniteMetricGlueLeft r R lam ε q) ∧
      (∀ t, t.1 ≤ τ.1 → σ t ∈ Set.range L) ∧
      (∀ t, τ.1 ≤ t.1 → σ t ∈ Set.range Rg) := by
  dsimp only
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let J := gluingCollarFiniteMetricGlueRight r R lam ε
  let L := Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let a := dist x (I q)
  let b := dist (J q) y
  let α := L ∘ gluingFinFermiRadialWindowArc hlam x (I q)
  let β := Rg ∘ gluingFinFermiRadialWindowArc hlam (J q) y
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hα : Isometry α :=
    (gluingCollarFiniteMetricGlueLeft_toGlue_isometry r R lam ε).comp
      (gluingFinFermiRadialWindowArc_isometry hlam x (I q))
  have hβ : Isometry β :=
    (gluingCollarFiniteMetricGlueRight_toGlue_isometry r R lam ε).comp
      (gluingFinFermiRadialWindowArc_isometry hlam (J q) y)
  have hjoin : α ⟨a, ⟨ha, le_rfl⟩⟩ = β ⟨0, ⟨le_rfl, hb⟩⟩ := by
    dsimp only [α, β, Function.comp_apply]
    rw [gluingFinFermiRadialWindowArc_finish, gluingFinFermiRadialWindowArc_start]
    exact congrFun (gluingCollarFiniteMetricGlue_commute r R lam ε) q
  have hd : dist (α ⟨0, ⟨le_rfl, ha⟩⟩) (β ⟨b, ⟨hb, le_rfl⟩⟩) = a + b := by
    dsimp only [α, β, Function.comp_apply]
    rw [gluingFinFermiRadialWindowArc_start, gluingFinFermiRadialWindowArc_finish]
    exact hq
  have hresult : ∃ τ : Icc (0 : ℝ) (a + b),
      ∃ σ : Icc (0 : ℝ) (a + b) → gluingCollarFiniteMetricGlueSpace r R lam ε,
        Isometry σ ∧
        σ ⟨0, ⟨le_rfl, add_nonneg ha hb⟩⟩ = L x ∧
        σ ⟨a + b, ⟨add_nonneg ha hb, le_rfl⟩⟩ = Rg y ∧
        τ.1 = a ∧ σ τ = L (I q) ∧
        (∀ t, t.1 ≤ τ.1 → σ t ∈ Set.range L) ∧
        (∀ t, τ.1 ≤ t.1 → σ t ∈ Set.range Rg) := by
    obtain ⟨σ, hσ, hleft, hright⟩ :=
      exists_isometric_two_leg_interval ha hb α β hα hβ hjoin hd
    let τ : Icc (0 : ℝ) (a + b) := ⟨a, ⟨ha, le_add_of_nonneg_right hb⟩⟩
    refine ⟨τ, σ, hσ, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simpa only [α, Function.comp_apply, gluingFinFermiRadialWindowArc_start] using
        hleft ⟨0, ⟨le_rfl, ha⟩⟩
    · simpa only [β, Function.comp_apply, b, gluingFinFermiRadialWindowArc_finish] using
        hright ⟨b, ⟨hb, le_rfl⟩⟩
    · simpa only [α, Function.comp_apply, a, τ, gluingFinFermiRadialWindowArc_finish] using
        hleft ⟨a, ⟨ha, le_rfl⟩⟩
    · intro t ht
      let s : Icc (0 : ℝ) a := ⟨t.1, ⟨t.2.1, ht⟩⟩
      have hs := hleft s
      change σ t = L (gluingFinFermiRadialWindowArc hlam x (I q) s) at hs
      exact ⟨_, hs.symm⟩
    · intro t ht
      let s : Icc (0 : ℝ) b := ⟨t.1 - a, ⟨by change a ≤ t.1 at ht; linarith,
        by have := t.2.2; linarith⟩⟩
      have hs := hright s
      have ht' : (⟨a + s.1, ⟨add_nonneg ha s.2.1, add_le_add le_rfl s.2.2⟩⟩ :
          Icc (0 : ℝ) (a + b)) = t := by apply Subtype.ext; dsimp [s]; ring
      rw [ht'] at hs
      exact ⟨_, hs.symm⟩
  change dist (L x) (Rg y) = a + b at hq
  let P : ℝ → Prop := fun d =>
    ∃ τ : Icc (0 : ℝ) d, ∃ σ : Icc (0 : ℝ) d →
        gluingCollarFiniteMetricGlueSpace r R lam ε,
      Isometry σ ∧
      (∀ t, t.1 = 0 → σ t = L x) ∧
      (∀ t, t.1 = d → σ t = Rg y) ∧
      τ.1 = a ∧ σ τ = L (I q) ∧
      (∀ t, t.1 ≤ τ.1 → σ t ∈ Set.range L) ∧
      (∀ t, τ.1 ≤ t.1 → σ t ∈ Set.range Rg)
  have hp : P (a + b) := by
    obtain ⟨τ, σ, hσ, hstart, hfinish, hτ, hseam, hleft, hright⟩ := hresult
    refine ⟨τ, σ, hσ, ?_, ?_, hτ, hseam, hleft, hright⟩
    · intro t ht
      have ht' : t = ⟨0, ⟨le_rfl, add_nonneg ha hb⟩⟩ := Subtype.ext ht
      rw [ht']
      exact hstart
    · intro t ht
      have ht' : t = ⟨a + b, ⟨add_nonneg ha hb, le_rfl⟩⟩ := Subtype.ext ht
      rw [ht']
      exact hfinish
  have hp' : P (dist (L x) (Rg y)) := by rw [hq]; exact hp
  obtain ⟨τ, σ, hσ, hstart, hfinish, hτ, hseam, hleft, hright⟩ := hp'
  exact ⟨τ, σ, hσ, hstart _ rfl, hfinish _ rfl, hτ, hseam, hleft, hright⟩

/-- Every cross-copy pair has an actual two-leg isometric segment through
one and the same attained common-fin minimizer. Its exact junction and
closed-copy ranges are retained for the local-to-global comparison proof. -/
theorem gluingCollarFiniteMetricGlue_cross_exists_twoLeg_isometric_segment
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (x y : gluingFinFermiRadialWindow lam R) :
    let L := Metric.toGlueL (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let d := dist (L x) (Rg y)
    ∃ q : gluingCollarFiniteUpperFin r R lam ε,
      d = dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) +
        dist (gluingCollarFiniteMetricGlueRight r R lam ε q) y ∧
      ∃ τ : Icc (0 : ℝ) d, ∃ σ : Icc (0 : ℝ) d →
          gluingCollarFiniteMetricGlueSpace r R lam ε,
        Isometry σ ∧
        σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = L x ∧
        σ ⟨d, ⟨dist_nonneg, le_rfl⟩⟩ = Rg y ∧
        τ.1 = dist x (gluingCollarFiniteMetricGlueLeft r R lam ε q) ∧
        σ τ = L (gluingCollarFiniteMetricGlueLeft r R lam ε q) ∧
        (∀ t, t.1 ≤ τ.1 → σ t ∈ Set.range L) ∧
        (∀ t, τ.1 ≤ t.1 → σ t ∈ Set.range Rg) := by
  dsimp only
  obtain ⟨q, hq⟩ := gluingCollarFiniteMetricGlue_cross_dist_attained
    (r := r) (R := R) (lam := lam) (ε := ε) hR hlam x y
  rw [dist_comm y (gluingCollarFiniteMetricGlueRight r R lam ε q)] at hq
  exact ⟨q, hq, gluingCollarFiniteMetricGlue_twoLeg_segment_of_seam hlam x y q hq⟩

#print axioms exists_isometric_two_leg_interval
#print axioms gluingFinFermiRadialWindowArc_isometry
#print axioms gluingCollarFiniteMetricGlue_twoLeg_segment_of_seam
#print axioms gluingCollarFiniteMetricGlue_cross_exists_twoLeg_isometric_segment

end SystolicGrowth
