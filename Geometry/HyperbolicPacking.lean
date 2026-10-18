module

public import Geometry.HyperbolicBallVolume
public import Geometry.RiemannDynamicsBridge
public import Mathlib.SetTheory.Cardinal.Free

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Pointwise UpperHalfPlane

namespace SystolicGrowth

/-! ## Packing estimates in the hyperbolic plane

The results here isolate the measure-theoretic part of the disk-packing
argument.  They use only the invariant measure on the upper half-plane and
the explicit ball-volume lower bound; no quotient-area or Gauss--Bonnet input
is needed.
-/

/-- The measure of a finite disjoint union of equal-radius hyperbolic balls is
the number of balls times the measure of one ball. -/
theorem volume_iUnion_balls_eq_card_mul (centers : Finset ℍ) (r : ℝ)
    (hdisjoint : Set.PairwiseDisjoint (centers : Set ℍ)
      fun z ↦ Metric.ball z r) :
    volume (⋃ z ∈ centers, Metric.ball z r) =
      (centers.card : ℝ≥0∞) * volume (Metric.ball (UpperHalfPlane.I : ℍ) r) := by
  rw [measure_biUnion_finset hdisjoint fun _z _hz ↦ measurableSet_ball]
  simp [volume_ball_eq_volume_ball_I]

/-- A finite family of pairwise-disjoint equal-radius balls contained in a
set cannot have more total ball area than that set. -/
theorem card_mul_volume_ball_le_volume_of_iUnion_subset
    (centers : Finset ℍ) (r : ℝ) {U : Set ℍ}
    (hdisjoint : Set.PairwiseDisjoint (centers : Set ℍ)
      fun z ↦ Metric.ball z r)
    (hsubset : (⋃ z ∈ centers, Metric.ball z r) ⊆ U) :
    (centers.card : ℝ≥0∞) * volume (Metric.ball (UpperHalfPlane.I : ℍ) r) ≤
      volume U := by
  calc
    (centers.card : ℝ≥0∞) * volume (Metric.ball (UpperHalfPlane.I : ℍ) r) =
        volume (⋃ z ∈ centers, Metric.ball z r) :=
      (volume_iUnion_balls_eq_card_mul centers r hdisjoint).symm
    _ ≤ volume U := measure_mono hsubset

/-- Quantitative form of finite disk packing using the elementary exponential
lower bound for hyperbolic ball area. -/
theorem card_mul_ofReal_exp_div_sixteen_le_volume_of_iUnion_subset
    (centers : Finset ℍ) {r : ℝ} {U : Set ℍ}
    (hr : Real.log 2 ≤ r)
    (hdisjoint : Set.PairwiseDisjoint (centers : Set ℍ)
      fun z ↦ Metric.ball z r)
    (hsubset : (⋃ z ∈ centers, Metric.ball z r) ⊆ U) :
    (centers.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp r / 16) ≤ volume U := by
  calc
    (centers.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp r / 16) ≤
        (centers.card : ℝ≥0∞) *
          volume (Metric.ball (UpperHalfPlane.I : ℍ) r) :=
      by
        simpa [mul_comm] using
          mul_le_mul_left (ofReal_exp_div_sixteen_le_volume_ball _ hr)
            (centers.card : ℝ≥0∞)
    _ ≤ volume U :=
      card_mul_volume_ball_le_volume_of_iUnion_subset centers r hdisjoint hsubset

/-- Centers separated by at least twice the radius determine pairwise
disjoint open balls. -/
theorem pairwiseDisjoint_balls_of_two_mul_le_dist
    (centers : Finset ℍ) {r : ℝ}
    (hseparated : ∀ {z}, z ∈ centers → ∀ {w}, w ∈ centers →
      z ≠ w → 2 * r ≤ dist z w) :
    Set.PairwiseDisjoint (centers : Set ℍ) fun z ↦ Metric.ball z r := by
  intro z hz w hw hzw
  apply Metric.ball_disjoint_ball
  simpa [two_mul] using hseparated hz hw hzw

/-- If all centers lie in one ball, enlarging its radius by the packing radius
contains every packed ball. -/
theorem iUnion_balls_subset_ball_add (centers : Finset ℍ)
    {o : ℍ} {R r : ℝ} (hcenters : ∀ z ∈ centers, z ∈ Metric.ball o R) :
    (⋃ z ∈ centers, Metric.ball z r) ⊆ Metric.ball o (R + r) := by
  refine iUnion₂_subset fun z hz ↦ Metric.ball_subset_ball' ?_
  have hz' := Metric.mem_ball.mp (hcenters z hz)
  linarith

/-- Local packing bound for a separated finite set of centers in a ball. -/
theorem card_mul_ofReal_exp_div_sixteen_le_volume_ball_add
    (centers : Finset ℍ) {o : ℍ} {R r : ℝ}
    (hr : Real.log 2 ≤ r)
    (hseparated : ∀ {z}, z ∈ centers → ∀ {w}, w ∈ centers →
      z ≠ w → 2 * r ≤ dist z w)
    (hcenters : ∀ z ∈ centers, z ∈ Metric.ball o R) :
    (centers.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp r / 16) ≤
      volume (Metric.ball o (R + r)) := by
  exact card_mul_ofReal_exp_div_sixteen_le_volume_of_iUnion_subset centers hr
    (pairwiseDisjoint_balls_of_two_mul_le_dist centers hseparated)
    (iUnion_balls_subset_ball_add centers hcenters)

/-- Real-valued local packing bound. -/
theorem card_mul_exp_div_sixteen_le_volume_real_ball_add
    (centers : Finset ℍ) {o : ℍ} {R r : ℝ}
    (hr : Real.log 2 ≤ r)
    (hseparated : ∀ {z}, z ∈ centers → ∀ {w}, w ∈ centers →
      z ≠ w → 2 * r ≤ dist z w)
    (hcenters : ∀ z ∈ centers, z ∈ Metric.ball o R) :
    (centers.card : ℝ) * Real.exp r / 16 ≤
      volume.real (Metric.ball o (R + r)) := by
  have h := card_mul_ofReal_exp_div_sixteen_le_volume_ball_add centers hr
    hseparated hcenters
  have h' := ENNReal.toReal_mono (measure_ball_ne_top (x := o) (r := R + r)) h
  have hnonneg : 0 ≤ Real.exp r / 16 :=
    div_nonneg (Real.exp_pos r).le (by norm_num)
  have h'' : (centers.card : ℝ) * (Real.exp r / 16) ≤
      volume.real (Metric.ball o (R + r)) := by
    simpa [Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hnonneg] using h'
  calc
    (centers.card : ℝ) * Real.exp r / 16 =
        (centers.card : ℝ) * (Real.exp r / 16) := by ring
    _ ≤ volume.real (Metric.ball o (R + r)) := h''

/-- An explicit upper bound for the size of a separated finite set in a
hyperbolic ball. -/
theorem card_le_sixteen_mul_exp_neg_mul_volume_real_ball_add
    (centers : Finset ℍ) {o : ℍ} {R r : ℝ}
    (hr : Real.log 2 ≤ r)
    (hseparated : ∀ {z}, z ∈ centers → ∀ {w}, w ∈ centers →
      z ≠ w → 2 * r ≤ dist z w)
    (hcenters : ∀ z ∈ centers, z ∈ Metric.ball o R) :
    (centers.card : ℝ) ≤
      16 * Real.exp (-r) * volume.real (Metric.ball o (R + r)) := by
  have harea := card_mul_exp_div_sixteen_le_volume_real_ball_add centers hr
    hseparated hcenters
  have hexp : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    (centers.card : ℝ) =
        16 * Real.exp (-r) * ((centers.card : ℝ) * Real.exp r / 16) := by
      symm
      calc
        16 * Real.exp (-r) * ((centers.card : ℝ) * Real.exp r / 16) =
            (centers.card : ℝ) * (Real.exp (-r) * Real.exp r) := by ring
        _ = centers.card := by rw [hexp]; ring
    _ ≤ 16 * Real.exp (-r) * volume.real (Metric.ball o (R + r)) :=
      mul_le_mul_of_nonneg_left harea (by positivity)

/-- A ball contained in a finite-volume region has logarithmically bounded
radius.  This is the abstract diameter/packing implication, independent of
any formula for the region's total area. -/
theorem radius_le_log_sixteen_mul_volume_real_of_ball_subset
    {U : Set ℍ} (hU : volume U ≠ ∞) (z : ℍ) {r : ℝ}
    (hr : Real.log 2 ≤ r) (hsubset : Metric.ball z r ⊆ U) :
    r ≤ Real.log (16 * volume.real U) := by
  apply radius_le_log_sixteen_mul_of_volume_real_ball_le z hr
  exact measureReal_mono hsubset hU

/-- Distinct elements of the deck group move a ball of radius less than half
the systole to pairwise-disjoint translates. -/
theorem pairwiseDisjoint_deck_smul_ball {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) {r : ℝ}
    (hr : 2 * r < X.systole) (elements : Finset X.deckGroup) :
    Set.PairwiseDisjoint (elements : Set X.deckGroup)
      fun γ ↦ γ • Metric.ball o r := by
  intro γ _hγ δ _hδ hγδ
  have hne : δ⁻¹ * γ ≠ 1 := by
    intro h
    apply hγδ
    calc
      γ = δ * (δ⁻¹ * γ) := by simp
      _ = δ := by rw [h]; simp
  have hdisjoint := disjoint_smul_ball X o r hr (δ⁻¹ * γ) hne
  have htranslated :
      Disjoint (δ • ((δ⁻¹ * γ) • Metric.ball o r))
        (δ • Metric.ball o r) :=
    disjoint_smul_set.mpr hdisjoint
  simpa [smul_smul] using htranslated

/-! ## Comparison with a fundamental Dirichlet region -/

 /-- A ball whose radius is at most half the systole has no overlap between
 distinct deck translates, so its hyperbolic area is bounded by the area of a
 Dirichlet fundamental domain. -/
 theorem volume_ball_le_dirichletDomain {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) {r : ℝ}
    (hr : 2 * r ≤ X.systole) :
    volume (Metric.ball o r) ≤
    volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  let D := Vendored.RiemannDynamics.dirichletDomain X.deckGroup o
  have hFD := X.dirichletDomain_isFundamentalDomain o
  apply hFD.measure_le_of_pairwise_disjoint Metric.isOpen_ball.nullMeasurableSet
  intro γ₁ γ₂ hγ
  have hne : γ₂⁻¹ * γ₁ ≠ 1 := by
    intro h
    apply hγ
    calc
      γ₁ = γ₂ * (γ₂⁻¹ * γ₁) := by simp
      _ = γ₂ := by rw [h]; simp
  have hdisjoint := disjoint_smul_ball_of_two_mul_le X o r hr (γ₂⁻¹ * γ₁) hne
  have htranslated :
      Disjoint (γ₂ • ((γ₂⁻¹ * γ₁) • Metric.ball o r))
        (γ₂ • Metric.ball o r) :=
    disjoint_smul_set.mpr hdisjoint
  have hballs :
      Disjoint (γ₁ • Metric.ball o r) (γ₂ • Metric.ball o r) := by
    simpa [smul_smul] using htranslated
  exact (hballs.mono inter_subset_left inter_subset_left).aedisjoint

/-- Exact measure of a finite union of deck translates of an embedded ball. -/
theorem volume_iUnion_deck_smul_ball_eq_card_mul {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) {r : ℝ}
    (hr : 2 * r < X.systole) (elements : Finset X.deckGroup) :
    volume (⋃ γ ∈ elements, γ • Metric.ball o r) =
      (elements.card : ℝ≥0∞) * volume (Metric.ball o r) := by
  rw [measure_biUnion_finset
    (pairwiseDisjoint_deck_smul_ball X o hr elements)]
  · calc
      ∑ γ ∈ elements, volume (γ • Metric.ball o r) =
          ∑ _γ ∈ elements, volume (Metric.ball o r) := by
        apply Finset.sum_congr rfl
        intro γ _hγ
        exact measure_smul volume γ (Metric.ball o r)
      _ = (elements.card : ℝ≥0∞) * volume (Metric.ball o r) := by simp
  · intro γ _hγ
    rw [Metric.smul_ball]
    exact measurableSet_ball

/-- Every finite family of distinct deck translates contains the expected
amount of hyperbolic area at the elementary exponential scale. -/
theorem card_mul_ofReal_exp_div_sixteen_le_volume_iUnion_deck_smul_ball
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {r : ℝ}
    (hradius : Real.log 2 ≤ r) (hsys : 2 * r < X.systole)
    (elements : Finset X.deckGroup) :
    (elements.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp r / 16) ≤
      volume (⋃ γ ∈ elements, γ • Metric.ball o r) := by
  rw [volume_iUnion_deck_smul_ball_eq_card_mul X o hsys elements]
  simpa [mul_comm] using
    mul_le_mul_left (ofReal_exp_div_sixteen_le_volume_ball o hradius)
      (elements.card : ℝ≥0∞)

/-- Proper discontinuity makes the set of deck transformations moving a
basepoint into a fixed closed ball finite. -/
theorem finite_deckElements_dist_le {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) :
    Set.Finite {γ : X.deckGroup | dist o (γ • o) ≤ R} := by
  apply (finite_disjoint_inter_image (Γ := X.deckGroup) (K := ({o} : Set ℍ))
    (L := Metric.closedBall o R) isCompact_singleton
      (isCompact_closedBall o R)).subset
  intro γ hγ
  refine ⟨γ • o, ⟨?_, Metric.mem_closedBall.mpr ?_⟩⟩
  · exact ⟨o, Set.mem_singleton o, rfl⟩
  · simpa [dist_comm] using hγ

/-- The finite set of deck transformations whose displacement of `o` is at
most `R`. -/
noncomputable def deckElementsDistLE {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) : Finset X.deckGroup :=
  (finite_deckElements_dist_le X o R).toFinset

@[simp]
theorem mem_deckElementsDistLE {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ)
    (γ : X.deckGroup) :
    γ ∈ deckElementsDistLE X o R ↔ dist o (γ • o) ≤ R := by
  simp [deckElementsDistLE]

/-- The union of radius-`r` balls translated by deck transformations of
displacement at most `R` lies in the ball of radius `R + r`. -/
theorem iUnion_deckElementsDistLE_smul_ball_subset {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R r : ℝ) :
    (⋃ γ ∈ deckElementsDistLE X o R, γ • Metric.ball o r) ⊆
      Metric.ball o (R + r) := by
  refine iUnion₂_subset fun γ hγ ↦ ?_
  rw [Metric.smul_ball]
  apply Metric.ball_subset_ball'
  have hdist : dist o (γ • o) ≤ R :=
    (mem_deckElementsDistLE X o R γ).mp hγ
  rw [dist_comm] at hdist
  linarith

/-- Quantitative orbit-counting bound obtained solely from proper
discontinuity, systolic separation, and the elementary ball-area estimate. -/
theorem card_deckElementsDistLE_mul_ofReal_exp_div_sixteen_le_volume_ball
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {R r : ℝ}
    (hradius : Real.log 2 ≤ r) (hsys : 2 * r < X.systole) :
    (deckElementsDistLE X o R).card * ENNReal.ofReal (Real.exp r / 16) ≤
      volume (Metric.ball o (R + r)) := by
  calc
    (deckElementsDistLE X o R).card * ENNReal.ofReal (Real.exp r / 16) ≤
        volume (⋃ γ ∈ deckElementsDistLE X o R,
          γ • Metric.ball o r) :=
      card_mul_ofReal_exp_div_sixteen_le_volume_iUnion_deck_smul_ball
        X o hradius hsys (deckElementsDistLE X o R)
    _ ≤ volume (Metric.ball o (R + r)) :=
      measure_mono (iUnion_deckElementsDistLE_smul_ball_subset X o R r)

/-- Real-valued upper bound on the number of deck transformations moving a
basepoint by at most `R`. -/
theorem card_deckElementsDistLE_le_sixteen_mul_exp_neg_mul_volume_real_ball
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {R r : ℝ}
    (hradius : Real.log 2 ≤ r) (hsys : 2 * r < X.systole) :
    ((deckElementsDistLE X o R).card : ℝ) ≤
      16 * Real.exp (-r) * volume.real (Metric.ball o (R + r)) := by
  have h := card_deckElementsDistLE_mul_ofReal_exp_div_sixteen_le_volume_ball
    (R := R) X o hradius hsys
  have h' := ENNReal.toReal_mono (measure_ball_ne_top (x := o) (r := R + r)) h
  have hnonneg : 0 ≤ Real.exp r / 16 :=
    div_nonneg (Real.exp_pos r).le (by norm_num)
  have harea : ((deckElementsDistLE X o R).card : ℝ) * Real.exp r / 16 ≤
      volume.real (Metric.ball o (R + r)) := by
    calc
      ((deckElementsDistLE X o R).card : ℝ) * Real.exp r / 16 =
          ((deckElementsDistLE X o R).card : ℝ) * (Real.exp r / 16) := by ring
      _ ≤ volume.real (Metric.ball o (R + r)) := by
        simpa [Measure.real, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal hnonneg] using h'
  have hexp : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    ((deckElementsDistLE X o R).card : ℝ) =
        16 * Real.exp (-r) *
          (((deckElementsDistLE X o R).card : ℝ) * Real.exp r / 16) := by
      symm
      calc
        16 * Real.exp (-r) *
              (((deckElementsDistLE X o R).card : ℝ) * Real.exp r / 16) =
            ((deckElementsDistLE X o R).card : ℝ) *
              (Real.exp (-r) * Real.exp r) := by ring
        _ = (deckElementsDistLE X o R).card := by rw [hexp]; ring
    _ ≤ 16 * Real.exp (-r) * volume.real (Metric.ball o (R + r)) :=
      mul_le_mul_of_nonneg_left harea (by positivity)

/-- An area upper bound for the ball of radius half the systole gives an
explicit logarithmic systole bound.  The `2 * log 2` branch handles surfaces
whose half-systole is too small for the exponential ball estimate. -/
theorem systole_le_max_log_of_half_systole_ball_area_le
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) {A : ℝ}
    (harea : volume.real (Metric.ball o (X.systole / 2)) ≤ A) :
    X.systole ≤
      max (2 * Real.log 2) (2 * Real.log (16 * A)) := by
  by_cases hradius : Real.log 2 ≤ X.systole / 2
  · have hlog : X.systole / 2 ≤ Real.log (16 * A) :=
      radius_le_log_sixteen_mul_of_volume_real_ball_le o hradius harea
    calc
      X.systole = 2 * (X.systole / 2) := by ring
      _ ≤ 2 * Real.log (16 * A) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ ≤ max (2 * Real.log 2) (2 * Real.log (16 * A)) :=
        le_max_right _ _
  · have hsmall : X.systole / 2 < Real.log 2 := lt_of_not_ge hradius
    calc
      X.systole = 2 * (X.systole / 2) := by ring
      _ ≤ 2 * Real.log 2 :=
        (mul_lt_mul_of_pos_left hsmall (by norm_num)).le
      _ ≤ max (2 * Real.log 2) (2 * Real.log (16 * A)) :=
        le_max_left _ _

 /-- The Dirichlet-domain comparison gives the explicit logarithmic systole
 upper bound used by the geometric input. -/
theorem systole_le_max_log_of_dirichletDomain_volume {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    X.systole ≤
      max (2 * Real.log 2)
        (2 * Real.log (16 *
          volume.real (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o))) := by
  obtain ⟨K, hK, _hKfinite, hcover⟩ :=
    X.exists_compact_covering_finite_volume
  have hDcompact :=
    X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  have hDfinite :
      volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≠ ∞ :=
    hDcompact.measure_lt_top.ne
  apply systole_le_max_log_of_half_systole_ball_area_le X o
  have hvol := volume_ball_le_dirichletDomain X o
    (r := X.systole / 2) (by ring_nf; exact le_rfl)
  have hreal := ENNReal.toReal_mono
    hDfinite hvol
  simpa [Measure.real] using hreal

 /-- Final scalar interface for the missing quotient-area comparison: any
 explicit upper bound on the Dirichlet volume immediately yields the
 corresponding systole bound. -/
theorem systole_le_max_log_of_dirichlet_volume_le {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) {A : ℝ}
    (hA : volume.real
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≤ A) :
    X.systole ≤ max (2 * Real.log 2) (2 * Real.log (16 * A)) := by
  obtain ⟨K, hK, _hKfinite, hcover⟩ :=
    X.exists_compact_covering_finite_volume
  have hDcompact :=
    X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  have hDfinite :
      volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≠ ∞ :=
    hDcompact.measure_lt_top.ne
  apply systole_le_max_log_of_half_systole_ball_area_le X o
  have hvol := volume_ball_le_dirichletDomain X o
    (r := X.systole / 2) (by ring_nf; exact le_rfl)
  have hreal := ENNReal.toReal_mono hDfinite hvol
  exact hreal.trans hA

/-! ## Finite polygonal area interfaces

The quotient-area theorem is most naturally supplied by a finite geodesic
triangulation of a fundamental polygon.  The following two lemmas isolate the
measure-theoretic and triangle-area parts of that argument without postulating
either a quotient measure or a genus-area formula.
-/

/-- Every nondegenerate hyperbolic triangle has area at most `π`. -/
theorem volume_hyperbolicTriangle_le_pi
    (v₁ v₂ v₃ : ℍ) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    volume (Vendored.RiemannDynamics.hyperbolicTriangle v₁ v₂ v₃) ≤
      ENNReal.ofReal Real.pi := by
  rw [Vendored.RiemannDynamics.volume_hyperbolicTriangle v₁ v₂ v₃ h₁₂ h₁₃ h₂₃]
  apply ENNReal.ofReal_le_ofReal
  linarith [Vendored.RiemannDynamics.sectorAngle_nonneg v₁ v₂ v₃,
    Vendored.RiemannDynamics.sectorAngle_nonneg v₂ v₁ v₃,
    Vendored.RiemannDynamics.sectorAngle_nonneg v₃ v₁ v₂]

/-- A finite cover by at most `N` pieces, each of area at most `π`, gives the
corresponding elementary area bound.  A later polygonal decomposition can
instantiate this interface with geodesic triangles. -/
theorem volume_le_fin_mul_pi_of_finite_cover {N : ℕ}
    (D : Set ℍ) (pieces : Fin N → Set ℍ)
    (hsub : D ⊆ ⋃ i, pieces i)
    (hpieces : ∀ i, volume (pieces i) ≤ ENNReal.ofReal Real.pi) :
    volume D ≤ N * ENNReal.ofReal Real.pi := by
  calc
    volume D ≤ volume (⋃ i, pieces i) := measure_mono hsub
    _ ≤ ∑' i, volume (pieces i) := measure_iUnion_le pieces
    _ ≤ ∑' _i : Fin N, ENNReal.ofReal Real.pi := by
      exact ENNReal.tsum_le_tsum (fun i ↦ hpieces i)
    _ = N * ENNReal.ofReal Real.pi := by
      simp

/-- A finite cover of the canonical Dirichlet region by `N` pieces of area at
most `π` gives a concrete real-valued covolume bound. -/
theorem dirichletDomain_volume_real_le_fin_mul_pi
    {g N : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (pieces : Fin N → Set ℍ)
    (hsub : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
      ⋃ i, pieces i)
    (hpieces : ∀ i, volume (pieces i) ≤ ENNReal.ofReal Real.pi) :
    volume.real (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≤
      (N : ℝ) * Real.pi := by
  have hvol := volume_le_fin_mul_pi_of_finite_cover
    (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) pieces hsub hpieces
  have hfinite : (N : ℝ≥0∞) * ENNReal.ofReal Real.pi ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite hvol
  change (volume
    (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)).toReal ≤ _
  simpa [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal Real.pi_nonneg] using hreal

/-- The finite triangle-cover interface now feeds directly into the explicit
Dirichlet-domain systole estimate. -/
theorem systole_le_dirichlet_log_bound_of_fin_triangle_cover
    {g N : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    (pieces : Fin N → Set ℍ)
    (hsub : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
      ⋃ i, pieces i)
    (hpieces : ∀ i, volume (pieces i) ≤ ENNReal.ofReal Real.pi) :
    X.systole ≤ max (2 * Real.log 2)
      (2 * Real.log (16 * ((N : ℝ) * Real.pi))) := by
  apply systole_le_max_log_of_dirichlet_volume_le X o
  exact dirichletDomain_volume_real_le_fin_mul_pi X o pieces hsub hpieces

end SystolicGrowth
