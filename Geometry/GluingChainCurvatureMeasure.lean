module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.QuotientAreaMeasure
public import Geometry.GluingSeamHomotopy
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

@[expose] public section

/-!
# Actual area and seam measures on the retained chain

The component measure is the original quotient hyperbolic area restricted
to the literal retained subtype, then pushed through the native quotient
inclusion. Seam length is the pushforward of `sinh r` times angular Lebesgue
measure on one positive turn of the actual outgoing polar circle.

Their negative area-minus-seam combination is a genuinely finite signed
measure on the original carrier. Identifying this candidate with intrinsic
bounded integral curvature still requires the local chart identification;
no chart independence or intrinsic curvature assertion is built into these
definitions.
-/

open MeasureTheory Set UpperHalfPlane
open scoped ENNReal UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

local instance : MeasurableSpace Circle := borel Circle

local instance : BorelSpace Circle := ⟨rfl⟩

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance componentCarrier_opensMeasurableSpace (i : Fin n) :
    OpensMeasurableSpace (X i).Carrier where
  borel_le := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    change IsOpen s at hs
    exact measurableSet_quotient.mpr (hs.preimage continuous_quotient_mk').measurableSet

/-- Literal inclusion of an original retained component into the chain quotient. -/
def componentInclude (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.ChainComponent i → P.GluedCarrier :=
  fun x => P.gluedMk ⟨i, x⟩

theorem componentInclude_measurable
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Measurable (P.componentInclude i) := by
  apply measurable_quotient_mk''.comp
  exact Measurable.of_le_map (iInf_le _ i)

theorem componentInclude_continuous
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Continuous (P.componentInclude i) :=
  P.gluedMk_continuous.comp continuous_sigmaMk

/-- Every open native set is measurable for the unchanged quotient sigma algebra. -/
theorem gluedCarrier_isOpen_measurable
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.GluedCarrier}
    (hs : IsOpen s) : MeasurableSet s := by
  apply measurableSet_quotient.mpr
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  change MeasurableSet ((P.componentInclude i) ⁻¹' s)
  exact (hs.preimage (P.componentInclude_continuous i)).measurableSet

/-- The exact retained set is measurable for the original quotient sigma algebra. -/
theorem componentRetainedSet_measurable
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    MeasurableSet ((X i).puncturedComponentSet
      (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) := by
  unfold ClosedHyperbolicSurface.puncturedComponentSet
    ClosedHyperbolicSurface.punctureDeletedSet
  apply MeasurableSet.compl
  apply MeasurableSet.union
  · split_ifs
    · exact (X i).measurableSet_orbitBall _ _
    · exact MeasurableSet.empty
  · split_ifs
    · exact (X i).measurableSet_orbitBall _ _
    · exact MeasurableSet.empty

/-- Actual quotient hyperbolic area restricted to the prescribed retained piece. -/
def retainedComponentAreaMeasure
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Measure (P.ChainComponent i) :=
  ((X i).quotientAreaMeasure (P.centers i).1).comap Subtype.val

instance retainedComponentAreaMeasure_isFinite
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsFiniteMeasure (P.retainedComponentAreaMeasure i) := by
  letI : IsFiniteMeasure ((X i).quotientAreaMeasure (P.centers i).1) :=
    ⟨lt_top_iff_ne_top.mpr ((X i).quotientAreaMeasure_univ_ne_top _)⟩
  unfold retainedComponentAreaMeasure
  infer_instance

/-- The retained area is literally restriction, not supplied measure data. -/
theorem retainedComponentAreaMeasure_map_subtype
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.retainedComponentAreaMeasure i).map Subtype.val =
      ((X i).quotientAreaMeasure (P.centers i).1).restrict
        ((X i).puncturedComponentSet
          (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) :=
  map_comap_subtype_coe (P.componentRetainedSet_measurable i) _

/-- The actual retained area has its unchanged subset mass. -/
theorem retainedComponentAreaMeasure_univ
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.retainedComponentAreaMeasure i univ =
      (X i).quotientAreaMeasure (P.centers i).1
        ((X i).puncturedComponentSet
          (P.centers i).1 (P.centers i).2 (gluingRadius C g) i) := by
  rw [retainedComponentAreaMeasure,
    comap_subtype_coe_apply (P.componentRetainedSet_measurable i)]
  simp

/-- Area from one original retained component on the native chain carrier. -/
def gluedComponentAreaMeasure
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Measure P.GluedCarrier :=
  (P.retainedComponentAreaMeasure i).map (P.componentInclude i)

instance gluedComponentAreaMeasure_isFinite
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsFiniteMeasure (P.gluedComponentAreaMeasure i) := by
  unfold gluedComponentAreaMeasure
  infer_instance

theorem gluedComponentAreaMeasure_univ_le_covolume
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.gluedComponentAreaMeasure i univ ≤ covolume (X i).deckGroup ℍ volume := by
  rw [gluedComponentAreaMeasure, Measure.map_apply (P.componentInclude_measurable i)
    MeasurableSet.univ, preimage_univ, P.retainedComponentAreaMeasure_univ i,
    ← (X i).quotientAreaMeasure_univ_eq_covolume (P.centers i).1]
  exact measure_mono (subset_univ _)

/-- The finite sum of the original retained component areas on the original quotient. -/
def gluedChainAreaMeasure (P : ExerciseGluingPreparation C g n genera X) :
    Measure P.GluedCarrier :=
  ∑ i : Fin n, P.gluedComponentAreaMeasure i

instance gluedChainAreaMeasure_isFinite
    (P : ExerciseGluingPreparation C g n genera X) :
    IsFiniteMeasure P.gluedChainAreaMeasure := by
  unfold gluedChainAreaMeasure
  infer_instance

theorem gluedChainAreaMeasure_univ_le_sum_covolumes
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainAreaMeasure univ ≤ ∑ i : Fin n, covolume (X i).deckGroup ℍ volume := by
  simp only [gluedChainAreaMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_le_sum fun i _ => P.gluedComponentAreaMeasure_univ_le_covolume i

/-- The actual outgoing native polar circle, before choosing one angular turn. -/
def gluedChainSeamCircleMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Circle → P.GluedCarrier := fun θ =>
  P.componentInclude (gluingChainEdgeLeft k)
    (P.rightCirclePoint (gluingChainEdgeLeft k)
      ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 θ (gluingRadius C g), by
        rw [Metric.mem_sphere, dist_comm, dist_gluingPolarPoint _ θ P.radius_pos.le]⟩)

/-- This is the already constructed native seam-circle inclusion, literally. -/
theorem gluedChainSeamCircleMap_eq_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    P.gluedChainSeamCircleMap k θ = (P.gluedSeamCircleInclusion k θ).1 := by
  rw [P.gluedSeamCircleInclusion_eq_outgoing k θ]
  rfl

theorem gluedChainSeamCircleMap_measurable
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Measurable (P.gluedChainSeamCircleMap k) := by
  apply (P.componentInclude_measurable (gluingChainEdgeLeft k)).comp
  apply Measurable.subtype_mk
  apply measurable_quotient_mk''.comp
  exact ((gluingPolarPoint_continuous (P.centers (gluingChainEdgeLeft k)).2).comp
    (continuous_id.prodMk continuous_const)).measurable

/-- One genuine positive angular turn of the original outgoing seam. -/
def gluedChainSeamAngularMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ℝ → P.GluedCarrier :=
  P.gluedChainSeamCircleMap k ∘ Circle.exp

theorem gluedChainSeamAngularMap_measurable
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Measurable (P.gluedChainSeamAngularMap k) :=
  (P.gluedChainSeamCircleMap_measurable k).comp Circle.exp.continuous.measurable

/-- Native seam arclength, using the actual `sinh r` angular density. -/
def gluedChainSeamLengthMeasure
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Measure P.GluedCarrier :=
  ENNReal.ofReal (Real.sinh (gluingRadius C g)) •
    (volume.restrict (Ioc 0 (2 * Real.pi))).map (P.gluedChainSeamAngularMap k)

instance gluedChainSeamLengthMeasure_isFinite
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsFiniteMeasure (P.gluedChainSeamLengthMeasure k) := by
  unfold gluedChainSeamLengthMeasure
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

/-- Every seam has its genuine hyperbolic circumference. -/
theorem gluedChainSeamLengthMeasure_univ
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainSeamLengthMeasure k univ =
      ENNReal.ofReal (2 * Real.pi * Real.sinh (gluingRadius C g)) := by
  rw [gluedChainSeamLengthMeasure, Measure.smul_apply,
    Measure.map_apply (P.gluedChainSeamAngularMap_measurable k) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [smul_eq_mul, ← ENNReal.ofReal_mul (Real.sinh_pos_iff.mpr P.radius_pos).le]
  congr 1
  ring

/-- The arclength measure is concentrated on its actual native seam, not an
arbitrary selected circle in the carrier. -/
theorem gluedChainSeamLengthMeasure_compl_seam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainSeamLengthMeasure k (P.gluedSeamCircle k)ᶜ = 0 := by
  have hmeas : MeasurableSet (P.gluedSeamCircle k)ᶜ :=
    P.gluedCarrier_isOpen_measurable (P.gluedSeamCircle_isClosed k).isOpen_compl
  have hpre : P.gluedChainSeamAngularMap k ⁻¹' (P.gluedSeamCircle k)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro θ hθ
    apply hθ
    change P.gluedChainSeamCircleMap k (Circle.exp θ) ∈ P.gluedSeamCircle k
    rw [P.gluedChainSeamCircleMap_eq_inclusion]
    exact P.gluedSeamCircleInclusion_mem k (Circle.exp θ)
  rw [gluedChainSeamLengthMeasure, Measure.smul_apply,
    Measure.map_apply (P.gluedChainSeamAngularMap_measurable k) hmeas, hpre]
  simp

/-- Total arclength of the actual finite collection of native seams. -/
def gluedChainTotalSeamLengthMeasure
    (P : ExerciseGluingPreparation C g n genera X) : Measure P.GluedCarrier :=
  ∑ k : Fin (n - 1), P.gluedChainSeamLengthMeasure k

instance gluedChainTotalSeamLengthMeasure_isFinite
    (P : ExerciseGluingPreparation C g n genera X) :
    IsFiniteMeasure P.gluedChainTotalSeamLengthMeasure := by
  unfold gluedChainTotalSeamLengthMeasure
  infer_instance

theorem gluedChainTotalSeamLengthMeasure_univ
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainTotalSeamLengthMeasure univ =
      (n - 1 : ℕ) * ENNReal.ofReal (2 * Real.pi * Real.sinh (gluingRadius C g)) := by
  simp [gluedChainTotalSeamLengthMeasure, Measure.coe_finsetSum,
    Finset.sum_apply, P.gluedChainSeamLengthMeasure_univ]

/-- Positive magnitude of the native negative-area/negative-seam candidate. -/
def gluedChainCurvatureMagnitude
    (P : ExerciseGluingPreparation C g n genera X) : Measure P.GluedCarrier :=
  P.gluedChainAreaMeasure +
    ENNReal.ofReal (2 * (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))) •
      P.gluedChainTotalSeamLengthMeasure

instance gluedChainCurvatureMagnitude_isFinite
    (P : ExerciseGluingPreparation C g n genera X) :
    IsFiniteMeasure P.gluedChainCurvatureMagnitude := by
  letI := P.gluedChainTotalSeamLengthMeasure.smul_finite
    (c := ENNReal.ofReal
      (2 * (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))))
    ENNReal.ofReal_ne_top
  unfold gluedChainCurvatureMagnitude
  infer_instance

/-- The actual finite seam contribution has total mass `4π cosh r` per edge. -/
theorem gluedChainCurvatureMagnitude_univ
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainCurvatureMagnitude univ = P.gluedChainAreaMeasure univ +
      (n - 1 : ℕ) * ENNReal.ofReal (4 * Real.pi * Real.cosh (gluingRadius C g)) := by
  have hsinh : 0 < Real.sinh (gluingRadius C g) := Real.sinh_pos_iff.mpr P.radius_pos
  have hcoefficient : 0 ≤ 2 *
      (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g)) := by positivity
  rw [gluedChainCurvatureMagnitude, Measure.add_apply, Measure.smul_apply,
    P.gluedChainTotalSeamLengthMeasure_univ, smul_eq_mul, ← mul_assoc,
    mul_comm (ENNReal.ofReal (2 *
      (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))))
      (n - 1 : ℕ), mul_assoc, ← ENNReal.ofReal_mul hcoefficient]
  congr 3
  field_simp
  ring

theorem gluedChainCurvatureMagnitude_univ_le
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainCurvatureMagnitude univ ≤
      (∑ i : Fin n, covolume (X i).deckGroup ℍ volume) +
        (n - 1 : ℕ) * ENNReal.ofReal (4 * Real.pi * Real.cosh (gluingRadius C g)) := by
  rw [P.gluedChainCurvatureMagnitude_univ]
  exact add_le_add P.gluedChainAreaMeasure_univ_le_sum_covolumes le_rfl

/-- The signed native candidate, without an intrinsic-curvature identification premise. -/
def gluedChainNegativeCurvatureMeasure
    (P : ExerciseGluingPreparation C g n genera X) : SignedMeasure P.GluedCarrier :=
  -P.gluedChainCurvatureMagnitude.toSignedMeasure

theorem gluedChainNegativeCurvatureMeasure_nonpositive
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainNegativeCurvatureMeasure ≤ 0 :=
  neg_nonpos.mpr (Measure.zero_le_toSignedMeasure _)

/-- The signed candidate is exactly negative native area minus `2 coth r`
times the actually constructed total native seam arclength. -/
theorem gluedChainNegativeCurvatureMeasure_eq_neg_area_sub_seam_length
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainNegativeCurvatureMeasure = -P.gluedChainAreaMeasure.toSignedMeasure -
      (2 * (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))) •
        P.gluedChainTotalSeamLengthMeasure.toSignedMeasure := by
  have hsinh : 0 < Real.sinh (gluingRadius C g) := Real.sinh_pos_iff.mpr P.radius_pos
  let k : ℝ := 2 * (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let μ := P.gluedChainTotalSeamLengthMeasure
  letI : IsFiniteMeasure (ENNReal.ofReal k • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  have hsmul : (ENNReal.ofReal k • μ).toSignedMeasure = k • μ.toSignedMeasure := by
    change (k.toNNReal • μ).toSignedMeasure = _
    rw [Measure.toSignedMeasure_smul]
    change (k.toNNReal : ℝ) • μ.toSignedMeasure = _
    rw [Real.coe_toNNReal k hk]
  change -(P.gluedChainAreaMeasure + ENNReal.ofReal k • μ).toSignedMeasure = _
  rw [Measure.toSignedMeasure_add, hsmul, neg_add, sub_eq_add_neg]

/-- Total variation is the actually constructed finite area-plus-seam measure. -/
theorem gluedChainNegativeCurvatureMeasure_totalVariation
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainNegativeCurvatureMeasure.totalVariation = P.gluedChainCurvatureMagnitude := by
  let μ := P.gluedChainCurvatureMagnitude
  let j : JordanDecomposition P.GluedCarrier :=
    { posPart := μ
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : j.toSignedMeasure = μ.toSignedMeasure := by
    simp [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero]
  change (-μ.toSignedMeasure).totalVariation = μ
  rw [SignedMeasure.totalVariation_neg, ← hj, SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp [j]

instance gluedChainNegativeCurvatureMeasure_totalVariation_isFinite
    (P : ExerciseGluingPreparation C g n genera X) :
    IsFiniteMeasure P.gluedChainNegativeCurvatureMeasure.totalVariation := by
  rw [P.gluedChainNegativeCurvatureMeasure_totalVariation]
  infer_instance

/-- An explicit finite upper bound for native total curvature variation. -/
theorem gluedChainNegativeCurvatureMeasure_totalVariation_univ_le
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedChainNegativeCurvatureMeasure.totalVariation univ ≤
      (∑ i : Fin n, covolume (X i).deckGroup ℍ volume) +
        (n - 1 : ℕ) * ENNReal.ofReal (4 * Real.pi * Real.cosh (gluingRadius C g)) := by
  rw [P.gluedChainNegativeCurvatureMeasure_totalVariation]
  exact P.gluedChainCurvatureMagnitude_univ_le

/-- On every measurable set the candidate is genuinely negative area and
negative seam mass. The real values are justified by the proved finiteness. -/
theorem gluedChainNegativeCurvatureMeasure_apply
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.GluedCarrier}
    (hs : MeasurableSet s) :
    P.gluedChainNegativeCurvatureMeasure s =
      -(P.gluedChainAreaMeasure.real s) -
        (2 * (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))) *
          P.gluedChainTotalSeamLengthMeasure.real s := by
  rw [P.gluedChainNegativeCurvatureMeasure_eq_neg_area_sub_seam_length,
    sub_apply, neg_apply, smul_apply, Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs, smul_eq_mul]

#print axioms retainedComponentAreaMeasure_map_subtype
#print axioms gluedChainSeamCircleMap_eq_inclusion
#print axioms gluedChainSeamLengthMeasure_univ
#print axioms gluedChainSeamLengthMeasure_compl_seam
#print axioms gluedChainNegativeCurvatureMeasure_eq_neg_area_sub_seam_length
#print axioms gluedChainNegativeCurvatureMeasure_totalVariation
#print axioms gluedChainNegativeCurvatureMeasure_totalVariation_univ_le

end

end SystolicGrowth.ExerciseGluingPreparation
