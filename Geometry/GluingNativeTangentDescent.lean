module

public import Geometry.GluingComponentTangentTransport
public import Geometry.GluingNativeUnitTangentFermi
public import Geometry.GluingNativeUnitTangentCylinder
public import Geometry.GluingChainCollarRetraction

@[expose] public section

/-!
# Actual physical frames in the native unit tangent atlas

The physical unit vector is `z.im * u`. Full genuine deck and Fermi
derivatives, rather than assumed transition phases, identify those vectors
with the original native unit tangent charts.
-/

open UpperHalfPlane Topology
open scoped MatrixGroups UpperHalfPlane ComplexConjugate

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem complex_conj_mk (a b : ℝ) :
    conj (⟨a, b⟩ : ℂ) = (⟨a, -b⟩ : ℂ) := rfl

/-- The actual deck differential acts on physical hyperbolic unit vectors
by the squared genuine SL multiplier, including its true height scale. -/
theorem gluingDeckComplex_fderiv_unit_vector
    (A : SL(2, ℝ)) (z : ℍ) (u : ℂ) :
    fderiv ℝ (gluingDeckComplex A) (z : ℂ) ((z.im : ℂ) * u) =
      ((A • z : ℍ).im : ℂ) * ((halfPlaneSpinCircle A z : ℂ) ^ 2 * u) := by
  rw [(gluingDeckComplex_hasFDerivAt_equiv A z.im_pos).fderiv]
  change gluingDeckComplexDeriv A (z : ℂ) * ((z.im : ℂ) * u) = _
  rw [gluingDeckComplex_im_smul, halfPlaneSpinCircle_coe]
  unfold gluingDeckComplexDeriv halfPlaneSpinMultiplier halfPlaneSpinDenominator
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  have hD := gluingDeckComplex_denom_ne_zero A z.im_pos
  have hN : (‖(A 1 0 : ℂ) * (z : ℂ) + (A 1 1 : ℂ)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hD)
  field_simp [hD, hN]

/-- The actual centered polar denominator, written without an angular lift. -/
def gluingPolarCircleDenominator (r : ℝ) (a : Circle) : ℂ :=
  1 - (Real.tanh (r / 2) : ℂ) * (a : ℂ)

theorem gluingPolarCircleDenominator_exp (r θ : ℝ) :
    gluingPolarCircleDenominator r (Circle.exp θ) =
      gluingPolarSpinDenominator (r, θ) := rfl

theorem gluingPolarCircleDenominator_ne_zero (r : ℝ) (a : Circle) :
    gluingPolarCircleDenominator r a ≠ 0 := by
  rw [← Circle.exp_arg a, gluingPolarCircleDenominator_exp]
  exact gluingPolarSpinDenominator_ne_zero _

def Internal.GluingNativeTangentDescentHelpers.gluingPolarDenominatorCircle (r : ℝ) (a : Circle) : Circle :=
  ⟨(‖gluingPolarCircleDenominator r a‖ : ℂ) / gluingPolarCircleDenominator r a, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr (gluingPolarCircleDenominator_ne_zero r a))⟩

/-- The genuine polar radial direction on the circle. Its expression is
jointly continuous in radius and angle, with no principal-argument branch. -/
def gluingPolarRadialCircle (r : ℝ) (a : Circle) : Circle :=
  Circle.exp (Real.pi / 2) * a * Internal.GluingNativeTangentDescentHelpers.gluingPolarDenominatorCircle r a ^ 2

theorem gluingPolarRadialCircle_exp (r θ : ℝ) :
    gluingPolarRadialCircle r (Circle.exp θ) = gluingPolarSpinCircle (r, θ) ^ 2 := by
  apply Circle.coe_injective
  simp only [gluingPolarRadialCircle, Circle.coe_mul, Circle.coe_pow,
    Circle.coe_exp, Internal.GluingNativeTangentDescentHelpers.gluingPolarDenominatorCircle, gluingPolarCircleDenominator_exp,
    gluingPolarSpinCircle_coe, gluingPolarSpinMultiplier, mul_pow]
  have h : Complex.exp (((θ / 2 + Real.pi / 4 : ℝ) : ℂ) * Complex.I) ^ 2 =
      Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]

theorem continuous_gluingPolarRadialCircle :
    Continuous (fun p : ℝ × Circle => gluingPolarRadialCircle p.1 p.2) := by
  have hT : Continuous (fun p : ℝ × Circle => Real.tanh (p.1 / 2)) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact ((Real.continuous_sinh.comp (continuous_fst.div_const 2)).div
      (Real.continuous_cosh.comp (continuous_fst.div_const 2))
      (fun p => (Real.cosh_pos (p.1 / 2)).ne'))
  have hD : Continuous (fun p : ℝ × Circle => gluingPolarCircleDenominator p.1 p.2) :=
    continuous_const.sub
      ((Complex.continuous_ofReal.comp hT).mul
        (continuous_subtype_val.comp continuous_snd))
  have hU : Continuous (fun p : ℝ × Circle => Internal.GluingNativeTangentDescentHelpers.gluingPolarDenominatorCircle p.1 p.2) :=
    ((Complex.continuous_ofReal.comp hD.norm).div hD
      (fun p => gluingPolarCircleDenominator_ne_zero p.1 p.2)).subtype_mk _
  exact (continuous_const.mul continuous_snd).mul (hU.pow 2)

/-- The physical incoming unit direction determined by a native Fermi
orthonormal direction, in the original seam angle convention. -/
def gluingIncomingPhysicalCircle (r s : ℝ) (a u : Circle) : Circle :=
  gluingPolarRadialCircle (r + s) a⁻¹ * u⁻¹

def gluingOutgoingPhysicalCircle (r s : ℝ) (a u : Circle) : Circle :=
  -gluingPolarRadialCircle (r - s) a * u⁻¹

theorem gluingIncomingPhysicalCircle_exp (r s θ : ℝ) (u : Circle) :
    gluingIncomingPhysicalCircle r s (Circle.exp θ) u =
      gluingFermiIncomingSpinCircle r (s, -θ) ^ 2 * u⁻¹ := by
  rw [gluingIncomingPhysicalCircle, ← Circle.exp_neg, gluingPolarRadialCircle_exp]
  rfl

theorem gluingOutgoingPhysicalCircle_exp (r s θ : ℝ) (u : Circle) :
    gluingOutgoingPhysicalCircle r s (Circle.exp θ) u =
      gluingFermiOutgoingSpinCircle r (s, -θ) ^ 2 * u⁻¹ := by
  rw [gluingOutgoingPhysicalCircle, gluingPolarRadialCircle_exp]
  have hi : Circle.exp (Real.pi / 2) ^ 2 = (-1 : Circle) := by
    apply Circle.coe_injective
    rw [Circle.coe_pow, Circle.coe_exp]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.exp_pi_div_two_mul_I, Complex.I_sq, Circle.coe_neg, Circle.coe_one]
  simp only [gluingFermiOutgoingSpinCircle, neg_neg, mul_pow, hi,
    neg_mul, one_mul]

theorem gluingPhysicalCircle_boundary_clutching (r : ℝ) (a u : Circle) :
    gluingFermiBoundarySpinCircle r a⁻¹ ^ 2 * gluingOutgoingPhysicalCircle r 0 a u =
      gluingIncomingPhysicalCircle r 0 a u := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective a
  rw [gluingIncomingPhysicalCircle_exp, gluingOutgoingPhysicalCircle_exp,
    ← Circle.exp_neg, gluingFermiBoundarySpinCircle_exp]
  simp only [gluingFermiBoundarySpinMultiplier, div_pow, ← mul_assoc, div_mul_cancel]

/-- Incoming physical circle direction in the true native orthonormal gauge.
The inverse records the literal conjugation from corrected Fermi parameters
to the repository's original complex seam chart. -/
def gluingFermiIncomingNativePhase (r : ℝ) (p : ℝ × ℝ) (u : Circle) : Circle :=
  (u / gluingFermiIncomingSpinCircle r p ^ 2)⁻¹

def gluingFermiOutgoingNativePhase (r : ℝ) (p : ℝ × ℝ) (u : Circle) : Circle :=
  (u / gluingFermiOutgoingSpinCircle r p ^ 2)⁻¹

theorem gluingIncomingPhysicalCircle_nativePhase (r s θ : ℝ) (u : Circle) :
    gluingFermiIncomingNativePhase r (s, -θ)
      (gluingIncomingPhysicalCircle r s (Circle.exp θ) u) = u := by
  rw [gluingIncomingPhysicalCircle_exp]
  simp [gluingFermiIncomingNativePhase, mul_comm]

theorem gluingOutgoingPhysicalCircle_nativePhase (r s θ : ℝ) (u : Circle) :
    gluingFermiOutgoingNativePhase r (s, -θ)
      (gluingOutgoingPhysicalCircle r s (Circle.exp θ) u) = u := by
  rw [gluingOutgoingPhysicalCircle_exp]
  simp [gluingFermiOutgoingNativePhase, mul_comm]

theorem continuous_gluingIncomingPhysicalCircle (r : ℝ) :
    Continuous (fun p : (ℝ × Circle) × Circle =>
      gluingIncomingPhysicalCircle r p.1.1 p.1.2 p.2) :=
  ((continuous_gluingPolarRadialCircle.comp
    ((continuous_const.add continuous_fst.fst).prodMk continuous_fst.snd.inv)).mul
      continuous_snd.inv)

theorem continuous_gluingOutgoingPhysicalCircle (r : ℝ) :
    Continuous (fun p : (ℝ × Circle) × Circle =>
      gluingOutgoingPhysicalCircle r p.1.1 p.1.2 p.2) :=
  ((continuous_gluingPolarRadialCircle.comp
    ((continuous_const.sub continuous_fst.fst).prodMk continuous_fst.snd)).neg.mul
      continuous_snd.inv)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Actual retained component frames over the genuine incoming collar. -/
abbrev IncomingTangentCollar (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  {q : P.TangentChainComponent i // P.tangentChainComponentBase i q ∈ P.incomingCollar i}

abbrev OutgoingTangentCollar (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  {q : P.TangentChainComponent i // P.tangentChainComponentBase i q ∈ P.outgoingCollar i}

def incomingTangentCollarParam (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (p : ↥(Metric.ball (P.centers i).1 (gluingEmbeddedRadius C g) \
      Metric.ball (P.centers i).1 (gluingRadius C g)) × Circle) :
    P.IncomingTangentCollar i :=
  ⟨⟨Quotient.mk _ (⟨p.1.1, p.2⟩ : HalfPlaneTangentFrame),
    (P.incomingCollarPoint i p.1).2⟩, p.1.1, p.1.2, rfl⟩

def outgoingTangentCollarParam (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (p : ↥(Metric.ball (P.centers i).2 (gluingEmbeddedRadius C g) \
      Metric.ball (P.centers i).2 (gluingRadius C g)) × Circle) :
    P.OutgoingTangentCollar i :=
  ⟨⟨Quotient.mk _ (⟨p.1.1, p.2⟩ : HalfPlaneTangentFrame),
    (P.outgoingCollarPoint i p.1).2⟩, p.1.1, p.1.2, rfl⟩

theorem incomingTangentCollarParam_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsEmbedding (P.incomingTangentCollarParam i) := by
  have h := ((X i).tangentBallHomeomorph (P.centers i).1
    (P.twice_outer_lt_systole i)).isEmbedding.comp
      ((Topology.IsEmbedding.inclusion (Set.sdiff_subset (t :=
        Metric.ball (P.centers i).1 (gluingRadius C g)))).prodMap
        Topology.IsEmbedding.id)
  have hv := Topology.IsEmbedding.subtypeVal.comp h
  apply (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp
  apply (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp
  exact hv

theorem outgoingTangentCollarParam_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsEmbedding (P.outgoingTangentCollarParam i) := by
  have h := ((X i).tangentBallHomeomorph (P.centers i).2
    (P.twice_outer_lt_systole i)).isEmbedding.comp
      ((Topology.IsEmbedding.inclusion (Set.sdiff_subset (t :=
        Metric.ball (P.centers i).2 (gluingRadius C g)))).prodMap
        Topology.IsEmbedding.id)
  have hv := Topology.IsEmbedding.subtypeVal.comp h
  apply (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp
  apply (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp
  exact hv

theorem incomingTangentCollarParam_surjective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Surjective (P.incomingTangentCollarParam i) := by
  intro q
  obtain ⟨z, hz, hzq⟩ := q.2
  let t : (X i).TangentBallCarrier (P.centers i).1 (gluingEmbeddedRadius C g) :=
    ⟨q.1.1, z, hz.1, hzq⟩
  obtain ⟨p, hp⟩ := (X i).tangentBallParam_surjective _ _ t
  have hbase := congrArg (fun v => (X i).tangentFrameBase v.1) hp
  have hpz : p.1.1 = z := quotientMk_injOn_ball (X i) (P.centers i).1
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i) p.1.2 hz.1
      (hbase.trans hzq.symm)
  refine ⟨(⟨z, hz⟩, p.2), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg Subtype.val hp
  change Quotient.mk _ (⟨p.1.1, p.2⟩ : HalfPlaneTangentFrame) = q.1.1 at he
  change Quotient.mk _ (⟨z, p.2⟩ : HalfPlaneTangentFrame) = q.1.1
  simpa only [hpz] using he

theorem outgoingTangentCollarParam_surjective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Surjective (P.outgoingTangentCollarParam i) := by
  intro q
  obtain ⟨z, hz, hzq⟩ := q.2
  let t : (X i).TangentBallCarrier (P.centers i).2 (gluingEmbeddedRadius C g) :=
    ⟨q.1.1, z, hz.1, hzq⟩
  obtain ⟨p, hp⟩ := (X i).tangentBallParam_surjective _ _ t
  have hbase := congrArg (fun v => (X i).tangentFrameBase v.1) hp
  have hpz : p.1.1 = z := quotientMk_injOn_ball (X i) (P.centers i).2
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i) p.1.2 hz.1
      (hbase.trans hzq.symm)
  refine ⟨(⟨z, hz⟩, p.2), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg Subtype.val hp
  change Quotient.mk _ (⟨p.1.1, p.2⟩ : HalfPlaneTangentFrame) = q.1.1 at he
  change Quotient.mk _ (⟨z, p.2⟩ : HalfPlaneTangentFrame) = q.1.1
  simpa only [hpz] using he

/-- Genuine full-frame collar sheets, including the inner boundary. -/
def incomingTangentCollarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (↥(Metric.ball (P.centers i).1 (gluingEmbeddedRadius C g) \
      Metric.ball (P.centers i).1 (gluingRadius C g)) × Circle) ≃ₜ
        P.IncomingTangentCollar i :=
  ((P.incomingTangentCollarParam_isEmbedding i).toHomeomorph.trans
    (Homeomorph.setCongr (Set.range_eq_univ.mpr (P.incomingTangentCollarParam_surjective i)))).trans
      (Homeomorph.Set.univ _)

def outgoingTangentCollarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (↥(Metric.ball (P.centers i).2 (gluingEmbeddedRadius C g) \
      Metric.ball (P.centers i).2 (gluingRadius C g)) × Circle) ≃ₜ
        P.OutgoingTangentCollar i :=
  ((P.outgoingTangentCollarParam_isEmbedding i).toHomeomorph.trans
    (Homeomorph.setCongr (Set.range_eq_univ.mpr (P.outgoingTangentCollarParam_surjective i)))).trans
      (Homeomorph.Set.univ _)

/-- Actual incoming polar points with their literal physical unit phases. -/
def incomingTangentCollarPolarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ((Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) × Circle) ≃ₜ
      P.IncomingTangentCollar i :=
  (((gluingHalfAnnulusPolarHomeomorph (P.centers i).1 _ _ P.radius_pos).symm).prodCongr
    (Homeomorph.refl Circle)).trans (P.incomingTangentCollarHomeomorph i)

def outgoingTangentCollarPolarHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ((Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) × Circle) ≃ₜ
      P.OutgoingTangentCollar i :=
  (((gluingHalfAnnulusPolarHomeomorph (P.centers i).2 _ _ P.radius_pos).symm).prodCongr
    (Homeomorph.refl Circle)).trans (P.outgoingTangentCollarHomeomorph i)

@[simp] theorem incomingTangentCollarPolarHomeomorph_frame
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (p : (Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) × Circle) :
    (P.incomingTangentCollarPolarHomeomorph i p).1.1 =
      Quotient.mk _ (⟨gluingPolarPoint (P.centers i).1 p.1.1 p.1.2, p.2⟩ :
        HalfPlaneTangentFrame) := rfl

@[simp] theorem outgoingTangentCollarPolarHomeomorph_frame
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (p : (Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) × Circle) :
    (P.outgoingTangentCollarPolarHomeomorph i p).1.1 =
      Quotient.mk _ (⟨gluingPolarPoint (P.centers i).2 p.1.1 p.1.2, p.2⟩ :
        HalfPlaneTangentFrame) := rfl

/-- The true native cylinder coordinates of an incoming physical frame. -/
def incomingTangentCollarNativeCylinderCoordinates
    (P : ExerciseGluingPreparation C g n genera X)
    (p : (Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) × Circle) :
    GluingSeamCylinder C g × Circle :=
  ((p.1.1⁻¹, ⟨p.1.2.1 - gluingRadius C g, by
    constructor
    · linarith [p.1.2.2.1, P.depth_pos]
    · change p.1.2.1 - gluingRadius C g < gluingDepth C g
      have hu := p.1.2.2.2
      change p.1.2.1 < gluingRadius C g + gluingDepth C g at hu
      linarith⟩), (p.2 / gluingPolarRadialCircle p.1.2 p.1.1)⁻¹)

def outgoingTangentCollarNativeCylinderCoordinates
    (P : ExerciseGluingPreparation C g n genera X)
    (p : (Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) × Circle) :
    GluingSeamCylinder C g × Circle :=
  ((p.1.1, ⟨gluingRadius C g - p.1.2.1, by
    constructor
    · have hu := p.1.2.2.2
      change p.1.2.1 < gluingRadius C g + gluingDepth C g at hu
      linarith
    · linarith [p.1.2.2.1, P.depth_pos]⟩),
      (p.2 / -gluingPolarRadialCircle p.1.2 p.1.1)⁻¹)

theorem continuous_incomingTangentCollarNativeCylinderCoordinates
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.incomingTangentCollarNativeCylinderCoordinates := by
  have hR := (continuous_subtype_val.comp continuous_fst.snd :
    Continuous (fun p : (Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) ×
      Circle => (p.1.2 : ℝ)))
  exact (continuous_fst.fst.inv.prodMk ((hR.sub continuous_const).subtype_mk _)).prodMk
    ((continuous_snd.div' (continuous_gluingPolarRadialCircle.comp
      (hR.prodMk continuous_fst.fst))).inv)

theorem continuous_outgoingTangentCollarNativeCylinderCoordinates
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.outgoingTangentCollarNativeCylinderCoordinates := by
  have hR := (continuous_subtype_val.comp continuous_fst.snd :
    Continuous (fun p : (Circle × Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g)) ×
      Circle => (p.1.2 : ℝ)))
  exact (continuous_fst.fst.prodMk ((continuous_const.sub hR).subtype_mk _)).prodMk
    ((continuous_snd.div' (continuous_gluingPolarRadialCircle.comp
      (hR.prodMk continuous_fst.fst)).neg).inv)

/-- An actual incoming retained-component frame transported to the genuine
native unit tangent total space, using the full native seam cylinder. -/
def incomingTangentCollarNativeUnit
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.IncomingTangentCollar (gluingChainEdgeRight k)) : P.NativeUnitTangentCarrier :=
  (P.nativeSeamCylinderUnitTangentHomeomorph k
    (P.incomingTangentCollarNativeCylinderCoordinates
      ((P.incomingTangentCollarPolarHomeomorph _).symm q))).1

def outgoingTangentCollarNativeUnit
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.OutgoingTangentCollar (gluingChainEdgeLeft k)) : P.NativeUnitTangentCarrier :=
  (P.nativeSeamCylinderUnitTangentHomeomorph k
    (P.outgoingTangentCollarNativeCylinderCoordinates
      ((P.outgoingTangentCollarPolarHomeomorph _).symm q))).1

theorem continuous_incomingTangentCollarNativeUnit
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (P.incomingTangentCollarNativeUnit k) :=
  continuous_subtype_val.comp ((P.nativeSeamCylinderUnitTangentHomeomorph k).continuous.comp
    (P.continuous_incomingTangentCollarNativeCylinderCoordinates.comp
      (P.incomingTangentCollarPolarHomeomorph _).symm.continuous))

theorem continuous_outgoingTangentCollarNativeUnit
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (P.outgoingTangentCollarNativeUnit k) :=
  continuous_subtype_val.comp ((P.nativeSeamCylinderUnitTangentHomeomorph k).continuous.comp
    (P.continuous_outgoingTangentCollarNativeCylinderCoordinates.comp
      (P.outgoingTangentCollarPolarHomeomorph _).symm.continuous))

theorem incomingTangentCollarNativeUnit_proj
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.IncomingTangentCollar (gluingChainEdgeRight k)) :
    (P.incomingTangentCollarNativeUnit k q).1.proj =
      P.gluedMk ⟨gluingChainEdgeRight k, P.tangentChainComponentBase _ q.1⟩ := by
  obtain ⟨p, rfl⟩ := (P.incomingTangentCollarPolarHomeomorph _).surjective q
  unfold incomingTangentCollarNativeUnit
  rw [Homeomorph.symm_apply_apply, P.nativeSeamCylinderUnitTangentHomeomorph_proj]
  rw [P.seamCylinderHomeomorph_apply_of_nonneg _ _
    (show 0 ≤ p.1.2.1 - gluingRadius C g from sub_nonneg.mpr p.1.2.2.1)]
  congr 1
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    change (X _).orbitProjection
      (gluingPolarPoint (P.centers _).1 (p.1.1⁻¹)⁻¹
        (gluingRadius C g + (p.1.2.1 - gluingRadius C g))) =
      (X _).orbitProjection (gluingPolarPoint (P.centers _).1 p.1.1 p.1.2.1)
    rw [inv_inv, add_sub_cancel]

theorem outgoingTangentCollarNativeUnit_proj
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.OutgoingTangentCollar (gluingChainEdgeLeft k)) :
    (P.outgoingTangentCollarNativeUnit k q).1.proj =
      P.gluedMk ⟨gluingChainEdgeLeft k, P.tangentChainComponentBase _ q.1⟩ := by
  obtain ⟨p, rfl⟩ := (P.outgoingTangentCollarPolarHomeomorph _).surjective q
  unfold outgoingTangentCollarNativeUnit
  rw [Homeomorph.symm_apply_apply, P.nativeSeamCylinderUnitTangentHomeomorph_proj]
  rw [P.seamCylinderHomeomorph_apply_of_nonpos _ _
    (show gluingRadius C g - p.1.2.1 ≤ 0 from sub_nonpos.mpr p.1.2.2.1)]
  congr 1
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    change (X _).orbitProjection
      (gluingPolarPoint (P.centers _).2 p.1.1
        (gluingRadius C g - (gluingRadius C g - p.1.2.1))) =
      (X _).orbitProjection (gluingPolarPoint (P.centers _).2 p.1.1 p.1.2.1)
    rw [sub_sub_cancel]

theorem incomingTangentCollarNativeCylinderCoordinates_injective
    (P : ExerciseGluingPreparation C g n genera X) :
    Function.Injective P.incomingTangentCollarNativeCylinderCoordinates := by
  intro p q h
  have ha : p.1.1 = q.1.1 := inv_injective (congrArg (fun v => v.1.1) h)
  have hr : p.1.2 = q.1.2 := by
    apply Subtype.ext
    have hs := congrArg (fun v : GluingSeamCylinder C g × Circle => v.1.2.1) h
    change p.1.2.1 - gluingRadius C g = q.1.2.1 - gluingRadius C g at hs
    linarith
  have hb := Prod.ext ha hr
  apply Prod.ext hb
  have hu := congrArg Prod.snd h
  change (p.2 / gluingPolarRadialCircle p.1.2 p.1.1)⁻¹ =
    (q.2 / gluingPolarRadialCircle q.1.2 q.1.1)⁻¹ at hu
  rw [hb] at hu
  exact div_left_injective (inv_injective hu)

theorem outgoingTangentCollarNativeCylinderCoordinates_injective
    (P : ExerciseGluingPreparation C g n genera X) :
    Function.Injective P.outgoingTangentCollarNativeCylinderCoordinates := by
  intro p q h
  have ha : p.1.1 = q.1.1 := congrArg (fun v => v.1.1) h
  have hr : p.1.2 = q.1.2 := by
    apply Subtype.ext
    have hs := congrArg (fun v : GluingSeamCylinder C g × Circle => v.1.2.1) h
    change gluingRadius C g - p.1.2.1 = gluingRadius C g - q.1.2.1 at hs
    linarith
  have hb := Prod.ext ha hr
  apply Prod.ext hb
  have hu := congrArg Prod.snd h
  change (p.2 / -gluingPolarRadialCircle p.1.2 p.1.1)⁻¹ =
    (q.2 / -gluingPolarRadialCircle q.1.2 q.1.1)⁻¹ at hu
  rw [hb] at hu
  exact div_left_injective (inv_injective hu)

theorem incomingTangentCollarNativeCylinderCoordinates_surjective_half
    (P : ExerciseGluingPreparation C g n genera X)
    (q : GluingSeamCylinder C g × Circle) (hq : 0 ≤ q.1.2.1) :
    ∃ p, P.incomingTangentCollarNativeCylinderCoordinates p = q := by
  let ρ : Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
    ⟨gluingRadius C g + q.1.2.1, by
      constructor
      · linarith
      · change gluingRadius C g + q.1.2.1 < gluingRadius C g + gluingDepth C g
        linarith [q.1.2.2.2]⟩
  refine ⟨((q.1.1⁻¹, ρ), gluingIncomingPhysicalCircle (gluingRadius C g)
    q.1.2.1 q.1.1 q.2), ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · exact inv_inv _
    · apply Subtype.ext
      change gluingRadius C g + q.1.2.1 - gluingRadius C g = q.1.2.1
      ring
  · change
      (gluingIncomingPhysicalCircle (gluingRadius C g) q.1.2.1 q.1.1 q.2 /
        gluingPolarRadialCircle (gluingRadius C g + q.1.2.1) q.1.1⁻¹)⁻¹ = q.2
    simp [gluingIncomingPhysicalCircle, mul_comm]

theorem outgoingTangentCollarNativeCylinderCoordinates_surjective_half
    (P : ExerciseGluingPreparation C g n genera X)
    (q : GluingSeamCylinder C g × Circle) (hq : q.1.2.1 ≤ 0) :
    ∃ p, P.outgoingTangentCollarNativeCylinderCoordinates p = q := by
  let ρ : Set.Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
    ⟨gluingRadius C g - q.1.2.1, by
      constructor
      · linarith
      · change gluingRadius C g - q.1.2.1 < gluingRadius C g + gluingDepth C g
        linarith [q.1.2.2.1]⟩
  refine ⟨((q.1.1, ρ), gluingOutgoingPhysicalCircle (gluingRadius C g)
    q.1.2.1 q.1.1 q.2), ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      change gluingRadius C g - (gluingRadius C g - q.1.2.1) = q.1.2.1
      ring
  · change
      (gluingOutgoingPhysicalCircle (gluingRadius C g) q.1.2.1 q.1.1 q.2 /
        -gluingPolarRadialCircle (gluingRadius C g - q.1.2.1) q.1.1)⁻¹ = q.2
    simp [gluingOutgoingPhysicalCircle, mul_comm]

theorem incomingTangentCollarNativeUnit_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Function.Injective (P.incomingTangentCollarNativeUnit k) := by
  intro p q h
  apply (P.incomingTangentCollarPolarHomeomorph _).symm.injective
  apply P.incomingTangentCollarNativeCylinderCoordinates_injective
  apply (P.nativeSeamCylinderUnitTangentHomeomorph k).injective
  exact Subtype.ext h

theorem outgoingTangentCollarNativeUnit_injective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Function.Injective (P.outgoingTangentCollarNativeUnit k) := by
  intro p q h
  apply (P.outgoingTangentCollarPolarHomeomorph _).symm.injective
  apply P.outgoingTangentCollarNativeCylinderCoordinates_injective
  apply (P.nativeSeamCylinderUnitTangentHomeomorph k).injective
  exact Subtype.ext h

/-- Every actual native unit direction over an incoming collar base has a
unique physical component-frame preimage in that actual retained collar. -/
theorem incomingTangentCollarNativeUnit_surjective_fiber
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.IncomingTangentCollar (gluingChainEdgeRight k))
    (v : P.NativeUnitTangentCarrier)
    (hv : v.1.proj = (P.incomingTangentCollarNativeUnit k q).1.proj) :
    ∃! q', P.incomingTangentCollarNativeUnit k q' = v := by
  let p := (P.incomingTangentCollarPolarHomeomorph _).symm q
  let a := P.incomingTangentCollarNativeCylinderCoordinates p
  have hmem : v.1.proj ∈ P.gluedMk '' P.seamNeighborhood k := by
    rw [hv]
    exact (P.nativeSeamCylinderUnitTangentHomeomorph k a).2
  let v' : P.NativeSeamUnitTangentOver k := ⟨v, hmem⟩
  let c := (P.nativeSeamCylinderUnitTangentHomeomorph k).symm v'
  have hcbase : c.1 = a.1 := by
    apply (P.seamCylinderHomeomorph k).injective
    apply Subtype.ext
    have h := congrArg (fun w : P.NativeSeamUnitTangentOver k => w.1.1.proj)
      ((P.nativeSeamCylinderUnitTangentHomeomorph k).apply_symm_apply v')
    change (P.seamCylinderHomeomorph k c.1).1 = v.1.proj at h
    exact h.trans hv
  have hcpos : 0 ≤ c.1.2.1 := by
    rw [hcbase]
    exact sub_nonneg.mpr p.1.2.2.1
  obtain ⟨r, hr⟩ := P.incomingTangentCollarNativeCylinderCoordinates_surjective_half c hcpos
  let q' := P.incomingTangentCollarPolarHomeomorph (gluingChainEdgeRight k) r
  have hq' : P.incomingTangentCollarNativeUnit k q' = v := by
    unfold incomingTangentCollarNativeUnit
    rw [Homeomorph.symm_apply_apply, hr]
    exact congrArg Subtype.val ((P.nativeSeamCylinderUnitTangentHomeomorph k).apply_symm_apply v')
  refine ⟨q', hq', ?_⟩
  intro w hw
  exact P.incomingTangentCollarNativeUnit_injective k (hw.trans hq'.symm)

theorem outgoingTangentCollarNativeUnit_surjective_fiber
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : P.OutgoingTangentCollar (gluingChainEdgeLeft k))
    (v : P.NativeUnitTangentCarrier)
    (hv : v.1.proj = (P.outgoingTangentCollarNativeUnit k q).1.proj) :
    ∃! q', P.outgoingTangentCollarNativeUnit k q' = v := by
  let p := (P.outgoingTangentCollarPolarHomeomorph _).symm q
  let a := P.outgoingTangentCollarNativeCylinderCoordinates p
  have hmem : v.1.proj ∈ P.gluedMk '' P.seamNeighborhood k := by
    rw [hv]
    exact (P.nativeSeamCylinderUnitTangentHomeomorph k a).2
  let v' : P.NativeSeamUnitTangentOver k := ⟨v, hmem⟩
  let c := (P.nativeSeamCylinderUnitTangentHomeomorph k).symm v'
  have hcbase : c.1 = a.1 := by
    apply (P.seamCylinderHomeomorph k).injective
    apply Subtype.ext
    have h := congrArg (fun w : P.NativeSeamUnitTangentOver k => w.1.1.proj)
      ((P.nativeSeamCylinderUnitTangentHomeomorph k).apply_symm_apply v')
    change (P.seamCylinderHomeomorph k c.1).1 = v.1.proj at h
    exact h.trans hv
  have hcneg : c.1.2.1 ≤ 0 := by
    rw [hcbase]
    exact sub_nonpos.mpr p.1.2.2.1
  obtain ⟨r, hr⟩ := P.outgoingTangentCollarNativeCylinderCoordinates_surjective_half c hcneg
  let q' := P.outgoingTangentCollarPolarHomeomorph (gluingChainEdgeLeft k) r
  have hq' : P.outgoingTangentCollarNativeUnit k q' = v := by
    unfold outgoingTangentCollarNativeUnit
    rw [Homeomorph.symm_apply_apply, hr]
    exact congrArg Subtype.val ((P.nativeSeamCylinderUnitTangentHomeomorph k).apply_symm_apply v')
  refine ⟨q', hq', ?_⟩
  intro w hw
  exact P.outgoingTangentCollarNativeUnit_injective k (hw.trans hq'.symm)

/-- The two true collar maps agree on the literal squared spin-clutching
of physical boundary directions, not on an assumed atlas phase. -/
theorem tangentCollarNativeUnit_boundary_param
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (a u : Circle) :
    P.incomingTangentCollarNativeUnit k
      (P.incomingTangentCollarPolarHomeomorph _
        ((a⁻¹, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩),
          gluingFermiBoundarySpinCircle (gluingRadius C g) a⁻¹ ^ 2 * u)) =
    P.outgoingTangentCollarNativeUnit k
      (P.outgoingTangentCollarPolarHomeomorph _
        ((a, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩), u)) := by
  unfold incomingTangentCollarNativeUnit outgoingTangentCollarNativeUnit
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  congr 2
  apply Prod.ext
  · apply Prod.ext
    · exact inv_inv a
    · apply Subtype.ext
      rfl
  · change
      ((gluingFermiBoundarySpinCircle (gluingRadius C g) a⁻¹ ^ 2 * u) /
        gluingPolarRadialCircle (gluingRadius C g) a⁻¹)⁻¹ =
          (u / -gluingPolarRadialCircle (gluingRadius C g) a)⁻¹
    have h := gluingPhysicalCircle_boundary_clutching (gluingRadius C g) a 1
    simp only [gluingOutgoingPhysicalCircle, gluingIncomingPhysicalCircle,
      sub_zero, add_zero, inv_one, mul_one] at h
    rw [← h]
    congr 1
    simp [div_eq_mul_inv, mul_comm, mul_assoc]

def tangentIncomingBoundaryCollarInclusion
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : (X i).TangentBoundaryCarrier (P.centers i).1 (gluingRadius C g)) :
    P.IncomingTangentCollar i :=
  ⟨P.tangentLeftBoundaryInclusion i q, by
    obtain ⟨p, rfl⟩ := (X i).tangentBoundaryParam_surjective _ _ q
    refine ⟨gluingPolarPoint (P.centers i).1 p.1 (gluingRadius C g), ⟨?_, ?_⟩, rfl⟩
    · simpa [Metric.mem_ball, dist_comm, dist_gluingPolarPoint _ p.1 P.radius_pos.le]
        using P.radius_lt_embeddedRadius
    · simp [Metric.mem_ball, dist_comm, dist_gluingPolarPoint _ p.1 P.radius_pos.le]⟩

def tangentOutgoingBoundaryCollarInclusion
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : (X i).TangentBoundaryCarrier (P.centers i).2 (gluingRadius C g)) :
    P.OutgoingTangentCollar i :=
  ⟨P.tangentRightBoundaryInclusion i q, by
    obtain ⟨p, rfl⟩ := (X i).tangentBoundaryParam_surjective _ _ q
    refine ⟨gluingPolarPoint (P.centers i).2 p.1 (gluingRadius C g), ⟨?_, ?_⟩, rfl⟩
    · simpa [Metric.mem_ball, dist_comm, dist_gluingPolarPoint _ p.1 P.radius_pos.le]
        using P.radius_lt_embeddedRadius
    · simp [Metric.mem_ball, dist_comm, dist_gluingPolarPoint _ p.1 P.radius_pos.le]⟩

/-- Actual incoming/outgoing boundary restrictions give the same native
unit tangent after the genuine component seam homeomorphism. -/
theorem tangentCollarNativeUnit_boundary_clutching
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.incomingTangentCollarNativeUnit k
      (P.tangentIncomingBoundaryCollarInclusion _ (P.seamTangentHomeomorph k q)) =
    P.outgoingTangentCollarNativeUnit k
      (P.tangentOutgoingBoundaryCollarInclusion _ q) := by
  obtain ⟨p, rfl⟩ := (X (gluingChainEdgeLeft k)).tangentBoundaryParam_surjective _ _ q
  have ht := ClosedHyperbolicSurface.fermiTangentBoundaryHomeomorph_param
    (X (gluingChainEdgeRight k)) (X (gluingChainEdgeLeft k))
    (P.centers (gluingChainEdgeRight k)).1 (P.centers (gluingChainEdgeLeft k)).2
    P.radius_pos P.radius_lt_embeddedRadius P.radius_lt_embeddedRadius
    (P.twice_outer_lt_systole _) (P.twice_outer_lt_systole _) p
  change P.seamTangentHomeomorph k _ = _ at ht
  rw [ht]
  exact P.tangentCollarNativeUnit_boundary_param k p.1 p.2

theorem Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularPoint k θ p ∈ (P.seamAngularComplexChart k θ).source := by
  rw [P.seamAngularComplexChart_source]
  exact ⟨p, rfl⟩

private theorem nativeUnitTangentCoord_injective
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) :
    Function.Injective (P.nativeUnitTangentCoord e he b) := by
  intro v w h
  apply Subtype.ext
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  apply (t.continuousLinearEquivAt ℝ b (by exact hb)).injective
  rw [t.coe_continuousLinearEquivAt_eq (by exact hb)]
  exact h

theorem nativeInteriorUnitTangentParam_coordinates
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (u : Circle) :
    P.nativeUnitTangentCoord e (Or.inl he) b (P.nativeUnitTangentParam e (Or.inl he) b hb u) =
      ((e b).im : ℂ) * (u : ℂ) := by
  have him := P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hb)
  rw [P.nativeUnitTangentCoord_param, P.gluingChartTangentForm_interior _ he,
    gluingComplexHalfPlaneTangentForm_apply, Complex.mul_conj', Circle.norm_coe]
  simp only [Complex.ofReal_one, one_pow, Complex.one_re]
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq_eq_abs,
    abs_of_pos him, one_div, inv_inv]
  rfl

/-- Genuine native interior unit coordinates transform by the actual local
deck differential. The multiplier is derived from the literal atlas overlap. -/
theorem nativeInteriorUnitTangentParam_overlap
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (b : P.GluedCarrier) (hb : b ∈ e.source) (hb' : b ∈ e'.source) (u : Circle) :
    ∃ A : SL(2, ℝ),
      e' b = ((A • UpperHalfPlane.ofComplex (e b) : ℍ) : ℂ) ∧
      P.nativeUnitTangentParam e (Or.inl he) b hb u =
        P.nativeUnitTangentParam e' (Or.inl he') b hb'
          (halfPlaneSpinCircle A (UpperHalfPlane.ofComplex (e b)) ^ 2 * u) := by
  have hx : e b ∈ (e.symm.trans e').source := by
    refine ⟨e.map_source hb, ?_⟩
    change e.symm (e b) ∈ e'.source
    rw [e.left_inv hb]
    exact hb'
  obtain ⟨him, A, hA⟩ := P.gluedInteriorComplexAtlas_transition_eventually_eq_deck e e' he he'
    (e b) hx
  let z := UpperHalfPlane.ofComplex (e b)
  have hz : (z : ℂ) = e b :=
    congrArg (fun w : ℍ => (w : ℂ)) (UpperHalfPlane.ofComplex_apply_of_im_pos him)
  have hAz : ((A • z : ℍ) : ℂ) = e' b := by
    rw [← gluingDeckComplex_coe, hz]
    have hv : (e.symm.trans e') (e b) = e' b := by
      change e' (e.symm (e b)) = e' b
      rw [e.left_inv hb]
    exact hA.self_of_nhds.symm.trans hv
  refine ⟨A, hAz.symm, ?_⟩
  apply P.nativeUnitTangentCoord_injective e' (Or.inl he') b hb'
  rw [P.nativeInteriorUnitTangentParam_coordinates e' he' b hb']
  have ht := P.nativeTangentCoordChange_apply e e' (Or.inl he) (Or.inl he') b hb hb'
    (((e b).im : ℂ) * (u : ℂ))
  have hv := P.nativeInteriorUnitTangentParam_coordinates e he b hb u
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, Or.inl he⟩ : atlas ℂ P.GluedCarrier)
  have heq : t.symmL ℝ b (((e b).im : ℂ) * (u : ℂ)) =
      (P.nativeUnitTangentParam e (Or.inl he) b hb u).val := by
    rw [← hv]
    exact t.symmL_continuousLinearMapAt (by exact hb) _
  rw [heq] at ht
  change P.nativeUnitTangentCoord e' (Or.inl he') b _ = _ at ht
  rw [ht, hA.fderiv_eq, ← hz]
  have hs := gluingDeckComplex_fderiv_unit_vector A z (u : ℂ)
  rw [Circle.coe_mul, Circle.coe_pow]
  simp only [UpperHalfPlane.ofComplex_apply]
  change fderiv ℝ (gluingDeckComplex A) (z : ℂ) ((z.im : ℂ) * (u : ℂ)) =
    ((e' b).im : ℂ) * ((halfPlaneSpinCircle A z : ℂ) ^ 2 * (u : ℂ))
  have him' : (A • z : ℍ).im = (e' b).im := congrArg Complex.im hAz
  rw [← him']
  exact hs

theorem incomingNativeUnitCoordinates_components
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : 0 ≤ p.1.1) (u : Circle) :
    gluingCollarOrthonormalComponents (gluingRadius C g)
      (P.seamAngularComplexChart k θ (P.seamAngularPoint k θ p))
      (P.incomingNativeUnitCoordinates o θ p hs u) =
        (gluingFermiIncomingNativePhase (gluingRadius C g) (p.1.1, -p.2.1) u : ℂ) := by
  have h := gluingFermiIncomingUnitVectorCoordinates_weighted o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  rw [P.seamAngularComplexChart_apply]
  change _ = (↑((u / gluingFermiIncomingSpinCircle (gluingRadius C g)
    (p.1.1, -p.2.1) ^ 2)⁻¹) : ℂ)
  rw [Circle.coe_inv_eq_conj, Circle.coe_div, Circle.coe_pow]
  simpa [gluingCollarOrthonormalComponents, incomingNativeUnitCoordinates,
    gluingSeamAngularModel, gluingCollarWarp, abs_of_nonneg hs, complex_conj_mk] using
      congrArg (starRingEnd ℂ) h

theorem outgoingNativeUnitCoordinates_components
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 ≤ 0) (u : Circle) :
    gluingCollarOrthonormalComponents (gluingRadius C g)
      (P.seamAngularComplexChart k θ (P.seamAngularPoint k θ p))
      (P.outgoingNativeUnitCoordinates o θ p hs u) =
        (gluingFermiOutgoingNativePhase (gluingRadius C g) (p.1.1, -p.2.1) u : ℂ) := by
  have h := gluingFermiOutgoingUnitVectorCoordinates_weighted o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  rw [P.seamAngularComplexChart_apply]
  change _ = (↑((u / gluingFermiOutgoingSpinCircle (gluingRadius C g)
    (p.1.1, -p.2.1) ^ 2)⁻¹) : ℂ)
  rw [Circle.coe_inv_eq_conj, Circle.coe_div, Circle.coe_pow]
  simpa [gluingCollarOrthonormalComponents, outgoingNativeUnitCoordinates,
    gluingSeamAngularModel, gluingCollarWarp, abs_of_nonpos hs, sub_eq_add_neg, complex_conj_mk] using
      congrArg (starRingEnd ℂ) h

/-- The real derivative of the actual native incoming polar branch sends
the transported native vector back to its literal physical unit vector. -/
theorem incomingNativeUnitCoordinates_fderiv
    (P : ExerciseGluingPreparation C g n genera X) (o : ℍ) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hs : 0 ≤ p.1.1) (u : Circle) :
    fderiv ℝ (gluingIncomingPolarLift o (gluingRadius C g))
      (gluingSeamAngularModel C g θ p) (P.incomingNativeUnitCoordinates o θ p hs u) =
      ((gluingPolarPoint o (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1)).im : ℂ) *
        (u : ℂ) := by
  let z := gluingSeamAngularModel C g θ p
  let v := gluingFermiIncomingUnitVectorCoordinates o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  have h := (gluingPolarLift_hasFDerivAt o (gluingIncomingPolarCoordinates (gluingRadius C g) z)).comp z
    (gluingIncomingPolarCoordinates_hasFDerivAt (gluingRadius C g) z)
  change HasFDerivAt (gluingIncomingPolarLift o (gluingRadius C g)) _ z at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have hv : (gluingIncomingPolarCoordinateDeriv : ℂ →L[ℝ] ℝ × ℝ)
      (P.incomingNativeUnitCoordinates o θ p hs u) = v := by
    apply Prod.ext <;> simp [gluingIncomingPolarCoordinateDeriv, incomingNativeUnitCoordinates, v,
      ContinuousLinearEquiv.smulLeft]
  rw [hv]
  change gluingPolarLiftFDeriv o (gluingRadius C g + p.1.1, -p.2.1) v = _
  rw [← (gluingPolarLift_hasFDerivAt o (gluingRadius C g + p.1.1, -p.2.1)).fderiv]
  rw [← gluingFermiIncomingLift_fderiv_apply o (gluingRadius C g) (p.1.1, -p.2.1) v,
    ← gluingFermiIncomingDerivEquiv_toCLM o (gluingRadius C g) (p.1.1, -p.2.1)
      (by linarith [P.radius_pos])]
  exact (gluingFermiIncomingDerivEquiv o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos])).apply_symm_apply _

theorem outgoingNativeUnitCoordinates_fderiv
    (P : ExerciseGluingPreparation C g n genera X) (o : ℍ) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hs : p.1.1 ≤ 0) (u : Circle) :
    fderiv ℝ (gluingOutgoingPolarLift o (gluingRadius C g))
      (gluingSeamAngularModel C g θ p) (P.outgoingNativeUnitCoordinates o θ p hs u) =
      ((gluingPolarPoint o (Circle.exp p.2.1) (gluingRadius C g - p.1.1)).im : ℂ) *
        (u : ℂ) := by
  let z := gluingSeamAngularModel C g θ p
  let v := gluingFermiOutgoingUnitVectorCoordinates o (gluingRadius C g)
    (p.1.1, -p.2.1) (by linarith [P.radius_pos]) u
  have h := (gluingPolarLift_hasFDerivAt o (gluingOutgoingPolarCoordinates (gluingRadius C g) z)).comp z
    (gluingOutgoingPolarCoordinates_hasFDerivAt (gluingRadius C g) z)
  change HasFDerivAt (gluingOutgoingPolarLift o (gluingRadius C g)) _ z at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have hv : (gluingOutgoingPolarCoordinateDeriv : ℂ →L[ℝ] ℝ × ℝ)
      (P.outgoingNativeUnitCoordinates o θ p hs u) = -v := by
    apply Prod.ext <;> simp [gluingOutgoingPolarCoordinateDeriv, outgoingNativeUnitCoordinates, v,
      ContinuousLinearEquiv.smulLeft]
  rw [hv, map_neg]
  change -(gluingPolarLiftFDeriv o (gluingRadius C g - p.1.1, p.2.1) v) = _
  rw [← (gluingPolarLift_hasFDerivAt o (gluingRadius C g - p.1.1, p.2.1)).fderiv]
  have hF := gluingFermiOutgoingLift_fderiv_apply o (gluingRadius C g) (p.1.1, -p.2.1) v
  simp only [neg_neg] at hF
  rw [← hF, ← gluingFermiOutgoingDerivEquiv_toCLM o (gluingRadius C g) (p.1.1, -p.2.1)
    (by linarith [P.radius_pos])]
  have hvunit : (gluingFermiOutgoingDerivEquiv o (gluingRadius C g)
      (p.1.1, -p.2.1) (by linarith [P.radius_pos]) : (ℝ × ℝ) →L[ℝ] ℂ) v =
      ((gluingFermiOutgoingLift o (gluingRadius C g) (p.1.1, -p.2.1)).im : ℂ) * (u : ℂ) :=
    (gluingFermiOutgoingDerivEquiv o (gluingRadius C g)
      (p.1.1, -p.2.1) (by linarith [P.radius_pos])).apply_symm_apply _
  have hi : (gluingFermiOutgoingLift o (gluingRadius C g) (p.1.1, -p.2.1)).im =
      (gluingPolarPoint o (Circle.exp p.2.1) (gluingRadius C g - p.1.1)).im := by
    change (gluingPolarPoint o (Circle.exp (-(-p.2.1)))
      (gluingRadius C g - p.1.1)).im = _
    rw [neg_neg]
  rw [hi] at hvunit
  exact hvunit

/-- Every genuine seam/interior overlap transports the literal component
physical directions into exactly the same original native unit tangent.
The actual overlap itself determines its center, deck map and side. -/
theorem nativeSeamInteriorUnitTangentParam_overlap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (hb : P.seamAngularPoint k θ p ∈ e.source) :
    (∃ (o : ℍ) (A : SL(2, ℝ)) (hs : p.1.1 < 0),
      e (P.seamAngularPoint k θ p) =
        ((A • gluingPolarPoint o (Circle.exp p.2.1) (gluingRadius C g - p.1.1) : ℍ) : ℂ) ∧
      ∀ u : Circle, P.outgoingNativeUnitTangent k o θ p hs.le u =
        P.nativeUnitTangentParam e (Or.inl he) (P.seamAngularPoint k θ p) hb
          (halfPlaneSpinCircle A
            (gluingPolarPoint o (Circle.exp p.2.1) (gluingRadius C g - p.1.1)) ^ 2 * u)) ∨
    (∃ (o : ℍ) (A : SL(2, ℝ)) (hs : 0 < p.1.1),
      e (P.seamAngularPoint k θ p) =
        ((A • gluingPolarPoint o (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1) : ℍ) : ℂ) ∧
      ∀ u : Circle, P.incomingNativeUnitTangent k o θ p hs.le u =
        P.nativeUnitTangentParam e (Or.inl he) (P.seamAngularPoint k θ p) hb
          (halfPlaneSpinCircle A
            (gluingPolarPoint o (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1)) ^ 2 * u)) := by
  let x := gluingSeamAngularModel C g θ p
  let b := P.seamAngularPoint k θ p
  have hsource := Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p
  have hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source := by
    refine ⟨?_, ?_⟩
    · change gluingSeamAngularModel C g θ p ∈ (P.seamAngularComplexChart k θ).target
      rw [← P.seamAngularComplexChart_apply k θ p]
      exact (P.seamAngularComplexChart k θ).map_source hsource
    · change (P.seamAngularComplexChart k θ).symm x ∈ e.source
      rw [P.seamAngularComplexChart_symm_apply]
      exact hb
  have hxb : ((P.seamAngularComplexChart k θ).symm.trans e) x = e b := by
    change e ((P.seamAngularComplexChart k θ).symm x) = e b
    rw [P.seamAngularComplexChart_symm_apply]
  rcases P.seamInterior_transition_eventually_eq_deck_polar k θ e he hx with
    ⟨o, A, hs, hA⟩ | ⟨o, A, hs, hA⟩
  · let z := gluingPolarPoint o (Circle.exp p.2.1) (gluingRadius C g - p.1.1)
    have hAz : ((A • z : ℍ) : ℂ) = e b := by
      rw [← gluingDeckComplex_coe]
      exact hA.self_of_nhds.symm.trans hxb
    refine Or.inl ⟨o, A, hs, hAz.symm, ?_⟩
    intro u
    apply P.nativeUnitTangentCoord_injective e (Or.inl he) b hb
    rw [P.nativeInteriorUnitTangentParam_coordinates e he b hb]
    rw [P.nativeUnitTangentCoord_change (P.seamAngularComplexChart k θ) e
      (Or.inr ⟨k, θ, rfl⟩) (Or.inl he) b hsource hb]
    have hc : P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ)
        (Or.inr ⟨k, θ, rfl⟩) b (P.outgoingNativeUnitTangent k o θ p hs.le u) =
        P.outgoingNativeUnitCoordinates o θ p hs.le u :=
      P.nativeUnitTangentCoord_ofCoordinates _ _ _ _ _ _
    rw [hc, P.seamAngularComplexChart_apply, hA.fderiv_eq,
      fderiv_comp (f := gluingOutgoingPolarLift o (gluingRadius C g))
        (g := gluingDeckComplex A) x
        (gluingDeckComplex_hasFDerivAt_equiv A z.im_pos).differentiableAt
        ((gluingOutgoingPolarLift_contDiff o (gluingRadius C g)).differentiable
          (by simp)).differentiableAt,
      ContinuousLinearMap.comp_apply]
    dsimp only [x]
    rw [P.outgoingNativeUnitCoordinates_fderiv o θ p hs.le u]
    rw [Circle.coe_mul, Circle.coe_pow]
    change fderiv ℝ (gluingDeckComplex A) (z : ℂ) ((z.im : ℂ) * (u : ℂ)) =
      ((e b).im : ℂ) * ((halfPlaneSpinCircle A z : ℂ) ^ 2 * (u : ℂ))
    have him : (A • z : ℍ).im = (e b).im := congrArg Complex.im hAz
    rw [← him]
    exact gluingDeckComplex_fderiv_unit_vector A z (u : ℂ)
  · let z := gluingPolarPoint o (Circle.exp (-p.2.1)) (gluingRadius C g + p.1.1)
    have hAz : ((A • z : ℍ) : ℂ) = e b := by
      rw [← gluingDeckComplex_coe]
      exact hA.self_of_nhds.symm.trans hxb
    refine Or.inr ⟨o, A, hs, hAz.symm, ?_⟩
    intro u
    apply P.nativeUnitTangentCoord_injective e (Or.inl he) b hb
    rw [P.nativeInteriorUnitTangentParam_coordinates e he b hb]
    rw [P.nativeUnitTangentCoord_change (P.seamAngularComplexChart k θ) e
      (Or.inr ⟨k, θ, rfl⟩) (Or.inl he) b hsource hb]
    have hc : P.nativeUnitTangentCoord (P.seamAngularComplexChart k θ)
        (Or.inr ⟨k, θ, rfl⟩) b (P.incomingNativeUnitTangent k o θ p hs.le u) =
        P.incomingNativeUnitCoordinates o θ p hs.le u :=
      P.nativeUnitTangentCoord_ofCoordinates _ _ _ _ _ _
    rw [hc, P.seamAngularComplexChart_apply, hA.fderiv_eq,
      fderiv_comp (f := gluingIncomingPolarLift o (gluingRadius C g))
        (g := gluingDeckComplex A) x
        (gluingDeckComplex_hasFDerivAt_equiv A z.im_pos).differentiableAt
        ((gluingIncomingPolarLift_contDiff o (gluingRadius C g)).differentiable
          (by simp)).differentiableAt,
      ContinuousLinearMap.comp_apply]
    dsimp only [x]
    rw [P.incomingNativeUnitCoordinates_fderiv o θ p hs.le u]
    rw [Circle.coe_mul, Circle.coe_pow]
    change fderiv ℝ (gluingDeckComplex A) (z : ℂ) ((z.im : ℂ) * (u : ℂ)) =
      ((e b).im : ℂ) * ((halfPlaneSpinCircle A z : ℂ) ^ 2 * (u : ℂ))
    have him : (A • z : ℍ).im = (e b).im := congrArg Complex.im hAz
    rw [← him]
    exact gluingDeckComplex_fderiv_unit_vector A z (u : ℂ)

/-- Genuine incoming physical frames agree with the original native
orthonormal chart, including the actual orientation correction. -/
theorem incomingNativeUnitTangent_eq_seamParam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : 0 ≤ p.1.1) (u : Circle) :
    P.incomingNativeUnitTangent k o θ p hs u =
      P.nativeSeamUnitTangentParam k θ (P.seamAngularPoint k θ p)
        (Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p)
        (gluingFermiIncomingNativePhase (gluingRadius C g) (p.1.1, -p.2.1) u) := by
  apply Eq.symm
  apply P.nativeSeamUnitTangentParam_eq_ofCoordinates
  rw [← P.incomingNativeUnitCoordinates_components k o θ p hs u,
    gluingCollarOrthonormalCoord_components P.radius_pos]

theorem outgoingNativeUnitTangent_eq_seamParam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (o : ℍ) (θ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (hs : p.1.1 ≤ 0) (u : Circle) :
    P.outgoingNativeUnitTangent k o θ p hs u =
      P.nativeSeamUnitTangentParam k θ (P.seamAngularPoint k θ p)
        (Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p)
        (gluingFermiOutgoingNativePhase (gluingRadius C g) (p.1.1, -p.2.1) u) := by
  apply Eq.symm
  apply P.nativeSeamUnitTangentParam_eq_ofCoordinates
  rw [← P.outgoingNativeUnitCoordinates_components k o θ p hs u,
    gluingCollarOrthonormalCoord_components P.radius_pos]

/-- The genuine incoming collar map is exactly transport by the actual
full native Fermi differential, in every valid local angular chart. -/
theorem incomingTangentCollarNativeUnit_local_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ : ℝ) (p : GluingSeamAngularDomain C g θ) (hs : 0 ≤ p.1.1) (u : Circle) :
    P.incomingTangentCollarNativeUnit k
      (P.incomingTangentCollarPolarHomeomorph _
        ((Circle.exp (-p.2.1), ⟨gluingRadius C g + p.1.1, by
          constructor
          · linarith
          · change gluingRadius C g + p.1.1 < gluingRadius C g + gluingDepth C g
            linarith [p.1.2.2]⟩), u)) =
      P.incomingNativeUnitTangentTotal k (P.centers (gluingChainEdgeRight k)).1 θ p hs u := by
  let c : GluingSeamCylinder C g × Circle :=
    ((Circle.exp p.2.1, p.1),
      gluingFermiIncomingNativePhase (gluingRadius C g) (p.1.1, -p.2.1) u)
  have hc : P.incomingTangentCollarNativeCylinderCoordinates
      ((Circle.exp (-p.2.1), ⟨gluingRadius C g + p.1.1, by
        constructor
        · linarith
        · change gluingRadius C g + p.1.1 < gluingRadius C g + gluingDepth C g
          linarith [p.1.2.2]⟩), u) = c := by
    apply Prod.ext
    · apply Prod.ext
      · change (Circle.exp (-p.2.1))⁻¹ = Circle.exp p.2.1
        rw [← Circle.exp_neg, neg_neg]
      · apply Subtype.ext
        change gluingRadius C g + p.1.1 - gluingRadius C g = p.1.1
        ring
    · change (u / gluingPolarRadialCircle (gluingRadius C g + p.1.1)
        (Circle.exp (-p.2.1)))⁻¹ = _
      rw [gluingPolarRadialCircle_exp]
      rfl
  unfold incomingTangentCollarNativeUnit
  rw [Homeomorph.symm_apply_apply, hc]
  apply Subtype.ext
  have h := P.nativeSeamCylinderUnitTangentHomeomorph_local_apply k θ c
    (Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p)
  change (P.nativeSeamCylinderUnitTangentHomeomorph k c).1.1 =
    Bundle.TotalSpace.mk (P.seamAngularPoint k θ p)
      (P.nativeSeamUnitTangentParam k θ (P.seamAngularPoint k θ p)
        (Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p) c.2).1 at h
  rw [h]
  exact congrArg (fun w : P.NativeUnitTangentFiber (P.seamAngularPoint k θ p) =>
    Bundle.TotalSpace.mk (P.seamAngularPoint k θ p) w.1)
      (P.incomingNativeUnitTangent_eq_seamParam k (P.centers (gluingChainEdgeRight k)).1
        θ p hs u).symm

theorem outgoingTangentCollarNativeUnit_local_apply
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (θ : ℝ) (p : GluingSeamAngularDomain C g θ) (hs : p.1.1 ≤ 0) (u : Circle) :
    P.outgoingTangentCollarNativeUnit k
      (P.outgoingTangentCollarPolarHomeomorph _
        ((Circle.exp p.2.1, ⟨gluingRadius C g - p.1.1, by
          constructor
          · linarith
          · change gluingRadius C g - p.1.1 < gluingRadius C g + gluingDepth C g
            linarith [p.1.2.1]⟩), u)) =
      P.outgoingNativeUnitTangentTotal k (P.centers (gluingChainEdgeLeft k)).2 θ p hs u := by
  let c : GluingSeamCylinder C g × Circle :=
    ((Circle.exp p.2.1, p.1),
      gluingFermiOutgoingNativePhase (gluingRadius C g) (p.1.1, -p.2.1) u)
  have hc : P.outgoingTangentCollarNativeCylinderCoordinates
      ((Circle.exp p.2.1, ⟨gluingRadius C g - p.1.1, by
        constructor
        · linarith
        · change gluingRadius C g - p.1.1 < gluingRadius C g + gluingDepth C g
          linarith [p.1.2.1]⟩), u) = c := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change gluingRadius C g - (gluingRadius C g - p.1.1) = p.1.1
        ring
    · have h := gluingOutgoingPhysicalCircle_exp (gluingRadius C g) p.1.1 p.2.1 1
      simp only [gluingOutgoingPhysicalCircle, inv_one, mul_one] at h
      change (u / -gluingPolarRadialCircle (gluingRadius C g - p.1.1)
        (Circle.exp p.2.1))⁻¹ = _
      rw [h]
      rfl
  unfold outgoingTangentCollarNativeUnit
  rw [Homeomorph.symm_apply_apply, hc]
  apply Subtype.ext
  have h := P.nativeSeamCylinderUnitTangentHomeomorph_local_apply k θ c
    (Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p)
  change (P.nativeSeamCylinderUnitTangentHomeomorph k c).1.1 =
    Bundle.TotalSpace.mk (P.seamAngularPoint k θ p)
      (P.nativeSeamUnitTangentParam k θ (P.seamAngularPoint k θ p)
        (Internal.GluingNativeTangentDescentHelpers.seamPoint_mem_chart P k θ p) c.2).1 at h
  rw [h]
  exact congrArg (fun w : P.NativeUnitTangentFiber (P.seamAngularPoint k θ p) =>
    Bundle.TotalSpace.mk (P.seamAngularPoint k θ p) w.1)
      (P.outgoingNativeUnitTangent_eq_seamParam k (P.centers (gluingChainEdgeLeft k)).2
        θ p hs u).symm

end ExerciseGluingPreparation

#print axioms gluingDeckComplex_fderiv_unit_vector
#print axioms gluingPolarRadialCircle_exp
#print axioms continuous_gluingPolarRadialCircle
#print axioms gluingPhysicalCircle_boundary_clutching
#print axioms gluingIncomingPhysicalCircle_nativePhase
#print axioms gluingOutgoingPhysicalCircle_nativePhase
#print axioms ExerciseGluingPreparation.incomingNativeUnitCoordinates_components
#print axioms ExerciseGluingPreparation.outgoingNativeUnitCoordinates_components
#print axioms ExerciseGluingPreparation.incomingNativeUnitTangent_eq_seamParam
#print axioms ExerciseGluingPreparation.outgoingNativeUnitTangent_eq_seamParam
#print axioms ExerciseGluingPreparation.nativeInteriorUnitTangentParam_coordinates
#print axioms ExerciseGluingPreparation.nativeInteriorUnitTangentParam_overlap
#print axioms ExerciseGluingPreparation.incomingNativeUnitCoordinates_fderiv
#print axioms ExerciseGluingPreparation.outgoingNativeUnitCoordinates_fderiv
#print axioms ExerciseGluingPreparation.nativeSeamInteriorUnitTangentParam_overlap
#print axioms ExerciseGluingPreparation.incomingTangentCollarHomeomorph
#print axioms ExerciseGluingPreparation.outgoingTangentCollarHomeomorph
#print axioms ExerciseGluingPreparation.continuous_incomingTangentCollarNativeUnit
#print axioms ExerciseGluingPreparation.continuous_outgoingTangentCollarNativeUnit
#print axioms ExerciseGluingPreparation.incomingTangentCollarNativeUnit_proj
#print axioms ExerciseGluingPreparation.outgoingTangentCollarNativeUnit_proj
#print axioms ExerciseGluingPreparation.incomingTangentCollarNativeUnit_injective
#print axioms ExerciseGluingPreparation.outgoingTangentCollarNativeUnit_injective
#print axioms ExerciseGluingPreparation.tangentCollarNativeUnit_boundary_clutching
#print axioms ExerciseGluingPreparation.incomingTangentCollarNativeUnit_surjective_fiber
#print axioms ExerciseGluingPreparation.outgoingTangentCollarNativeUnit_surjective_fiber
#print axioms ExerciseGluingPreparation.incomingTangentCollarNativeUnit_local_apply
#print axioms ExerciseGluingPreparation.outgoingTangentCollarNativeUnit_local_apply

end
end SystolicGrowth
