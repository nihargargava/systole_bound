module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainDistance

@[expose] public section

/-!
# A separated extended-metric target for the native fin-chain distance

The wrapper carries the already defined finite-walk distance, with its
curvature scale. The original fin quotient and its topology are unchanged.
Separation removes only zero-distance ambiguity; infinite distances remain
permitted. Native hyperbolic slabs map contractively into this target and
agree on their actual adjacent fins.
-/

open Set

namespace SystolicGrowth

/-- A fresh type carrying the native fin quotient's finite-walk distance.
This does not put a second topology or metric on the original quotient. -/
structure GluingCollarFiniteFinPathTarget (r R lam ε : ℝ) where
  val : gluingCollarFiniteFinTarget r ε

noncomputable instance gluingCollarFiniteFinPathTarget_pseudoEMetricSpace
    (r R lam ε : ℝ) : PseudoEMetricSpace (GluingCollarFiniteFinPathTarget r R lam ε) where
  edist p q := ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε p.val q.val
  edist_self p := by simp only [gluingCollarFiniteFinChainEDist_self, mul_zero]
  edist_comm p q := by rw [gluingCollarFiniteFinChainEDist_comm]
  edist_triangle p q s := by
    calc
      _ ≤ ENNReal.ofReal lam *
          (gluingCollarFiniteFinChainEDist r R lam ε p.val q.val +
            gluingCollarFiniteFinChainEDist r R lam ε q.val s.val) :=
        mul_le_mul_of_nonneg_left (gluingCollarFiniteFinChainEDist_triangle
          r R lam ε p.val q.val s.val) (by positivity)
      _ = _ := mul_add _ _ _

@[simp] theorem gluingCollarFiniteFinPathTarget_edist
    (r R lam ε : ℝ) (p q : GluingCollarFiniteFinPathTarget r R lam ε) :
    edist p q = ENNReal.ofReal lam *
      gluingCollarFiniteFinChainEDist r R lam ε p.val q.val := rfl

/-- The separated extended-metric space, not asserted to be a finite metric
space on the entire unrestricted raw quotient. -/
abbrev gluingCollarFiniteFinPathEMetric (r R lam ε : ℝ) :=
  SeparationQuotient (GluingCollarFiniteFinPathTarget r R lam ε)

noncomputable def gluingCollarFiniteFinPathMk (r R lam ε : ℝ)
    (p : gluingCollarFiniteFinTarget r ε) : gluingCollarFiniteFinPathEMetric r R lam ε :=
  SeparationQuotient.mk (⟨p⟩ : GluingCollarFiniteFinPathTarget r R lam ε)

/-- Separation retains exactly the specified scaled native extended distance. -/
@[simp] theorem gluingCollarFiniteFinPathMk_edist
    (r R lam ε : ℝ) (p q : gluingCollarFiniteFinTarget r ε) :
    edist (gluingCollarFiniteFinPathMk r R lam ε p)
      (gluingCollarFiniteFinPathMk r R lam ε q) =
        ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε p q := rfl

/-- Actual inverse Fermi coordinates as one complex coordinate pair. -/
noncomputable def gluingCollarFiniteFinPathCoordinates (lam : ℝ) (z : UpperHalfPlane) : ℂ :=
  (gluingFinFermiRadialCoord lam z : ℂ) +
    (gluingFinFermiTransverseCoord lam z : ℂ) * Complex.I

@[simp] theorem gluingCollarFiniteFinPathCoordinates_re (lam : ℝ) (z : UpperHalfPlane) :
    (gluingCollarFiniteFinPathCoordinates lam z).re = gluingFinFermiRadialCoord lam z := by
  simp [gluingCollarFiniteFinPathCoordinates]

@[simp] theorem gluingCollarFiniteFinPathCoordinates_im (lam : ℝ) (z : UpperHalfPlane) :
    (gluingCollarFiniteFinPathCoordinates lam z).im = gluingFinFermiTransverseCoord lam z := by
  simp [gluingCollarFiniteFinPathCoordinates]

theorem gluingCollarFiniteFinPathCoordinates_reconstruct
    {lam : ℝ} (hlam : 0 < lam) (z : UpperHalfPlane) :
    gluingFinFermiPoint lam (gluingCollarFiniteFinPathCoordinates lam z).re
      (gluingCollarFiniteFinPathCoordinates lam z).im = z := by
  rw [gluingCollarFiniteFinPathCoordinates_re, gluingCollarFiniteFinPathCoordinates_im]
  exact gluingFinFermiPoint_inverse_right hlam z

/-- Integer-labelled native slabs, using the exact inverse Fermi coordinates. -/
noncomputable def gluingCollarFiniteFinPathSlabMap (r R lam ε : ℝ) (n : ℤ) :
    gluingFinFermiRadialWindow lam R → gluingCollarFiniteFinPathEMetric r R lam ε := fun z =>
  gluingCollarFiniteFinPathMk r R lam ε
    (Quotient.mk _ (n, gluingCollarFiniteFinPathCoordinates lam z.1))

/-- Every native slab step supplies a genuine finite-chain competitor with
exactly its hyperbolic extended distance after curvature scaling. -/
theorem gluingCollarFiniteFinPathSlabMap_edist_le
    {r R lam ε : ℝ} (hlam : 0 < lam) (n : ℤ)
    (z w : gluingFinFermiRadialWindow lam R) :
    edist (gluingCollarFiniteFinPathSlabMap r R lam ε n z)
      (gluingCollarFiniteFinPathSlabMap r R lam ε n w) ≤ edist z w := by
  let Z := gluingCollarFiniteFinPathCoordinates lam z.1
  let W := gluingCollarFiniteFinPathCoordinates lam w.1
  have hz : Z.re ∈ Icc (-R) R := by
    simpa only [Z, gluingCollarFiniteFinPathCoordinates_re,
      gluingFinFermiRadialWindow, Set.mem_setOf_eq] using z.2
  have hw : W.re ∈ Icc (-R) R := by
    simpa only [W, gluingCollarFiniteFinPathCoordinates_re,
      gluingFinFermiRadialWindow, Set.mem_setOf_eq] using w.2
  change ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε
    (Quotient.mk _ (n, Z)) (Quotient.mk _ (n, W)) ≤ edist z w
  calc
    _ ≤ ENNReal.ofReal lam * gluingCollarFiniteFermiEDist R lam Z W :=
      mul_le_mul_of_nonneg_left
        (gluingCollarFiniteFinChainEDist_le_fermi n hz hw) (by positivity)
    _ = ENNReal.ofReal (dist z.1 w.1) := by
      rw [gluingCollarFiniteFermiEDist_scaled_eq hlam hz hw]
      rw [gluingCollarFiniteFinPathCoordinates_reconstruct hlam,
        gluingCollarFiniteFinPathCoordinates_reconstruct hlam]
    _ = edist z w := by rw [edist_dist]; rfl

theorem gluingCollarFiniteFinPathSlabMap_lipschitz
    {r R lam ε : ℝ} (hlam : 0 < lam) (n : ℤ) :
    LipschitzWith 1 (gluingCollarFiniteFinPathSlabMap r R lam ε n) := by
  intro z w
  simpa only [ENNReal.coe_one, one_mul] using
    gluingCollarFiniteFinPathSlabMap_edist_le (r := r) (ε := ε) hlam n z w

/-- Adjacent slab maps agree on the original whole-fin identification,
already in the raw quotient before separation. -/
theorem gluingCollarFiniteFinPathSlabMap_seam
    (r R lam ε : ℝ) (n : ℤ) (q : gluingCollarFiniteUpperFin r R lam ε) :
    gluingCollarFiniteFinPathSlabMap r R lam ε n
        (gluingCollarFiniteMetricGlueLeft r R lam ε q) =
      gluingCollarFiniteFinPathSlabMap r R lam ε (n + 1)
        (gluingCollarFiniteMetricGlueRight r R lam ε q) := by
  apply congrArg (gluingCollarFiniteFinPathMk r R lam ε)
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [gluingCollarFiniteMetricGlueLeft, gluingCollarFiniteMetricGlueRight,
      gluingCollarFiniteFinPathCoordinates_re, gluingFinFermiRadialCoord_mirror]
  · simp only [gluingCollarFiniteMetricGlueLeft, gluingCollarFiniteMetricGlueRight,
      gluingCollarFiniteFinPathCoordinates_im, gluingFinFermiTransverseCoord_mirror, neg_neg]
  · simpa only [gluingCollarFiniteMetricGlueLeft, gluingCollarFiniteFinPathCoordinates_re,
      gluingCollarFiniteFinPathCoordinates_im] using q.2.2

/-- Evaluating an actual labelled Fermi slab point returns its original raw
integer-coordinate class inside the separated extended-metric target. -/
theorem gluingCollarFiniteFinPathSlabMap_fermi
    {r R lam ε : ℝ} (hlam : 0 < lam) (n : ℤ) (z : ℂ)
    (hz : z.re ∈ Icc (-R) R) :
    gluingCollarFiniteFinPathSlabMap r R lam ε n
      ⟨gluingFinFermiPoint lam z.re z.im, by
        change gluingFinFermiRadialCoord lam _ ∈ Icc (-R) R
        simpa only [gluingFinFermiRadialCoord_point hlam] using hz⟩ =
      gluingCollarFiniteFinPathMk r R lam ε (Quotient.mk _ (n, z)) := by
  have hcoord : gluingCollarFiniteFinPathCoordinates lam
      (gluingFinFermiPoint lam z.re z.im) = z := by
    apply Complex.ext
    · rw [gluingCollarFiniteFinPathCoordinates_re, gluingFinFermiRadialCoord_point hlam]
    · rw [gluingCollarFiniteFinPathCoordinates_im, gluingFinFermiTransverseCoord_point hlam]
  simp only [gluingCollarFiniteFinPathSlabMap, hcoord]

#print axioms gluingCollarFiniteFinPathSlabMap_lipschitz
#print axioms gluingCollarFiniteFinPathSlabMap_seam
#print axioms gluingCollarFiniteFinPathSlabMap_fermi

end SystolicGrowth
