module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteMetricBlockDistanceBridge

@[expose] public section

/-!
# Exact native whole-chain distances in the finite-block limit

The two constructed nonexpanding maps give opposite inequalities. The
identity is restricted to representatives in the original radial window;
outside-window raw classes can have infinite distance and are not asserted
to form the blocks' metric space. The curvature scale is retained exactly.
-/

open Set

namespace SystolicGrowth

/-- The opposite lift recovers the original separated path class at every
actual radial-window Fermi representative. -/
theorem gluingCollarFiniteMetricBlockLimitPathMap_chainMap_mk
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i : ℤ) (z : ℂ)
    (hz : z.re ∈ Icc (-R) R) :
    gluingCollarFiniteMetricBlockLimitPathMap (r := r) (ε := ε) hR hlam
      (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (i, z))) =
        gluingCollarFiniteFinPathMk r R lam ε (Quotient.mk _ (i, z)) := by
  rw [gluingCollarFiniteMetricBlockChainMap_mk hR hlam i z hz,
    gluingCollarFiniteMetricBlockLimitPathMap_copy]
  exact gluingCollarFiniteFinPathSlabMap_fermi hlam i z hz

/-- The original scaled whole-chain extended distance is exactly the metric
limit's distance, for any two actual radial-window representatives. -/
theorem gluingCollarFiniteMetricBlockChainMap_edist_eq
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam) (i j : ℤ) (z w : ℂ)
    (hz : z.re ∈ Icc (-R) R) (hw : w.re ∈ Icc (-R) R) :
    edist (gluingCollarFiniteMetricBlockChainMap (r := r) (ε := ε) hR hlam
        (Quotient.mk _ (i, z)))
      (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (j, w))) =
        ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε
          (Quotient.mk _ (i, z)) (Quotient.mk _ (j, w)) := by
  apply le_antisymm
  · exact gluingCollarFiniteMetricBlockChainMap_edist_le hR hlam _ _
  · calc
      _ = edist (gluingCollarFiniteFinPathMk r R lam ε (Quotient.mk _ (i, z)))
          (gluingCollarFiniteFinPathMk r R lam ε (Quotient.mk _ (j, w))) :=
        (gluingCollarFiniteFinPathMk_edist r R lam ε _ _).symm
      _ = edist
          (gluingCollarFiniteMetricBlockLimitPathMap hR hlam
            (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (i, z))))
          (gluingCollarFiniteMetricBlockLimitPathMap hR hlam
            (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (j, w)))) := by
        rw [gluingCollarFiniteMetricBlockLimitPathMap_chainMap_mk hR hlam i z hz,
          gluingCollarFiniteMetricBlockLimitPathMap_chainMap_mk hR hlam j w hw]
      _ ≤ _ := by
        simpa only [ENNReal.coe_one, one_mul] using
          gluingCollarFiniteMetricBlockLimitPathMap_lipschitz hR hlam
            (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (i, z)))
            (gluingCollarFiniteMetricBlockChainMap hR hlam (Quotient.mk _ (j, w)))

/-- The exact bridge is independent of how admissible raw representatives
are supplied; it is not an assertion about outside-window quotient points. -/
theorem gluingCollarFiniteMetricBlockChainMap_edist_eq_of_window
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (p q : gluingCollarFiniteFinTarget r ε)
    (hp : ∃ i : ℤ, ∃ z : ℂ, z.re ∈ Icc (-R) R ∧ Quotient.mk _ (i, z) = p)
    (hq : ∃ j : ℤ, ∃ w : ℂ, w.re ∈ Icc (-R) R ∧ Quotient.mk _ (j, w) = q) :
    edist (gluingCollarFiniteMetricBlockChainMap hR hlam p)
      (gluingCollarFiniteMetricBlockChainMap hR hlam q) =
        ENNReal.ofReal lam * gluingCollarFiniteFinChainEDist r R lam ε p q := by
  obtain ⟨i, z, hz, rfl⟩ := hp
  obtain ⟨j, w, hw, rfl⟩ := hq
  exact gluingCollarFiniteMetricBlockChainMap_edist_eq hR hlam i j z w hz hw

/-- The real-distance form needed by the proper native retraction limit. -/
theorem gluingCollarFiniteMetricBlockChainMap_dist_eq_of_window
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (p q : gluingCollarFiniteFinTarget r ε)
    (hp : ∃ i : ℤ, ∃ z : ℂ, z.re ∈ Icc (-R) R ∧ Quotient.mk _ (i, z) = p)
    (hq : ∃ j : ℤ, ∃ w : ℂ, w.re ∈ Icc (-R) R ∧ Quotient.mk _ (j, w) = q) :
    dist (gluingCollarFiniteMetricBlockChainMap hR hlam p)
      (gluingCollarFiniteMetricBlockChainMap hR hlam q) =
        lam * (gluingCollarFiniteFinChainEDist r R lam ε p q).toReal := by
  have h := congrArg ENNReal.toReal
    (gluingCollarFiniteMetricBlockChainMap_edist_eq_of_window hR hlam p q hp hq)
  simpa only [edist_dist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal hlam.le] using h

#print axioms gluingCollarFiniteMetricBlockChainMap_edist_eq
#print axioms gluingCollarFiniteMetricBlockChainMap_dist_eq_of_window

end SystolicGrowth
