module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.MetricSpace.Isometry

@[expose] public section

/-!
# The systole of a metric space through continuous essential loops

The extended systole is the infimum of metric variations of all based loops
that are not homotopic to a constant loop. No rectifiability or smoothness is
assumed. The empty infimum is infinity, so simply connected spaces need no
special convention.
-/

open Set
open scoped ENNReal NNReal unitInterval

noncomputable section

namespace SystolicGrowth

/-- **Math.** The length infimum over all essential continuous based loops,
with their basepoints allowed to vary. -/
def metricHomotopySystole (M : Type*) [PseudoMetricSpace M] : ℝ≥0∞ :=
  ⨅ y : M, ⨅ ℓ : Path y y, ⨅ (_ : ¬ ℓ.Homotopic (Path.refl y)),
    eVariationOn ℓ univ

/-- **Math.** A common lower bound on essential-loop lengths is precisely
a lower bound on their infimum. -/
theorem le_metricHomotopySystole_iff {M : Type*} [PseudoMetricSpace M] {L : ℝ≥0∞} :
    L ≤ metricHomotopySystole M ↔
      ∀ (y : M) (ℓ : Path y y), ¬ ℓ.Homotopic (Path.refl y) →
        L ≤ eVariationOn ℓ univ := by
  simp only [metricHomotopySystole, le_iInf_iff]

/-- **Math.** Every genuine essential continuous loop is an admissible
competitor for the systole. -/
theorem metricHomotopySystole_le_eVariationOn {M : Type*} [PseudoMetricSpace M]
    {y : M} (ℓ : Path y y) (hess : ¬ ℓ.Homotopic (Path.refl y)) :
    metricHomotopySystole M ≤ eVariationOn ℓ univ := by
  exact iInf_le_of_le y (iInf_le_of_le ℓ (iInf_le_of_le hess le_rfl))

/-- **Math.** A homeomorphism preserves whether a based loop is essential.
The reverse implication maps the actual nullhomotopy back through its inverse. -/
theorem path_map_homeomorph_nullhomotopic_iff
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) {y : M} (ℓ : Path y y) :
    (ℓ.map e.continuous).Homotopic (Path.refl (e y)) ↔
      ℓ.Homotopic (Path.refl y) := by
  have hrefl : (Path.refl y).map e.continuous = Path.refl (e y) := by
    apply Path.ext
    rfl
  constructor
  · intro h
    have hback := (h.map (⟨e.symm, e.symm.continuous⟩ : C(N, M))).pathCast
      (e.symm_apply_apply y).symm (e.symm_apply_apply y).symm
    have hloop : ((ℓ.map e.continuous).map e.symm.continuous).cast
        (e.symm_apply_apply y).symm (e.symm_apply_apply y).symm = ℓ := by
      apply Path.ext
      funext t
      exact e.symm_apply_apply (ℓ t)
    have hconst : ((Path.refl (e y)).map e.symm.continuous).cast
        (e.symm_apply_apply y).symm (e.symm_apply_apply y).symm = Path.refl y := by
      apply Path.ext
      funext t
      exact e.symm_apply_apply y
    simpa only [hloop, hconst] using hback
  · intro h
    simpa only [hrefl] using h.map (⟨e, e.continuous⟩ : C(M, N))

/-- **Math.** A genuinely Lipschitz homeomorphism bounds the target systole
by its distortion times the source systole, including infinite systoles.
The positive distortion excludes the empty-infimum `0 * ∞` exception. -/
theorem metricHomotopySystole_le_mul_of_lipschitz_homeomorph
    {M N : Type*} [PseudoMetricSpace M] [PseudoMetricSpace N]
    (e : M ≃ₜ N) {K : ℝ≥0} (hK : 0 < K) (he : LipschitzWith K e) :
    metricHomotopySystole N ≤ (K : ℝ≥0∞) * metricHomotopySystole M := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  simp only [metricHomotopySystole,
    ENNReal.mul_iInf_of_ne hK0 ENNReal.coe_ne_top, le_iInf_iff]
  intro y ℓ hess
  have hmapped : ¬ (ℓ.map e.continuous).Homotopic (Path.refl (e y)) := by
    simpa only [path_map_homeomorph_nullhomotopic_iff] using hess
  have hsys := metricHomotopySystole_le_eVariationOn (ℓ.map e.continuous) hmapped
  have hlength := he.lipschitzOnWith.comp_eVariationOn_le
    (g := ℓ) (s := univ) (mapsTo_univ ℓ univ)
  exact hsys.trans hlength

/-- **Math.** The continuous-loop systole is invariant under an actual
isometry equivalence, with homotopies transported rather than assumed. -/
theorem metricHomotopySystole_eq_of_isometryEquiv
    {M N : Type*} [PseudoMetricSpace M] [PseudoMetricSpace N] (e : M ≃ᵢ N) :
    metricHomotopySystole M = metricHomotopySystole N := by
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      metricHomotopySystole_le_mul_of_lipschitz_homeomorph e.symm.toHomeomorph
        (K := 1) zero_lt_one e.symm.isometry_toFun.lipschitz
  · simpa only [ENNReal.coe_one, one_mul] using
      metricHomotopySystole_le_mul_of_lipschitz_homeomorph e.toHomeomorph
        (K := 1) zero_lt_one e.isometry_toFun.lipschitz

#print axioms le_metricHomotopySystole_iff
#print axioms metricHomotopySystole_le_eVariationOn
#print axioms metricHomotopySystole_le_mul_of_lipschitz_homeomorph
#print axioms metricHomotopySystole_eq_of_isometryEquiv

end SystolicGrowth
