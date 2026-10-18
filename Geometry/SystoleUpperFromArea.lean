module

public import Geometry.HyperbolicPacking
public import Geometry.QuotientAreaMeasure
public import Geometry.FiniteTriangleFundamentalDomain

@[expose] public section

/-!
# Logarithmic systole bound from quotient area

The final liminf argument needs a uniform `O(log g)` upper bound, not the
sharp constant in a disk-packing estimate. This module reduces that input to
the genus-dependent quotient-area bound. The latter is the remaining
Gauss--Bonnet/triangulation obligation.
-/

open MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth

namespace ClosedHyperbolicSurface

/-- The area bound `covolume ≤ 4πg` already gives a uniform logarithmic
systole estimate with a deliberately loose absolute constant. -/
theorem systole_le_eighteen_log_of_covolume_le_genus
    {g : ℕ} (hg : 2 ≤ g) (X : ClosedHyperbolicSurface g)
    (harea : (covolume X.deckGroup ℍ volume).toReal ≤
      4 * Real.pi * (g : ℝ)) :
    X.systole ≤ 18 * Real.log (g : ℝ) := by
  have hg_real : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg_pos : (0 : ℝ) < g := by linarith
  have harea' : volume.real
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup (I : ℍ)) ≤
        4 * Real.pi * (g : ℝ) := by
    simpa [X.covolume_eq_dirichletDomain_volume (I : ℍ), Measure.real]
      using harea
  have hpack := systole_le_max_log_of_dirichlet_volume_le X (I : ℍ) harea'
  have hlog_g_pos : 0 < Real.log (g : ℝ) :=
    Real.log_pos (by linarith)
  have hlog_two_le : Real.log 2 ≤ Real.log (g : ℝ) :=
    Real.log_le_log (by norm_num) hg_real
  have hconst : 64 * Real.pi ≤ (2 : ℝ) ^ 8 := by
    nlinarith [Real.pi_le_four]
  have hpow : (2 : ℝ) ^ 8 ≤ (g : ℝ) ^ 8 := by
    gcongr
  have harg : 16 * (4 * Real.pi * (g : ℝ)) ≤ (g : ℝ) ^ 9 := by
    calc
      16 * (4 * Real.pi * (g : ℝ)) =
          (64 * Real.pi) * (g : ℝ) := by ring
      _ ≤ ((2 : ℝ) ^ 8) * (g : ℝ) :=
        mul_le_mul_of_nonneg_right hconst hg_pos.le
      _ ≤ ((g : ℝ) ^ 8) * (g : ℝ) :=
        mul_le_mul_of_nonneg_right hpow hg_pos.le
      _ = (g : ℝ) ^ 9 := by ring
  have hlog_arg : Real.log (16 * (4 * Real.pi * (g : ℝ))) ≤
      9 * Real.log (g : ℝ) := by
    calc
      Real.log (16 * (4 * Real.pi * (g : ℝ))) ≤
          Real.log ((g : ℝ) ^ 9) :=
        Real.log_le_log (by positivity) harg
      _ = 9 * Real.log (g : ℝ) := by rw [Real.log_pow]; norm_num
  exact hpack.trans (max_le (by nlinarith) (by nlinarith))

/-- A genus-area bound supplies exactly the second field of `GeometricInput`
after weakening that field to the logarithmic bound actually used. -/
theorem exists_log_systole_upper_bound_of_covolume_le_genus
    (harea : ∀ {g : ℕ}, 2 ≤ g → (X : ClosedHyperbolicSurface g) →
      (covolume X.deckGroup ℍ volume).toReal ≤ 4 * Real.pi * (g : ℝ)) :
    ∃ K : ℝ, ∀ {g : ℕ}, 2 ≤ g → (X : ClosedHyperbolicSurface g) →
      X.systole ≤ K * Real.log (g : ℝ) := by
  refine ⟨18, ?_⟩
  intro g hg X
  exact systole_le_eighteen_log_of_covolume_le_genus hg X (harea hg X)

/-- A fundamental domain covered by at most `4g` geodesic triangles gives
the logarithmic systole bound needed by the final reduction.  This offers a
polygonal alternative to a separate Gauss--Bonnet formalization. -/
theorem systole_le_eighteen_log_of_triangle_certificate
    {g : ℕ} (hg : 2 ≤ g) (X : ClosedHyperbolicSurface g)
    (T : FiniteTriangleFundamentalDomain X)
    (hcount : T.triangleCount ≤ 4 * g) :
    X.systole ≤ 18 * Real.log (g : ℝ) := by
  have hcountReal : (T.triangleCount : ℝ) ≤ 4 * (g : ℝ) := by
    exact_mod_cast hcount
  have harea : (covolume X.deckGroup ℍ volume).toReal ≤
      4 * Real.pi * (g : ℝ) := by
    rw [X.covolume_eq_dirichletDomain_volume (I : ℍ)]
    have htriangle := T.volume_real_dirichletDomain_le_fin_mul_pi (I : ℍ)
    dsimp [Measure.real] at htriangle
    nlinarith [Real.pi_pos]
  exact X.systole_le_eighteen_log_of_covolume_le_genus hg harea

/-- An Euler-characteristic calculation of the total angular defect in a
finite fundamental-domain triangulation gives the required systole bound.
The deficit estimate is the remaining polygonal Gauss--Bonnet obligation. -/
theorem systole_le_eighteen_log_of_angleDeficit_sum
    {g : ℕ} (hg : 2 ≤ g) (X : ClosedHyperbolicSurface g)
    (T : FiniteTriangleFundamentalDomain X)
    (hdeficit : (∑ i : Fin T.triangleCount, T.angleDeficit i) ≤
      4 * Real.pi * (g : ℝ)) :
    X.systole ≤ 18 * Real.log (g : ℝ) := by
  apply X.systole_le_eighteen_log_of_covolume_le_genus hg
  exact (T.covolume_toReal_le_sum_angleDeficit).trans hdeficit

/-- An explicit genus-linear triangulation certificate for every surface
supplies the geometric input's uniform systole upper-bound field. -/
theorem exists_log_systole_upper_bound_of_triangle_certificates
    (htriangles : ∀ {g : ℕ}, 2 ≤ g → (X : ClosedHyperbolicSurface g) →
      ∃ T : FiniteTriangleFundamentalDomain X, T.triangleCount ≤ 4 * g) :
    ∃ K : ℝ, ∀ {g : ℕ}, 2 ≤ g → (X : ClosedHyperbolicSurface g) →
      X.systole ≤ K * Real.log (g : ℝ) := by
  refine ⟨18, ?_⟩
  intro g hg X
  obtain ⟨T, hcount⟩ := htriangles hg X
  exact X.systole_le_eighteen_log_of_triangle_certificate hg T hcount

end ClosedHyperbolicSurface

end SystolicGrowth
